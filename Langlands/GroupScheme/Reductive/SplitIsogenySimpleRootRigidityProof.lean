import Langlands.GroupScheme.Reductive.SplitIsogenySimpleRootRigidityStatement
import Langlands.GroupScheme.Absolute.BorelHomomorphismRigidityProof
import Langlands.GroupScheme.Absolute.RegularCocharacterBorelProof
import Langlands.GroupScheme.Reductive.SplitLeviGluingSimpleUnipotent
import Langlands.GroupScheme.Reductive.RootDatumExistence
import Langlands.GroupScheme.Reductive.FieldExtensionProof
import Langlands.GroupScheme.Torus.MaximalBaseChangeProof
import Langlands.GroupScheme.Torus.RootSupportBaseChange
import Langlands.GroupScheme.Rational.RootSubgroupBaseChange
import Langlands.GroupScheme.Rational.SmoothAffineGenericCentralizer
import Langlands.GroupScheme.Dynamic.AffineRepresentability
import Langlands.GroupScheme.Dynamic.Uniqueness
import Langlands.GroupScheme.SchematicHomEquality
import Langlands.GroupScheme.LocallyNoetherianHomEquality
import Langlands.GroupScheme.BaseChangeReflection
import Langlands.GroupScheme.RepresentabilityTransfer
import Langlands.AbelianScheme.KernelBaseChange
import Mathlib.AlgebraicGeometry.Morphisms.Separated

/-! # Isogenies of split reductive groups are determined by `T` and the simple root groups:
proof (Milne 21.63) -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace SplitIsogenySimpleRootRigidity

section Equalizer

variable {B : Scheme.{u}} {G H : GroupScheme B}

/-- The points on which two homomorphisms `f g : G ⟶ H` agree, on every test scheme. -/
def homEqualizerSubgroup (f g : G ⟶ H) : SubgroupFunctor G where
  carrier T :=
    { carrier := {x | x ≫ f.hom.hom = x ≫ g.hom.hom}
      one_mem' := by
        change (1 : T ⟶ G.X) ≫ f.hom.hom = (1 : T ⟶ G.X) ≫ g.hom.hom
        rw [MonObj.one_comp, MonObj.one_comp]
      mul_mem' := fun {x y} hx hy => by
        change x ≫ f.hom.hom = x ≫ g.hom.hom at hx
        change y ≫ f.hom.hom = y ≫ g.hom.hom at hy
        change (x * y) ≫ f.hom.hom = (x * y) ≫ g.hom.hom
        rw [MonObj.mul_comp, MonObj.mul_comp, hx, hy]
      inv_mem' := fun {x} hx => by
        change x ≫ f.hom.hom = x ≫ g.hom.hom at hx
        change x⁻¹ ≫ f.hom.hom = x⁻¹ ≫ g.hom.hom
        rw [GrpObj.inv_comp, GrpObj.inv_comp, hx] }
  comp_mem {T T'} a {x} hx := by
    change x ≫ f.hom.hom = x ≫ g.hom.hom at hx
    change (a ≫ x) ≫ f.hom.hom = (a ≫ x) ≫ g.hom.hom
    rw [Category.assoc, Category.assoc, hx]

@[simp]
theorem mem_homEqualizerSubgroup (f g : G ⟶ H) {T : Over B} (x : T ⟶ G.X) :
    x ∈ (homEqualizerSubgroup f g).carrier T ↔ x ≫ f.hom.hom = x ≫ g.hom.hom :=
  Iff.rfl

/-- The agreement subgroup is the functor of points of the scheme equalizer. -/
theorem mem_homEqualizerSubgroup_iff_factors (f g : G ⟶ H) {T : Over B} (x : T ⟶ G.X) :
    x ∈ (homEqualizerSubgroup f g).carrier T ↔
      ∃ y : T ⟶ equalizer f.hom.hom g.hom.hom,
        y ≫ equalizer.ι f.hom.hom g.hom.hom = x := by
  rw [mem_homEqualizerSubgroup]
  constructor
  · intro hx
    exact ⟨equalizer.lift x hx, equalizer.lift_ι _ _⟩
  · rintro ⟨y, rfl⟩
    simp only [Category.assoc]
    rw [equalizer.condition]

/-- For a separated target, the agreement subgroup has a closed representing subgroup. -/
theorem homEqualizerSubgroup_isClosedRepresentable (f g : G ⟶ H) [IsSeparated H.X.hom] :
    (homEqualizerSubgroup f g).IsClosedRepresentable :=
  (homEqualizerSubgroup f g).isClosedRepresentable_of_scheme
    (equalizer.ι f.hom.hom g.hom.hom) (fun _ x => mem_homEqualizerSubgroup_iff_factors f g x)

/-- A homomorphism lands in the agreement subgroup exactly when the two composites agree. -/
theorem range_le_homEqualizerSubgroup_iff (f g : G ⟶ H) {K : GroupScheme B} (i : K ⟶ G) :
    SubgroupFunctor.range i ≤ homEqualizerSubgroup f g ↔ i ≫ f = i ≫ g := by
  constructor
  · intro hi
    apply hom_ext_points
    intro T x
    have hx := hi T (SubgroupFunctor.mem_range.mpr ⟨x, rfl⟩)
    simpa only [mem_homEqualizerSubgroup, Grp.comp_hom_hom, Category.assoc] using hx
  · intro hi T x hx
    obtain ⟨y, rfl⟩ := SubgroupFunctor.mem_range.mp hx
    change (y ≫ i.hom.hom) ≫ f.hom.hom = (y ≫ i.hom.hom) ≫ g.hom.hom
    simpa only [Grp.comp_hom_hom, Category.assoc] using
      congrArg (fun j : K ⟶ H => y ≫ j.hom.hom) hi

end Equalizer

section AlgClosed

variable {k : Type u} [Field k] [IsAlgClosed k]

/-- The algebraically closed case. Two homomorphisms from a connected reductive group with a
split maximal torus `i` to a connected reductive group are equal if they agree on `T` and on the
root subgroups of the simple roots of a generic cocharacter `ν`. -/
theorem eq_of_isAlgClosed
    {G G' : GroupScheme (Spec (CommRingCat.of k))}
    (hG : IsConnectedReductive G) (hG' : IsConnectedReductive G')
    {T : CommGroupScheme (Spec (CommRingCat.of k))} (i : T.toGrp ⟶ G)
    (hT : IsSplitTorus T.toGrp) (hi : IsMaximalTorus i) (ν : cocharacterLattice T)
    (hν : haveI := hG.isAffineHom; IsGenericCocharacter i ν)
    (φ₁ φ₂ : G ⟶ G') (hTφ : i ≫ φ₁ = i ≫ φ₂)
    (hsimple : haveI := hG.isAffineHom; ∀ α ∈ simpleRelativeRoots i ν,
      RelativeRoot.subgroup i α ≤ homEqualizerSubgroup φ₁ φ₂) :
    φ₁ = φ₂ := by
  have := hG.isAffineHom
  have := hG.smooth
  have := hG.connectedSpace
  have := hG'.isAffineHom
  have := hG'.smooth
  have := hG'.connectedSpace
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  obtain ⟨E, q, hqrep, hqc⟩ := homEqualizerSubgroup_isClosedRepresentable φ₁ φ₂
  obtain ⟨J, _, P, hP, -⟩ := rootDatumExistence k G hG T hT i hi
  let χ := CommGroupScheme.groupHom ν ≫ i
  have hU : Dynamic.unipotent χ ≤ homEqualizerSubgroup φ₁ φ₂ := by
    rw [← hqrep.2]
    exact LeviGluing.unipotent_le_range_of_simpleRoots hG hT hi hP hν q hqc
      (fun α hα => hqrep.2 ▸ hsimple α hα)
  have hZ : Dynamic.centralizer χ ≤ homEqualizerSubgroup φ₁ φ₂ := by
    rw [centralizer_comp_eq_range_of_isRegular hG hT i hi ν hν]
    exact (range_le_homEqualizerSubgroup_iff φ₁ φ₂ i).mpr hTφ
  have hPle : Dynamic.parabolic χ ≤ homEqualizerSubgroup φ₁ φ₂ :=
    Dynamic.parabolic_le_of_centralizer_le_of_unipotent_le χ _ hZ hU
  have hBorel : IsBorelSubgroup (Dynamic.Affine.parabolicHom χ) :=
    (regularCocharacterBorel k G hG T i hT hi).1 ν hν _ _
      (Dynamic.Affine.isClosedSubgroup_parabolicHom χ)
      (Dynamic.Affine.isRepresentedBy_parabolicHom χ)
  have hB : Dynamic.Affine.parabolicHom χ ≫ φ₁ = Dynamic.Affine.parabolicHom χ ≫ φ₂ := by
    apply (range_le_homEqualizerSubgroup_iff φ₁ φ₂ _).mp
    rw [(Dynamic.Affine.isRepresentedBy_parabolicHom χ).2]
    exact hPle
  have hb : Spec.map (CommRingCat.ofHom (algebraMap k k)) = 𝟙 _ := by
    rw [Algebra.algebraMap_self, CommRingCat.ofHom_id, Spec.map_id]
  have : IsIso (Spec.map (CommRingCat.ofHom (algebraMap k k))) := by
    rw [hb]
    infer_instance
  apply LocallyNoetherianHomEquality.baseChange_hom_ext_of_isIso
    (Spec.map (CommRingCat.ofHom (algebraMap k k)))
  exact borelHomomorphismRigidity k G G' _ _ hBorel k
    ((GroupScheme.baseChange (Spec.map (CommRingCat.ofHom (algebraMap k k)))).map φ₁)
    ((GroupScheme.baseChange (Spec.map (CommRingCat.ofHom (algebraMap k k)))).map φ₂)
    (by rw [← Functor.map_comp, ← Functor.map_comp, hB])

end AlgClosed

section BaseChange

variable {k K : Type u} [Field k] [Field K] [Algebra k K]

local notation "b" => Spec.map (CommRingCat.ofHom (algebraMap k K))

/-- For a split torus `T`, every simple root of `T_K` in `G_K` for the base-changed cocharacter
is the base change of a simple root of `T` in `G`. -/
theorem exists_simpleRelativeRoot_of_baseChange
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
    [LocallyOfFiniteType G.X.hom] [IsAffineHom ((GroupScheme.baseChange b).obj G).X.hom]
    {T : CommGroupScheme (Spec (CommRingCat.of k))} (hT : IsSplitTorus T.toGrp)
    (i : T.toGrp ⟶ G) (ν : cocharacterLattice T)
    {α' : characterLattice ((CommGroupScheme.baseChange b).obj T)}
    (hα' : α' ∈ simpleRelativeRoots ((GroupScheme.baseChange b).map i)
      (cocharacterLattice.baseChange b T ν)) :
    ∃ α ∈ simpleRelativeRoots i ν, characterLattice.baseChange b T α = α' := by
  have hmem : ∀ χ : characterLattice T,
      characterLattice.baseChange b T χ ∈ relativeRoots
        (T := (CommGroupScheme.baseChange b).obj T) ((GroupScheme.baseChange b).map i) ↔
        χ ∈ relativeRoots i :=
    fun χ => mem_roots_baseChange_iff (K := K) G T hT i χ
  obtain ⟨⟨hα'r, hα'pos⟩, hα'not⟩ := hα'
  obtain ⟨α, rfl⟩ := (hT.characterLattice_baseChange_bijective b T).2 α'
  rw [latticePairing_baseChange] at hα'pos
  refine ⟨α, ⟨⟨(hmem α).mp hα'r, hα'pos⟩, ?_⟩, rfl⟩
  rintro ⟨β, ⟨hβr, hβpos⟩, c, ⟨hcr, hcpos⟩, hαβc⟩
  apply hα'not
  refine ⟨characterLattice.baseChange b T β, ⟨(hmem β).mpr hβr, ?_⟩,
    characterLattice.baseChange b T c, ⟨(hmem c).mpr hcr, ?_⟩, ?_⟩
  · rwa [latticePairing_baseChange]
  · rwa [latticePairing_baseChange]
  · rw [hαβc, map_add]

end BaseChange

end SplitIsogenySimpleRootRigidity

open SplitIsogenySimpleRootRigidity in
/-- Milne, Corollary 21.63: isogenies of split reductive groups that agree on the torus and on
the root subgroups of the simple roots are equal. -/
theorem splitIsogenySimpleRootRigidity : SplitIsogenySimpleRootRigidityStatement.{u} := by
  intro k _ G G' hG hG' T T' i i' hT hi hT' hi' ν hν IsSplitIsogeny φ₁ φ₂ _ _ hTφ hsimple
  have := hG.isAffineHom
  have := hG.smooth
  have := hG'.isAffineHom
  have := hG'.smooth
  let K := AlgebraicClosure k
  set b : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of k) :=
    Spec.map (CommRingCat.ofHom (algebraMap k K))
  have hGK : IsConnectedReductive ((GroupScheme.baseChange b).obj G) :=
    connectedReductiveFieldExtensionStatement k K G hG
  have hG'K : IsConnectedReductive ((GroupScheme.baseChange b).obj G') :=
    connectedReductiveFieldExtensionStatement k K G' hG'
  have := hGK.isAffineHom
  have hTK : IsSplitTorus ((CommGroupScheme.baseChange b).obj T).toGrp := hT.baseChange b
  have hiK : IsMaximalTorus (T := (CommGroupScheme.baseChange b).obj T)
      ((GroupScheme.baseChange b).map i) :=
    (maximalTorusBaseChange k K G T i hi.1 hi.2.1).1 hi
  have hνK : IsGenericCocharacter (T := (CommGroupScheme.baseChange b).obj T)
      ((GroupScheme.baseChange b).map i)
      (cocharacterLattice.baseChange b T ν) := by
    intro α' hα'
    obtain ⟨α, rfl⟩ := (hT.characterLattice_baseChange_bijective b T).2 α'
    rw [latticePairing_baseChange]
    exact hν α ((mem_roots_baseChange_iff (K := K) G T hT i α).mp hα')
  have hφK : (GroupScheme.baseChange b).map i ≫ (GroupScheme.baseChange b).map φ₁ =
      (GroupScheme.baseChange b).map i ≫ (GroupScheme.baseChange b).map φ₂ := by
    rw [← Functor.map_comp, ← Functor.map_comp, hTφ]
  have hsimpleK : ∀ α' ∈ simpleRelativeRoots ((GroupScheme.baseChange b).map i)
      (cocharacterLattice.baseChange b T ν),
      RelativeRoot.subgroup ((GroupScheme.baseChange b).map i) α' ≤
        homEqualizerSubgroup ((GroupScheme.baseChange b).map φ₁)
          ((GroupScheme.baseChange b).map φ₂) := by
    intro α' hα'
    obtain ⟨α, hα, rfl⟩ := exists_simpleRelativeRoot_of_baseChange (K := K) hT i ν hα'
    rw [RelativeRoot.subgroup_baseChange]
    intro T' x hx
    rw [SubgroupFunctor.mem_baseChange] at hx
    have h := hsimple α hα _ _ hx
    rw [mem_homEqualizerSubgroup]
    apply (baseChangePointsEquiv b G' T').injective
    rw [baseChangePointsEquiv_comp, baseChangePointsEquiv_comp]
    exact h
  have hK := eq_of_isAlgClosed hGK hG'K _ hTK hiK _ hνK _ _ hφK hsimpleK
  have : IsSchemeTheoreticallyDominant b :=
    isSchemeTheoreticallyDominant_specMap (algebraMap k K).injective
  have : QuasiCompact b := (fieldExtension_fpqc k K).2.2
  exact SchematicHomEquality.baseChange_hom_ext b hK

end Langlands.GroupScheme
