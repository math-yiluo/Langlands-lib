import Langlands.GroupScheme.Cartan.ConjugacyDensityStatement
import Langlands.GroupScheme.Absolute.BorelPointContainmentProof
import Langlands.GroupScheme.Absolute.MaximalTorusConjugacyProof
import Langlands.GroupScheme.Rational.SplitTorusCentralizerReduction
import Langlands.GroupScheme.Rational.TorusCentralizerConjugacy
import Langlands.GroupScheme.Rational.ParabolicConjugacyTransport
import Langlands.GroupScheme.Torus.CentralizerConnected
import Langlands.GroupScheme.Torus.SplitReflection
import Langlands.GroupScheme.Torus.FiniteGaloisSplittingProof

/-! # Proof: conjugacy and density of Cartan subgroups -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.MonoidalCategory Opposite
open CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.AlgebraicGeometry.TangentSmoothness

open _root_.AlgebraicGeometry _root_.Langlands.AlgebraicGeometry.Picard

variable {K : Type u} [Field K] {X Y : Scheme.{u}}

/-- Let `f : X ⟶ Y` be a morphism over `Spec K` with `X` smooth over `K` and `Y` irreducible and
locally of finite type over `K`. If `f` is surjective on rational tangent vectors at some
`K`-point of `X`, then the range of `f` contains a dense open subset of `Y`: the image of the
smooth locus of `f`. -/
theorem exists_isOpen_dense_subset_range_of_isTangentSurjectiveAt
    {p : X ⟶ Spec (CommRingCat.of K)} {q : Y ⟶ Spec (CommRingCat.of K)} [Smooth p]
    [LocallyOfFiniteType q] [IrreducibleSpace Y] (f : X ⟶ Y) (hf : f ≫ q = p)
    {x : Spec (CommRingCat.of K) ⟶ X} (hx : IsRationalPoint p x)
    (h : IsTangentSurjectiveAt p q f x) :
    ∃ U : Set Y, IsOpen U ∧ Dense U ∧ U ⊆ Set.range f := by
  have := locallyOfFinitePresentation_of_comp_eq f hf
  have hz := mem_smoothLocus_of_isTangentSurjectiveAt f hf hx h
  have : Smooth (f.smoothLocus.ι ≫ f) := by
    rw [← Scheme.Hom.smoothLocus_eq_top_iff, ← Scheme.Hom.preimage_smoothLocus_eq,
      Scheme.Opens.ι_preimage_self]
  have hopen : IsOpen (Set.range (f.smoothLocus.ι ≫ f)) :=
    (f.smoothLocus.ι ≫ f).isOpenMap.isOpen_range
  refine ⟨_, hopen, hopen.dense ⟨_, ⟨⟨_, hz⟩, rfl⟩⟩, ?_⟩
  rintro _ ⟨u, rfl⟩
  exact ⟨f.smoothLocus.ι u, rfl⟩

end Langlands.AlgebraicGeometry.TangentSmoothness

namespace Langlands.GroupScheme

namespace CartanConjugacyDensity

open Langlands.AlgebraicGeometry.Picard Langlands.AlgebraicGeometry.TangentSmoothness
open BorelPointContainment

set_option backward.isDefEq.respectTransparency false

variable {k : Type u} [Field k]

/-- **Open dense image of the conjugation map of a dynamic centralizer.** Let `G` be a smooth
connected affine group over an algebraically closed field, `χ` a cocharacter of `G` and
`iZ : Z ⟶ G` a smooth affine representative of its dynamic centralizer. Then the range of the
conjugation map `G × Z ⟶ G`, `(x, z) ↦ x iZ(z) x⁻¹`, contains a dense open subset of `G`. -/
theorem exists_isOpen_dense_subset_range_conjugation_centralizer [IsAlgClosed k]
    {G Z : GroupScheme (Spec (CommRingCat.of k))} [Smooth G.X.hom] [IsAffineHom G.X.hom]
    [ConnectedSpace G.X.left] [Smooth Z.X.hom] [IsAffineHom Z.X.hom]
    (χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G) (iZ : Z ⟶ G)
    (hZ : (Dynamic.centralizer χ).IsRepresentedBy iZ) :
    ∃ U : Set G.X.left, IsOpen U ∧ Dense U ∧ U ⊆ Set.range (conjugation iZ).left := by
  let P := (algSpec (CommRingCat.of k)).obj (op (CommAlgCat.of (CommRingCat.of k) k))
  have hP : P.hom = 𝟙 _ := by
    simp [P, algSpec_obj_hom, Algebra.algebraMap_self]
    rfl
  let e : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ P :=
    Over.homMk (𝟙 _) (by rw [hP]; rfl)
  have hconst : ∀ y : P ⟶ G.X, G.constantPoint (e ≫ y) P = y := by
    intro y
    unfold constantPoint
    rw [← Category.assoc]
    convert Category.id_comp y
    apply Over.OverMorphism.ext
    simp [e, hP]
  obtain ⟨u, hu⟩ := exists_generic_affinePoint (k := k) (G := G) χ
  have hχZ : SubgroupFunctor.range χ ≤ Dynamic.centralizer χ := by
    rw [← torusCentralizer_gm_eq_dynamicCentralizer]
    exact range_le_torusCentralizer χ
  let χ' := hZ.factorHom χ hχZ
  have hχ' : χ' ≫ iZ = χ := hZ.factorHom_comp χ hχZ
  let z₀ : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ Z.X := (e ≫ u⁻¹) ≫ χ'.hom.hom
  have hz₀ : G.constantPoint (z₀ ≫ iZ.hom.hom) P = (u ≫ χ.hom.hom)⁻¹ := by
    have h : z₀ ≫ iZ.hom.hom = e ≫ (u ≫ χ.hom.hom)⁻¹ := by
      rw [Category.assoc, ← Grp.comp_hom_hom, hχ']
      simp only [GrpObj.comp_inv, GrpObj.inv_comp, Category.assoc]
    rw [h, hconst]
  have : Smooth (G.X ⊗ Z.X).hom := smooth_tensor _ _ inferInstance inferInstance
  have : IrreducibleSpace G.X.left := DynamicConnected.irreducibleSpace_of_smooth G
  refine exists_isOpen_dense_subset_range_of_isTangentSurjectiveAt _ (Over.w _)
    (Over.w (lift 1 z₀ : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X ⊗ Z.X))
    (isTangentSurjectiveAt_conjugation iZ z₀ fun W => ?_)
  obtain ⟨X, ξ, h⟩ := exists_adjoint_sub_add_eq χ iZ hZ u hu (Additive.ofMul W)
  refine ⟨X.toMul, ξ.toMul, ?_⟩
  rw [hz₀, inv_inv]
  have h' := congrArg Additive.toMul h
  rw [toMul_add, toMul_sub, adjoint_toMul, lieKernelTargetLinear_toMul, toMul_ofMul] at h'
  rw [← h', div_eq_mul_inv, mul_right_comm]

/-- The isomorphism of underlying group schemes defined by an isomorphism of commutative group
schemes. -/
def groupIso {T T' : CommGroupScheme (Spec (CommRingCat.of k))} (φ : T ≅ T') :
    T.toGrp ≅ T'.toGrp where
  hom := CommGroupScheme.groupHom φ.hom
  inv := CommGroupScheme.groupHom φ.inv
  hom_inv_id := congrArg Additive.toMul φ.hom_inv_id
  inv_hom_id := congrArg Additive.toMul φ.inv_hom_id

/-- **Conjugacy of Cartan subgroups.** Over an algebraically closed field, any two Cartan
subgroups of a smooth connected affine group are conjugate by a rational point. -/
theorem exists_range_comp_innerIso_eq [IsAlgClosed k]
    {G C C' : GroupScheme (Spec (CommRingCat.of k))} [Smooth G.X.hom] [IsAffineHom G.X.hom]
    [ConnectedSpace G.X.left] {c : C ⟶ G} {c' : C' ⟶ G}
    (hc : IsCartanSubgroup c) (hc' : IsCartanSubgroup c') :
    ∃ g : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X,
      SubgroupFunctor.range (c ≫ (G.innerIso g).hom) = SubgroupFunctor.range c' := by
  obtain ⟨T, j, hj, hrep⟩ := hc.exists_centralizer_representation
  obtain ⟨T', j', hj', hrep'⟩ := hc'.exists_centralizer_representation
  obtain ⟨g, φ, hg⟩ := maximalTorusConjugacy k G T T' j j' hj hj'
  refine ⟨g, ?_⟩
  rw [(hrep.comp_iso (G.innerIso g)).2, hrep'.2,
    torusCentralizer_eq_comap_of_iso j (G.innerIso g), SubgroupFunctor.comap_iso_hom_inv, hg]
  exact torusCentralizer_eq_of_iso _ _ (groupIso φ) rfl

/-- **Density of the conjugates of a Cartan subgroup.** Over an algebraically closed field, the
range of the conjugation map `G × C ⟶ G` of a Cartan subgroup `c : C ⟶ G` of a smooth connected
affine group contains a dense open subset of `G`. -/
theorem exists_isOpen_dense_subset_range_conjugation [IsAlgClosed k]
    {G C : GroupScheme (Spec (CommRingCat.of k))} [Smooth G.X.hom] [IsAffineHom G.X.hom]
    [ConnectedSpace G.X.left] {c : C ⟶ G} (hc : IsCartanSubgroup c) :
    ∃ U : Set G.X.left, IsOpen U ∧ Dense U ∧ U ⊆ Set.range (conjugation c).left := by
  obtain ⟨T, j, hj, hrep⟩ := hc.exists_centralizer_representation
  have hT : IsSplitTorus T.toGrp :=
    hj.1.isSplitTorus_of_finiteGaloisSplitting torusFiniteGaloisSplitting
  obtain ⟨ν, hν⟩ := hT.exists_cocharacter_centralizer_eq j
  have hZ : (Dynamic.centralizer (CommGroupScheme.groupHom ν ≫ j)).IsRepresentedBy c := by
    rw [hν]
    exact hrep
  have : Smooth C.X.hom := hc.smooth_connected.1
  have : IsAffineHom C.X.hom := hc.isClosedSubgroup.isAffineHom
  exact exists_isOpen_dense_subset_range_conjugation_centralizer _ c hZ

end CartanConjugacyDensity

open CartanConjugacyDensity in
/-- **Conjugacy and density of Cartan subgroups** (Milne, Proposition 17.44, the assertions over
an algebraically closed field). -/
theorem cartanConjugacyDensity : CartanConjugacyDensityStatement.{u} := by
  intro k _ _ G _ _ _
  exact ⟨fun C C' c c' hc hc' => exists_range_comp_innerIso_eq hc hc',
    fun C c hc => exists_isOpen_dense_subset_range_conjugation hc⟩

end Langlands.GroupScheme
