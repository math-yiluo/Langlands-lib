import Langlands.GroupScheme.Reductive.SplitSemisimpleRootSpanNecessity
import Langlands.GroupScheme.Reductive.CenterExistenceProof
import Langlands.GroupScheme.Absolute.MaximalTorusCentralizerStatement
import Langlands.GroupScheme.Rational.CentralRootRestriction
import Langlands.GroupScheme.Torus.KernelDiagonalizable
import Langlands.GroupScheme.Lie.ScalarExtension
import Mathlib.AlgebraicGeometry.Morphisms.Finite

/-! # Finite root index implies semisimplicity for self-centralizing maximal tori

The "if" half of Milne Proposition 21.48, reduced to the self-centralizing property of maximal
tori (`MaximalTorusCentralizerStatement`, Milne Corollary 17.84). -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Opposite TensorProduct
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false

section Field

variable {k : Type u} [Field k]

/-- Over a field, a pure tensor `b ⊗ v` with `v ≠ 0` vanishes only if `b = 0`. -/
theorem eq_zero_of_tmul_eq_zero {B V : Type*} [CommRing B] [Algebra k B] [AddCommGroup V]
    [Module k V] {b : B} {v : V} (hv : v ≠ 0) (h : b ⊗ₜ[k] v = 0) : b = 0 := by
  obtain ⟨f, hf⟩ := Module.Projective.exists_dual_ne_zero k hv
  have h1 := congrArg ((TensorProduct.rid k B).toLinearMap ∘ₗ LinearMap.lTensor B f) h
  simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
    LinearMap.lTensor_tmul, TensorProduct.rid_tmul, map_zero] at h1
  rw [← one_smul k b, ← inv_mul_cancel₀ hf, mul_smul, h1, smul_zero]

variable {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom] {T : CommGroupScheme (Spec (CommRingCat.of k))}

/-- **Roots are trivial on central torus points over test algebras.** Let `w : Z ⟶ T` be a
homomorphism into a commutative group scheme with `i : T ⟶ G`, such that `w ≫ i` is central.
Then every root of `T` in `G` takes the value `1` at the image in `T` of every `B`-point of `Z`.
A central point acts trivially through `Ad` on the scalar extension of a nonzero root vector,
while it acts by the value of the root; over a field the scalar extension of a nonzero vector is
torsion-free. -/
theorem characterValue_root_eq_one_of_isCentral (i : T.toGrp ⟶ G)
    {Z : GroupScheme (Spec (CommRingCat.of k))} (w : Z ⟶ T.toGrp) (hc : IsCentral (w ≫ i))
    {B : Type u} [CommRing B] [Algebra k B] (s : Lie.AffinePoints Z B)
    {α : characterLattice T} (hα : α ∈ roots i) :
    Lie.characterValue α (s ≫ w.hom.hom) = 1 := by
  obtain ⟨X, hXmem, hX0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hα.2
  have hw := (mem_weightSpace.1 hXmem) B (s ≫ w.hom.hom)
  have hz := IsCentral.adjoint_eq (w ≫ i) hc s (lieKernelMapLinear G (Algebra.ofId k B) X)
  rw [Grp.comp_hom_hom, ← Category.assoc, hw] at hz
  have h0 : ((Lie.characterValue α (s ≫ w.hom.hom) : B) - 1) ⊗ₜ[k] X = 0 := by
    apply (Lie.kernelScalarExtension G B).injective
    rw [Lie.kernelScalarExtension_tmul, map_zero, sub_smul, one_smul, hz, sub_self]
  exact Units.ext (sub_eq_zero.1 (eq_zero_of_tmul_eq_zero hX0 h0))

omit [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom] in
/-- Over the spectrum of a test algebra, a character value equal to `1` gives a point character
equal to `1`: both are the unit attached to the composite point of `𝔾_m`. -/
theorem pointCharacters_algSpec_eq_one {A : (CommAlgCat k)ᵒᵖ}
    (t : Lie.AffinePoints T.toGrp A.unop) {α : characterLattice T}
    (hv : Lie.characterValue α t = 1) :
    characterLattice.pointCharacters T ((algSpec _).obj A) t (.ofAdd α) = 1 := by
  have h1 := congrArg Units.val hv
  rw [Lie.characterValue, Gm.affinePointsEquiv_val, Units.val_one] at h1
  exact Units.ext ((Scheme.ΓSpecIso (CommRingCat.of A.unop)).commRingCatIsoToRingEquiv.injective
    (h1.trans (map_one _).symm))

/-- **Roots are trivial on central torus points.** In the situation of
`characterValue_root_eq_one_of_isCentral`, every root of `T` in `G` takes the value `1` at the
image in `T` of every point of `Z` over an affine test scheme. -/
theorem pointCharacters_root_eq_one_of_isCentral (i : T.toGrp ⟶ G)
    {Z : GroupScheme (Spec (CommRingCat.of k))} (w : Z ⟶ T.toGrp) (hc : IsCentral (w ≫ i))
    (U : Over (Spec (CommRingCat.of k))) [IsAffine U.left] (x : U ⟶ Z.X)
    {α : characterLattice T} (hα : α ∈ roots i) :
    characterLattice.pointCharacters T U (x ≫ w.hom.hom) (.ofAdd α) = 1 := by
  obtain ⟨A, ⟨e⟩⟩ := (essImage_algSpec (G := U)).2 inferInstance
  let s : Lie.AffinePoints Z A.unop := e.hom ≫ x
  have hp := pointCharacters_algSpec_eq_one (s ≫ w.hom.hom)
    (characterValue_root_eq_one_of_isCentral i w hc s hα)
  have hn := characterLattice.pointCharacters_naturality T e.inv (s ≫ w.hom.hom) α
  rw [hp, map_one] at hn
  simpa only [s, Category.assoc, Iso.inv_hom_id_assoc] using hn

end Field

set_option linter.defProp false in
/-- **Finite root index implies semisimplicity** (the "if" half of Milne Proposition 21.48),
assuming that maximal tori of connected reductive groups are self-centralizing (Milne
Corollary 17.84). The scheme-theoretic centre `Z` of `G` lies in the centralizer of the split
maximal torus `T`, hence factors through `T`. Every root is trivial on `Z`, so the universal point
of `Z` in `T` comes from a point of the diagonalizable group `D(X*(T)/ℤΦ)`. The resulting map
`Z ⟶ D(X*(T)/ℤΦ)` is a closed immersion, and `D(X*(T)/ℤΦ)` is finite because its character group
is finite. -/
def splitSemisimpleOfFiniteRootIndex_of_maximalTorusCentralizer
    (hcent : MaximalTorusCentralizerStatement.{u}) :
    SplitSemisimpleOfFiniteRootIndexStatement.{u} := by
  classical
  intro k _ G hG T hT i hi J P hP hfin
  refine ⟨hG, ?_⟩
  have := hG.isAffineHom
  have := hG.smooth
  obtain ⟨Z, z, hz⟩ := schemeTheoreticCenterExistence k G hG
  have hself := hcent k G hG T i hi
  have : IsClosedImmersion i.hom.hom.left := hi.2.1
  have hri : (SubgroupFunctor.range i).IsRepresentedBy i := ⟨Over.mono_of_mono_left _, rfl⟩
  have hle : SubgroupFunctor.range z ≤ SubgroupFunctor.range i := by
    rw [← hself, hz.2]
    intro U g hg V a t
    exact hg V a (t ≫ i.hom.hom)
  set w := hri.liftOfLE z hle with hwdef
  have hw : w ≫ i = z := hri.liftOfLE_comp z hle
  have hc : IsCentral (w ≫ i) := by
    rw [hw]
    exact hz.isCentral
  have : IsClosedImmersion z.hom.hom.left := hz.1
  have : IsAffineHom Z.X.hom := by
    rw [← Over.w z.hom.hom]
    infer_instance
  have : IsAffine Z.X.left := isAffine_of_isAffineHom Z.X.hom
  -- The universal point of `Z` in `T`, as a character of the character lattice.
  let φ := characterLattice.pointCharacters T Z.X w.hom.hom
  have hroot : ∀ j, φ (.ofAdd (P.root j)) = 1 := by
    intro j
    have hα : P.root j ∈ roots i := hP.2.1 ▸ ⟨j, rfl⟩
    have h := pointCharacters_root_eq_one_of_isCentral i w hc Z.X (𝟙 _) hα
    rwa [Category.id_comp] at h
  let f : characterLattice T →ₗ[ℤ] Additive (Γ(Z.X.left, ⊤))ˣ :=
    (MonoidHom.toAdditiveRight φ).toIntLinearMap
  have hker : P.rootSpan ℤ ≤ LinearMap.ker f := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨j, rfl⟩
    change Additive.ofMul (φ (.ofAdd (P.root j))) = 0
    rw [hroot j]
    rfl
  let Q := characterLattice T ⧸ P.rootSpan ℤ
  let ψ : Multiplicative Q →* (Γ(Z.X.left, ⊤))ˣ :=
    AddMonoidHom.toMultiplicativeLeft ((P.rootSpan ℤ).liftQ f hker).toAddMonoidHom
  let D := Diagonalizable.groupScheme (CommRingCat.of k) Q
  let π : Multiplicative (characterLattice T) →* Multiplicative Q :=
    AddMonoidHom.toMultiplicative (P.rootSpan ℤ).mkQ.toAddMonoidHom
  let g : Z.X ⟶ D.X := (Diagonalizable.characterPointsEquiv (CommRingCat.of k) Q Z.X).symm ψ
  let incl : D.X ⟶ T.X := (characterLattice.pointCharactersEquiv T hT D.X).symm
    ((Diagonalizable.characterPointsEquiv (CommRingCat.of k) Q D.X (𝟙 _)).comp π)
  have hgincl : g ≫ incl = w.hom.hom := by
    apply (characterLattice.pointCharactersEquiv T hT Z.X).injective
    apply MonoidHom.ext
    intro χ
    change characterLattice.pointCharacters T Z.X (g ≫ incl) (.ofAdd χ.toAdd) =
      φ (.ofAdd χ.toAdd)
    rw [characterLattice.pointCharacters_naturality]
    have hincl : characterLattice.pointCharacters T D.X incl =
        (Diagonalizable.characterPointsEquiv (CommRingCat.of k) Q D.X (𝟙 _)).comp π :=
      (characterLattice.pointCharactersEquiv T hT D.X).apply_symm_apply _
    rw [hincl, MonoidHom.comp_apply]
    change Units.map g.left.appTop.hom.toMonoidHom
        (Diagonalizable.characterPointsEquiv (CommRingCat.of k) Q D.X (𝟙 _)
          (.ofAdd ((P.rootSpan ℤ).mkQ χ.toAdd))) = _
    rw [← Diagonalizable.characterPointsEquiv_naturality, Category.comp_id,
      MulEquiv.apply_symm_apply]
    rfl
  have hcomp : g.left ≫ (incl.left ≫ i.hom.hom.left) = z.hom.hom.left := by
    rw [← Category.assoc, ← Over.comp_left, hgincl, ← Over.comp_left, ← Grp.comp_hom_hom, hw]
  have : IsClosedImmersion (g.left ≫ (incl.left ≫ i.hom.hom.left)) := by
    rw [hcomp]
    infer_instance
  have : IsSeparated (incl.left ≫ i.hom.hom.left) := by
    have : IsSeparated ((incl.left ≫ i.hom.hom.left) ≫ G.X.hom) := by
      rw [Category.assoc, Over.w i.hom.hom, Over.w incl]
      change IsSeparated (Spec.map (CommRingCat.ofHom
        (algebraMap k (AddMonoidAlgebra k Q))))
      infer_instance
    exact IsSeparated.of_comp _ G.X.hom
  have : IsClosedImmersion g.left := IsClosedImmersion.of_comp g.left (incl.left ≫ i.hom.hom.left)
  have : Module.Finite k (AddMonoidAlgebra k Q) :=
    Module.Finite.equiv (AddMonoidAlgebra.coeffLinearEquiv k).symm
  have hD : IsFinite D.X.hom := by
    change IsFinite (Spec.map (CommRingCat.ofHom (algebraMap k (AddMonoidAlgebra k Q))))
    rw [IsFinite.SpecMap_iff]
    exact RingHom.finite_algebraMap.2 inferInstance
  refine ⟨Z, z, hz, ?_⟩
  rw [← Over.w g]
  infer_instance

/-- Self-centralizing maximal tori give the published split semisimplicity criterion
(Milne Proposition 21.48 with Definition C.34) in both its root and coroot forms. -/
theorem splitSemisimpleRootDatum_of_maximalTorusCentralizer
    (hcent : MaximalTorusCentralizerStatement.{u}) :
    SplitSemisimpleRootDatumStatement.{u} :=
  splitSemisimpleRootDatum_of_finiteRootIndex
    (splitSemisimpleOfFiniteRootIndex_of_maximalTorusCentralizer hcent)

end Langlands.GroupScheme
