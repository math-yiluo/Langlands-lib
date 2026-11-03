import Langlands.GroupScheme.Rational.RelativeWeylChamberGeneration
import Langlands.GroupScheme.Rational.RelativeRootSignInclusionsStatement
import Langlands.GroupScheme.Rational.ParabolicNormalizerStatement
import Langlands.GroupScheme.Rational.NormalizerParabolicPoints
import Langlands.GroupScheme.Absolute.BorelStatement
import Langlands.GroupScheme.Dynamic.AffineRepresentability

/-! # Positive-root stabilizers from explicit geometric statements -/

set_option backward.isDefEq.respectTransparency false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace Dynamic

variable {S : Scheme.{u}} {G : GroupScheme S}

/-- Equality with the conjugate parabolic places a rational point in the
normalizer functor, including its conditions after every refinement. -/
theorem mem_normalizer_parabolic_of_conjugate_eq
    (χ : (Gm S).toGrp ⟶ G) (n : Over.mk (𝟙 S) ⟶ G.X)
    (h : parabolic (χ ≫ (G.innerIso n).hom) = parabolic χ) :
    n ∈ (parabolic χ).normalizer.carrier (Over.mk (𝟙 S)) := by
  intro V a x hx
  rw [comp_eq_constantPoint a n]
  have he : ∀ y : V ⟶ G.X, y ∈ (parabolic χ).carrier V ↔
      G.constantPoint n V * y * (G.constantPoint n V)⁻¹ ∈
        (parabolic χ).carrier V := by
    intro y
    simpa only [h] using (mem_parabolic_conj χ n (x := y))
  refine ⟨(he x).mp hx, (he _).mpr ?_⟩
  have hc : G.constantPoint n V *
      ((G.constantPoint n V)⁻¹ * x * G.constantPoint n V) *
        (G.constantPoint n V)⁻¹ = x := by group
  rwa [hc]

end Dynamic

section Field

variable {k : Type u} [Field k]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))}

/-- Parabolicity and self-normalization statements identify the full normalizer
of a dynamic parabolic with the parabolic itself. -/
theorem dynamicParabolic_normalizer_eq_of_structural_statements
    (hpar : ParabolicDynamicStatement.{u})
    (hself : ParabolicSelfNormalizerStatement.{u})
    (hG : IsConnectedReductive G)
    (χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G) :
    (Dynamic.parabolic χ).normalizer = Dynamic.parabolic χ := by
  have := hG.isAffineHom
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  let j := Dynamic.Affine.parabolicHom χ
  have hj := Dynamic.Affine.isClosedSubgroup_parabolicHom χ
  have hr := (Dynamic.Affine.isRepresentedBy_parabolicHom χ).2
  have hp : IsParabolicSubgroup j :=
    (hpar k G hG _ j hj).mpr ⟨χ, hr⟩
  rw [← hr]
  exact hself k G hG _ j hp

variable (i : T.toGrp ⟶ G) [Mono i.hom.hom.left]

/-- The character-action convention pairs a transformed character with the
cocharacter conjugated by the inverse normalizing point. -/
theorem latticePairing_weylAction (n : normalizerPoints i)
    (α : characterLattice T) (ν : cocharacterLattice T) :
    latticePairing T (weylAction i n α) ν =
      latticePairing T α (ν ≫ (normalizingAut i n).inv) := by
  simp only [weylAction_apply, latticePairing_apply, Category.assoc]

variable [IsAffineHom G.X.hom]

/-- Under the root-sign inclusion statement, a normalizing point preserving the
positive roots of a generic cocharacter normalizes its dynamic parabolic. -/
theorem mem_normalizer_parabolic_of_positive_roots
    (hsigns : RelativeRootSignInclusionsStatement.{u})
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    {ν : cocharacterLattice T} (hν : IsGenericCocharacter i ν)
    (n : normalizerPoints i)
    (hn : ∀ α ∈ relativeRoots i,
      0 < latticePairing T (weylAction i n α) ν ↔ 0 < latticePairing T α ν) :
    (n : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X) ∈
      (Dynamic.parabolic (CommGroupScheme.groupHom ν ≫ i)).normalizer.carrier
        (Over.mk (𝟙 (Spec (CommRingCat.of k)))) := by
  let σ := normalizingAut i n
  let ν' : cocharacterLattice T := ν ≫ σ.inv
  have hp : ∀ α ∈ relativeRoots i,
      0 < latticePairing T α ν' ↔ 0 < latticePairing T α ν := by
    intro α hα
    simpa only [latticePairing_weylAction i, ν', σ] using hn α hα
  have hν' : IsGenericCocharacter i ν' := by
    intro α hα
    rw [← latticePairing_weylAction i n α ν]
    exact hν _ (weylAction_mapsTo_relativeRoots i n hα)
  have hnn : ∀ α ∈ relativeRoots i,
      0 ≤ latticePairing T α ν' ↔ 0 ≤ latticePairing T α ν := by
    intro α hα
    have ha := hp α hα
    have hb := hν α hα
    have hc := hν' α hα
    omega
  have hP : Dynamic.parabolic (CommGroupScheme.groupHom ν' ≫ i) =
      Dynamic.parabolic (CommGroupScheme.groupHom ν ≫ i) :=
    le_antisymm
      ((hsigns k G hG T i hi ν' ν).1.mpr fun α hα => (hnn α hα).mp)
      ((hsigns k G hG T i hi ν ν').1.mpr fun α hα => (hnn α hα).mpr)
  have hconj : (CommGroupScheme.groupHom ν ≫ i) ≫
      (G.innerIso (n : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X)⁻¹).hom =
        CommGroupScheme.groupHom ν' ≫ i := by
    rw [Category.assoc, (isNormalizingPoint_normalizingAut i n).inv]
    rfl
  have hninv := Dynamic.mem_normalizer_parabolic_of_conjugate_eq
    (CommGroupScheme.groupHom ν ≫ i)
    (n : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X)⁻¹ (by rw [hconj, hP])
  exact inv_inv (n : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X) ▸
    ((Dynamic.parabolic (CommGroupScheme.groupHom ν ≫ i)).normalizer.carrier _).inv_mem hninv

/-- The actual positive-root stabilizer is trivial assuming the four named
geometric statements. None of these statements is discharged here. -/
theorem hasTrivialPositiveRootStabilizer_of_structural_statements
    (hsigns : RelativeRootSignInclusionsStatement.{u})
    (hpar : ParabolicDynamicStatement.{u})
    (hself : ParabolicSelfNormalizerStatement.{u})
    (hcent : GenericCentralizerStatement.{u})
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    {ν : cocharacterLattice T} (hν : IsGenericCocharacter i ν) :
    HasTrivialPositiveRootStabilizer i ν := by
  intro w hw
  obtain ⟨n, rfl⟩ := QuotientGroup.mk_surjective w
  have hn := mem_normalizer_parabolic_of_positive_roots i hsigns hG hi hν n hw
  rw [dynamicParabolic_normalizer_eq_of_structural_statements hpar hself hG] at hn
  have hz := hi.isSplitSubtorus.mem_centralizer_of_mem_parabolic ν n.property hn
  rw [hcent k G hG T i hi ν hν, torusCentralizer_carrier_base] at hz
  rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
  exact hz

end Field

/-- The conditional geometric reduction to trivial positive-root stabilizers,
with all four structural statements explicit and with no field restriction. -/
def PositiveRootStabilizerReductionStatement : Prop :=
  RelativeRootSignInclusionsStatement.{u} →
  ParabolicDynamicStatement.{u} →
  ParabolicSelfNormalizerStatement.{u} →
  GenericCentralizerStatement.{u} →
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))
    (hG : IsConnectedReductive G) (T : CommGroupScheme (Spec (CommRingCat.of k)))
    (i : T.toGrp ⟶ G) (hi : IsMaximalSplitTorus i) (ν : cocharacterLattice T),
    haveI := hG.isAffineHom
    haveI := hi.isSplitSubtorus.mono
    IsGenericCocharacter i ν → HasTrivialPositiveRootStabilizer i ν

/-- The explicit all-test normalizer argument proves the conditional reduction. -/
theorem positiveRootStabilizerReduction : PositiveRootStabilizerReductionStatement.{u} := by
  intro hsigns hpar hself hcent k _ G hG T i hi ν
  have := hG.isAffineHom
  have := hi.isSplitSubtorus.mono
  exact hasTrivialPositiveRootStabilizer_of_structural_statements
    i hsigns hpar hself hcent hG hi

end Langlands.GroupScheme
