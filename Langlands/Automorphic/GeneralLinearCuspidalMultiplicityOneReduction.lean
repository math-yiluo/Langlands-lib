import Langlands.Automorphic.GeneralLinearCuspidalSummandEquivalenceStatement
import Langlands.Automorphic.CuspidalOperatorMultiplicityOneStatement
import Langlands.Global.AdeleQuotientCompactProof

/-! # Multiplicity one for the cuspidal spectrum of `GL_n`, reduced to three named premises

`GeneralLinearCuspidalMultiplicityOneStatement` (Getz–Hahn, Theorem 11.4.3; Shalika 1974,
Theorem 5.5) follows from

* `CuspidalOperatorMultiplicityOneStatement`: equivalent irreducible cuspidal operator
  realizations have the same space of forms;
* `GeneralLinearCuspidalSummandRealizationStatement`: every irreducible closed invariant
  subspace of the cuspidal `L²` space is the closure of the `L²` classes of the forms of a
  cuspidal operator realization;
* `GeneralLinearCuspidalSummandEquivalenceStatement`: realizations of isometrically equivalent
  irreducible summands are equivalent.

The case `n = 0` is proved directly: the quotient `[GL_0]` is a point, so its `L²` space has
dimension at most one. None of the three premises is proved here. -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField MeasureTheory
open scoped CategoryTheory.MonObj

set_option autoImplicit false

namespace Langlands.Automorphic.GroupSchemeFunctions

open Langlands.Global Langlands.Global.AdelicGroupPoints
open Langlands.Global.PositiveRealTorus Langlands.GroupScheme

local instance multiplicityOneReductionGeneralLinearIsAffine (F : Type u) [Field F] (n : ℕ) :
    IsAffine (GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of F)).X.left :=
  GroupScheme.GeneralLinear.isAffine_groupScheme (Fin n) (CommRingCat.of F)

local instance multiplicityOneReductionGeneralLinearSmooth (F : Type u) [Field F] (n : ℕ) :
    Smooth (GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of F)).X.hom :=
  GroupScheme.GeneralLinear.smoothStatement (Fin n) (CommRingCat.of F)

namespace GeneralLinearCuspidalMultiplicityOne

/-- On a measure space with at most one point, every `L²` class is a multiple of any nonzero
one. -/
theorem lp_eq_smul_of_subsingleton {α : Type*} [MeasurableSpace α] [Subsingleton α]
    {ν : Measure α} (f g : Lp ℂ 2 ν) (hf : f ≠ 0) : ∃ c : ℂ, g = c • f := by
  rcases isEmpty_or_nonempty α with hα | ⟨⟨x₀⟩⟩
  · exact absurd (Lp.ext (ae_of_all _ fun x => isEmptyElim x)) hf
  · have hfx : (f : α → ℂ) x₀ ≠ 0 := by
      intro h0
      apply hf
      apply Lp.ext
      filter_upwards [Lp.coeFn_zero ℂ 2 ν] with x hx
      rw [hx, Subsingleton.elim x x₀, h0]
      rfl
    refine ⟨(g : α → ℂ) x₀ / (f : α → ℂ) x₀, ?_⟩
    apply Lp.ext
    filter_upwards [Lp.coeFn_smul ((g : α → ℂ) x₀ / (f : α → ℂ) x₀) f] with x hx
    rw [hx, Pi.smul_apply, Subsingleton.elim x x₀, smul_eq_mul, div_mul_cancel₀ _ hfx]

/-- On a measure space with at most one point, a nonzero submodule of a subspace of `L²`
contains every submodule. -/
theorem submodule_le_of_subsingleton {α : Type*} [MeasurableSpace α] [Subsingleton α]
    {ν : Measure α} {S : Submodule ℂ (Lp ℂ 2 ν)} (P Q : Submodule ℂ S) (hQ : Q ≠ ⊥) :
    P ≤ Q := by
  obtain ⟨q, hq, hq0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hQ
  intro x _
  have hq0' : (q : Lp ℂ 2 ν) ≠ 0 := fun h => hq0 (Subtype.ext h)
  obtain ⟨c, hc⟩ := lp_eq_smul_of_subsingleton (q : Lp ℂ 2 ν) (x : Lp ℂ 2 ν) hq0'
  have hx : x = c • q := Subtype.ext hc
  rw [hx]
  exact Q.smul_mem c hq

/-- On a measure space with at most one point, two nonzero submodules of a subspace of `L²`
are equal. -/
theorem submodule_eq_of_subsingleton {α : Type*} [MeasurableSpace α] [Subsingleton α]
    {ν : Measure α} {S : Submodule ℂ (Lp ℂ 2 ν)} (P Q : Submodule ℂ S) (hP : P ≠ ⊥)
    (hQ : Q ≠ ⊥) : P = Q :=
  le_antisymm (submodule_le_of_subsingleton P Q hQ) (submodule_le_of_subsingleton Q P hP)

/-- The adelic points of `GL_0` form a one-point group. -/
theorem subsingleton_adelicGroupPoints_zero (F : Type u) [Field F] [NumberField F] :
    Subsingleton (AdelicGroupPoints F
      (GroupScheme.GeneralLinear.groupScheme (Fin 0) (CommRingCat.of F))) :=
  ⟨fun _ _ => (GeneralLinearGroupPoints.adelicHomeomorph F 0).injective
    (Units.ext (Subsingleton.elim _ _))⟩

/-- The positive-central rational quotient of `GL_0` has at most one point. -/
theorem subsingleton_positiveRationalQuotient_zero (F : Type u) [Field F] [NumberField F]
    (T : CommGroupScheme (Spec (CommRingCat.of F)))
    (i : T.toGrp ⟶ GroupScheme.GeneralLinear.groupScheme (Fin 0) (CommRingCat.of F)) :
    Subsingleton (PositiveRationalQuotient F
      (GroupScheme.GeneralLinear.groupScheme (Fin 0) (CommRingCat.of F)) T i) := by
  have := subsingleton_adelicGroupPoints_zero F
  refine ⟨fun a b => ?_⟩
  obtain ⟨x, rfl⟩ := LeftCosetSpace.mk_surjective _ a
  obtain ⟨y, rfl⟩ := LeftCosetSpace.mk_surjective _ b
  rw [Subsingleton.elim x y]

/-- An `L²` class on the positive-central rational quotient of `GL_{r+1}` is determined by a
continuous function on `GL_{r+1}(𝔸_F)` of which it is the class. -/
theorem isGeneralLinearFormClass_unique (F : Type u) [Field F] [NumberField F] (r : ℕ)
    (T : CommGroupScheme (Spec (CommRingCat.of F)))
    (i : T.toGrp ⟶ GroupScheme.GeneralLinear.groupScheme (Fin (r + 1)) (CommRingCat.of F))
    {φ ψ : Lp ℂ 2 (positiveRationalQuotientHaarMeasure F
      (GroupScheme.GeneralLinear.groupScheme (Fin (r + 1)) (CommRingCat.of F)) T i)}
    {f : Langlands.Automorphic.ContinuousRationalFunctions F (r + 1)}
    (hφ : IsGeneralLinearFormClass F r T i φ f) (hψ : IsGeneralLinearFormClass F r T i ψ f) :
    φ = ψ := by
  obtain ⟨h, hhf, hφh⟩ := hφ
  obtain ⟨h', hh'f, hψh'⟩ := hψ
  have hh : h = h' := positiveQuotientContinuousPullback_injective F _ T i
    ((continuousGeneralLinearEquiv F (r + 1)).injective (hhf.trans hh'f.symm))
  subst hh
  exact Lp.ext (hφh.trans hψh'.symm)

/-- Two cuspidal operator realizations with the same space of forms have the same image in
any subspace of `L²` of the quotient, when each vector is sent to the class of its function. -/
theorem range_eq_of_realization_eq (F : Type u) [Field F] [NumberField F]
    [CompactSpace (AdeleQuotient F)] {r : ℕ}
    (T : CommGroupScheme (Spec (CommRingCat.of F)))
    (i : T.toGrp ⟶ GroupScheme.GeneralLinear.groupScheme (Fin (r + 1)) (CommRingCat.of F))
    (S : Submodule ℂ (Lp ℂ 2 (positiveRationalQuotientHaarMeasure F
      (GroupScheme.GeneralLinear.groupScheme (Fin (r + 1)) (CommRingCat.of F)) T i)))
    (R R' : Langlands.Automorphic.CuspidalOperatorRealization F r)
    (hRR : R.realization = R'.realization)
    (Φ : R.Space →ₗ[ℂ] S) (Φ' : R'.Space →ₗ[ℂ] S)
    (hΦ : ∀ f : R.Space,
      IsGeneralLinearFormClass F r T i (Φ f : Lp ℂ 2 _) (R.realization.toContinuous f))
    (hΦ' : ∀ f : R'.Space,
      IsGeneralLinearFormClass F r T i (Φ' f : Lp ℂ 2 _) (R'.realization.toContinuous f)) :
    LinearMap.range Φ = LinearMap.range Φ' := by
  obtain ⟨ρ, hirr, hcusp⟩ := R
  obtain ⟨ρ', hirr', hcusp'⟩ := R'
  dsimp only at hRR
  subst hRR
  have hΦΦ : Φ = Φ' := LinearMap.ext fun f =>
    Subtype.ext (isGeneralLinearFormClass_unique F r T i (hΦ f) (hΦ' f))
  rw [hΦΦ]

end GeneralLinearCuspidalMultiplicityOne

open GeneralLinearCuspidalMultiplicityOne in
/-- **Multiplicity one for the cuspidal spectrum of `GL_n`, from three named premises.**
Operator multiplicity one for cuspidal realizations, the realization of every irreducible
cuspidal `L²` summand by cusp forms, and the equivalence of the realizations of isometrically
equivalent summands together imply `GeneralLinearCuspidalMultiplicityOneStatement`. The case
`n = 0` uses none of them. -/
theorem generalLinearCuspidalMultiplicityOne_of_summandEquivalence
    (hOne : Langlands.Automorphic.CuspidalOperatorMultiplicityOneStatement.{u})
    (hReal : GeneralLinearCuspidalSummandRealizationStatement.{u})
    (hEquiv : GeneralLinearCuspidalSummandEquivalenceStatement.{u}) :
    GeneralLinearCuspidalMultiplicityOneStatement.{u} := by
  intro F _ _ n
  cases n with
  | zero =>
    intro hPD T i hi _ I _ e hc _ hG S πc P Q hP hQ _ _ _
    have := subsingleton_positiveRationalQuotient_zero F T i
    exact submodule_eq_of_subsingleton P Q hP.1 hQ.1
  | succ r =>
    intro hPD T i hi _ I _ e hc _ hG S πc P Q hP hQ hPi U hU
    have : CompactSpace (AdeleQuotient F) := compactSpace_adeleQuotient F
    obtain ⟨R, Φ, hΦ, hΦP⟩ := hReal F r hPD T i hi I e hc P hP
    obtain ⟨R', Φ', hΦ', hΦQ⟩ := hReal F r hPD T i hi I e hc Q hQ
    have hRR := hOne F r R R'
      (hEquiv F r hPD T i hi I e hc P Q hP hQ hPi U hU R R' Φ Φ' hΦ hΦP hΦ' hΦQ)
    rw [← hΦP, ← hΦQ, range_eq_of_realization_eq F T i S R R' hRR Φ Φ' hΦ hΦ']

end Langlands.Automorphic.GroupSchemeFunctions
