import Langlands.Global.PrimeToRationalProfiniteIntegerComparison
import Langlands.Global.PrimeToIntegralProfiniteIntegerComparisonProof
import Mathlib.RingTheory.Flat.Localization
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.TensorProduct.Maps

noncomputable section
open scoped TensorProduct

namespace Langlands.Global

private def rationalLift {R A : Type*} [CommRing R] [CommRing A] [Algebra ℚ A]
    (f : R →+* A) : (ℚ ⊗[ℤ] R) →ₐ[ℚ] A :=
  Algebra.TensorProduct.lift (Algebra.ofId ℚ A) f.toIntAlgHom
    (fun _ _ => Commute.all _ _)

private theorem rationalLift_injective {R A : Type*}
    [CommRing R] [CommRing A] [Algebra ℚ A]
    (f : R →+* A) (hf : Function.Injective f) :
    Function.Injective (rationalLift f) := by
  let : Module.Flat ℤ ℚ := IsLocalization.flat ℚ (nonZeroDivisors ℤ)
  let g := f.toIntAlgHom.toLinearMap
  let e := IsLocalization.moduleLid (nonZeroDivisors ℤ) ℚ A
  have he : (rationalLift f).toLinearMap = e.toLinearMap.comp (g.baseChange ℚ) := by
    apply TensorProduct.AlgebraTensorModule.ext
    intro q a
    change algebraMap ℚ A q * f a = q • f a
    exact (Algebra.smul_def q (f a)).symm
  change Function.Injective (rationalLift f).toLinearMap
  rw [he]
  exact e.injective.comp (Module.Flat.lTensor_preserves_injective_linearMap g hf)

private theorem finiteRestriction_surjective (m : ℕ) :
    Function.Surjective (primeToFiniteRestriction m) := by
  classical
  intro a
  let b : ∀ v : FinitePlace ℚ, FiniteCompletion ℚ v :=
    fun v => if hv : (m : NumberField.RingOfIntegers ℚ) ∉ v.asIdeal
      then a ⟨v, hv⟩ else 0
  have hb : ∀ᶠ v in Filter.cofinite, b v ∈ v.adicCompletionIntegers ℚ := by
    apply Filter.eventually_cofinite.mpr
    have ha := Filter.eventually_cofinite.mp a.property
    apply (ha.image Subtype.val).subset
    intro v hv
    by_cases hm : (m : NumberField.RingOfIntegers ℚ) ∉ v.asIdeal
    · refine ⟨⟨v, hm⟩, ?_, rfl⟩
      change a ⟨v, hm⟩ ∉ v.adicCompletionIntegers ℚ
      change b v ∉ v.adicCompletionIntegers ℚ at hv
      dsimp only [b] at hv
      rw [dite_eq_left hm] at hv
      exact hv
    · apply False.elim
      apply hv
      dsimp only [b]
      rw [dite_eq_right hm]
      exact (v.adicCompletionIntegers ℚ).zero_mem
  refine ⟨⟨b, hb⟩, ?_⟩
  apply Subtype.ext
  funext v
  change b v.val = a v
  dsimp only [b]
  rw [dite_eq_left v.property]

private theorem awayComparison_of_integral
    (h : RationalProfiniteIntegerAdeleComparison) (m : ℕ)
    (e₀ : PrimeToProfiniteIntegerRing m ≃+* primeToIntegralFiniteAdeles m)
    (hc : Continuous e₀) (hci : Continuous e₀.symm)
    (hz : ∀ z : ℤ, (e₀ (PrimeToProfiniteIntegerRing.intCastHom m z) :
      PrimeToFiniteAdeles m) = algebraMap ℚ (PrimeToFiniteAdeles m) (z : ℚ))
    (hr : ∀ a : ProfiniteIntegerRing,
      e₀ (PrimeToProfiniteIntegerRing.restrict m a) =
        primeToIntegralRestriction m (h.choose a)) :
    PrimeToRationalProfiniteIntegerAdeleComparison h m := by
  let f := (primeToIntegralInclusion m).comp e₀.toRingHom
  let g := rationalLift f
  let r := Algebra.TensorProduct.map (AlgHom.id ℚ ℚ)
    (PrimeToProfiniteIntegerRing.restrict m).toIntAlgHom
  have hg (q : ℚ) (a : PrimeToProfiniteIntegerRing m) :
      g (q ⊗ₜ[ℤ] a) =
        algebraMap ℚ (PrimeToFiniteAdeles m) q * (e₀ a : PrimeToFiniteAdeles m) := rfl
  have square (x : ℚ ⊗[ℤ] ProfiniteIntegerRing) :
      g (r x) = primeToFiniteRestriction m (h.choose_spec.2.2.2.choose x) := by
    induction x using TensorProduct.inductionOn with
    | tmul q a =>
      change g (q ⊗ₜ[ℤ] PrimeToProfiniteIntegerRing.restrict m a) = _
      rw [hg, hr, h.choose_spec.2.2.2.choose_spec]
      simp
    | add x y hx hy => simp_all
  have hinj : Function.Injective g :=
    rationalLift_injective f (Subtype.val_injective.comp e₀.injective)
  have hsurj : Function.Surjective g := by
    intro a
    obtain ⟨b, hb⟩ := finiteRestriction_surjective m a
    refine ⟨r (h.choose_spec.2.2.2.choose.symm b), ?_⟩
    rw [square, AlgEquiv.apply_symm_apply, hb]
  refine ⟨e₀, hc, hci, hz, hr, AlgEquiv.ofBijective g ⟨hinj, hsurj⟩, hg, ?_⟩
  intro q a
  exact square (q ⊗ₜ[ℤ] a)

private theorem awayComparisons_of_integral
    (hi : PrimeToIntegralProfiniteIntegerAdeleComparisons) :
    PrimeToRationalProfiniteIntegerAdeleComparisons := by
  intro h m
  obtain ⟨e₀, hc, hci, hz, hr⟩ :=
    hi h.choose h.choose_spec.1 h.choose_spec.2.1 h.choose_spec.2.2.1 m
  exact awayComparison_of_integral h m e₀ hc hci hz hr

/-- The normalized away comparisons for every natural modulus, coupled to the
full integral and rational witnesses chosen from the supplied hypothesis. -/
theorem primeToRationalProfiniteIntegerAdeleComparisons :
    PrimeToRationalProfiniteIntegerAdeleComparisons :=
  awayComparisons_of_integral primeToIntegralProfiniteIntegerAdeleComparisons

end Langlands.Global
