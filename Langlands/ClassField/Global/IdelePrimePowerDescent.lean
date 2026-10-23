import Langlands.ClassField.Global.IdeleInvariantDescent
import Mathlib.Data.Nat.Factorization.Basic

/-! # Descent from prime-power coverage by local degrees -/

noncomputable section

namespace Langlands.ClassField.Global

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open scoped NumberField Langlands.Global.AdelicFunctoriality.FiniteExtension
open Langlands.Global.AdelicFunctoriality Langlands.Global.CompletionPadic
open Langlands.ClassFieldTheory.Local

universe u

variable (I : ∀ (p : ℕ) [Fact p.Prime], InvariantFamily.{u, u} p)
  (hI : ∀ (p : ℕ) [Fact p.Prime], (I p).RelativeImages)
  {F E : Type u} [Field F] [NumberField F] [Field E] [NumberField E]
  [Algebra F E] [IsGalois F E]
  (wf : ∀ v : HeightOneSpectrum (𝓞 F), FinitePlacesAbove E v)
  (wi : ∀ v : InfinitePlace F, InfinitePlacesAbove E v)

private theorem denominator_natCard (n : ℕ) (hn : 0 < n) :
    Nat.card (denominatorSubgroup n) = n :=
  (Nat.card_congr (denominatorEquiv n hn).toEquiv).symm.trans (Nat.card_zmod n)

/-- Coverage of each prime-power divisor of the global degree by some finite
local degree, for the chosen places. -/
def PrimePowerLocalDegreeCoverage : Prop :=
  ∀ p k : ℕ, p.Prime → 0 < k → p ^ k ∣ Module.finrank F E →
    ∃ v : HeightOneSpectrum (𝓞 F),
      haveI := (wf v).2
      p ^ k ∣ Module.finrank (padicField v).Carrier ((wf v).1.adicCompletion E)

variable (hcover : PrimePowerLocalDegreeCoverage wf)

include hcover in
/-- Prime-power local degree coverage makes the total invariant have full
global denominator range, without a single place of full global degree. -/
theorem totalIdeleInvariant_range_of_primePowerLocalDegreeCoverage :
    (totalIdeleInvariant I hI wf wi).range =
      denominatorSubgroup (Module.finrank F E) := by
  have hn : 0 < Module.finrank F E := Module.finrank_pos
  let : NeZero (Module.finrank F E) := ⟨hn.ne'⟩
  let : Finite (denominatorSubgroup (Module.finrank F E)) :=
    Finite.of_equiv (ZMod (Module.finrank F E)) (denominatorEquiv _ hn).toEquiv
  have hle : (totalIdeleInvariant I hI wf wi).range ≤
      denominatorSubgroup (Module.finrank F E) := by
    rintro _ ⟨c, rfl⟩
    exact totalIdeleInvariant_mem_denominator I hI wf wi c
  let : Finite (totalIdeleInvariant I hI wf wi).range :=
    Finite.of_injective (AddSubgroup.inclusion hle) (AddSubgroup.inclusion_injective hle)
  have hdvd : Module.finrank F E ∣ Nat.card (totalIdeleInvariant I hI wf wi).range := by
    apply (Nat.dvd_iff_prime_pow_dvd_dvd _ _).2
    intro p k hp hpk
    by_cases hk : k = 0
    · simp [hk]
    obtain ⟨v, hv⟩ := hcover p k hp (Nat.pos_of_ne_zero hk) hpk
    let := (wf v).2
    let := FiniteExtension.local_finite v (wf v).1
    let := isGalois_adicCompletion v (wf v).1
    let := Fintype.ofFinite ((E ≃ₐ[F] E) ⧸ (FundamentalClass.decompositionHom v (wf v).1).range)
    have hinj : Function.Injective
        (localDenominatorToTotalInvariantRange I hI wf wi v) := by
      intro a b hab
      apply Subtype.ext
      exact congrArg (fun x : (totalIdeleInvariant I hI wf wi).range =>
        (x : RationalModIntegers)) hab
    have hd := AddSubgroup.card_dvd_of_injective
      (localDenominatorToTotalInvariantRange I hI wf wi v) hinj
    rw [denominator_natCard _ Module.finrank_pos] at hd
    exact hv.trans hd
  apply AddSubgroup.eq_of_le_of_card_ge hle
  rw [denominator_natCard _ hn]
  exact Nat.le_of_dvd Nat.card_pos hdvd

include hcover in
/-- Under prime-power local degree coverage, the denominator-valued total
invariant is surjective. -/
theorem totalIdeleInvariantToDenominator_surjective_of_primePowerLocalDegreeCoverage :
    Function.Surjective (totalIdeleInvariantToDenominator I hI wf wi) := by
  intro y
  have hy : y.val ∈ (totalIdeleInvariant I hI wf wi).range := by
    rw [totalIdeleInvariant_range_of_primePowerLocalDegreeCoverage I hI wf wi hcover]
    exact y.property
  obtain ⟨c, hc⟩ := hy
  exact ⟨c, Subtype.ext hc⟩

variable
  (hrec : ∀ x : relativeCohomology F E 2, Reciprocity.SumOfInvariantsVanishes I x)
  [Finite (relativeIdeleClassCohomology F E 2)]
  (hcard : Nat.card (relativeIdeleClassCohomology F E 2) ≤ Module.finrank F E)

/-- Reciprocity, the cohomology order bound and prime-power local degree
coverage give the actual idele-class invariant equivalence. -/
def ideleClassInvariantEquivOfPrimePowerLocalDegreeCoverage :
    relativeIdeleClassCohomology F E 2 ≃+ denominatorSubgroup (Module.finrank F E) :=
  Langlands.FiniteInvariantDescent.equiv
    (ideleQuotientCohomologyMap F E 2).hom.toAddMonoidHom
    (totalIdeleInvariantToDenominator I hI wf wi)
    (fun c hc => totalIdeleInvariantToDenominator_eq_zero_of_ideleQuotient_eq_zero
      I hI wf wi hrec c hc)
    (totalIdeleInvariantToDenominator_surjective_of_primePowerLocalDegreeCoverage
      I hI wf wi hcover)
    (by rwa [denominator_natCard _ (Module.finrank_pos : 0 < Module.finrank F E)])

@[simp] theorem ideleClassInvariantEquivOfPrimePowerLocalDegreeCoverage_apply_quotient
    (c : relativeIdeleCohomology F E 2) :
    ideleClassInvariantEquivOfPrimePowerLocalDegreeCoverage I hI wf wi hcover hrec hcard
      (ideleQuotientCohomologyMap F E 2 c) =
        totalIdeleInvariantToDenominator I hI wf wi c :=
  Langlands.FiniteInvariantDescent.equiv_apply _ _ _ _ _ c

include I hI wf wi hcover hrec hcard in
/-- The same hypotheses imply surjectivity of the actual quotient cohomology map. -/
theorem ideleQuotientCohomologyMap_surjective_of_primePowerLocalDegreeCoverage :
    Function.Surjective (ideleQuotientCohomologyMap F E 2) :=
  Langlands.FiniteInvariantDescent.surjective_of_card_le
    (ideleQuotientCohomologyMap F E 2).hom.toAddMonoidHom
    (totalIdeleInvariantToDenominator I hI wf wi)
    (fun c hc => totalIdeleInvariantToDenominator_eq_zero_of_ideleQuotient_eq_zero
      I hI wf wi hrec c hc)
    (totalIdeleInvariantToDenominator_surjective_of_primePowerLocalDegreeCoverage
      I hI wf wi hcover)
    (by rwa [denominator_natCard _ (Module.finrank_pos : 0 < Module.finrank F E)])

end Langlands.ClassField.Global
