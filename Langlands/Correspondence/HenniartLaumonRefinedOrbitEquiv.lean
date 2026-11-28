import Langlands.Correspondence.HenniartLaumonNumericalReductionStatement
import Langlands.Galois.CoefficientIdentification
import Mathlib.Data.Nat.Prime.Infinite

/-! # Refined orbit equivalence from Laumon's twist-equivariant rank shift -/

noncomputable section

set_option autoImplicit false

universe uK uΩ uW

namespace Langlands.Henniart.LocalNumerical

variable (K : Type uK) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (Ω : Type uΩ) [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]
    (ℓ : ℕ) [Fact ℓ.Prime] (ι : PadicAlgCl ℓ →+* ℂ)

private theorem ladicOrbit_eq_iff {k : ℕ}
    (a b : IrreducibleLadicClass.{uK, uΩ, uW} K Ω ℓ k.succPNat) :
    ladicUnramifiedOrbitClass K Ω ℓ k a = ladicUnramifiedOrbitClass K Ω ℓ k b ↔
      ∃ χ : ladicUnramifiedCharacters K Ω ℓ, ladicUnramifiedTwist K Ω ℓ k χ b = a := by
  let := ladicUnramifiedTwistAction.{uK, uΩ, uW} K Ω ℓ
  change Quotient.mk _ (⟨k, a⟩ : Σ r : ℕ, IrreducibleLadicClass K Ω ℓ r.succPNat) =
    Quotient.mk _ ⟨k, b⟩ ↔ _
  rw [Quotient.eq, MulAction.orbitRel_apply, MulAction.mem_orbit_iff]
  exact exists_congr fun χ => ⟨fun h => eq_of_heq (Sigma.mk.inj_iff.mp h).2,
    fun h => congrArg (Sigma.mk k) h⟩

variable {r r' s : ℕ}
  (Φ : {a : IrreducibleLadicClass.{uK, uΩ, uW} K Ω ℓ r.succPNat //
      LadicHasSwan K Ω ℓ ι a s} ≃
    {b : IrreducibleLadicClass.{uK, uΩ, uW} K Ω ℓ r'.succPNat //
      LadicHasSwan K Ω ℓ ι b s})
  (hΦ : ∀ (χ : ladicUnramifiedCharacters K Ω ℓ) (a : {a // LadicHasSwan K Ω ℓ ι a s}),
    ∃ ha : LadicHasSwan K Ω ℓ ι (ladicUnramifiedTwist K Ω ℓ r χ a.val) s,
      (Φ ⟨ladicUnramifiedTwist K Ω ℓ r χ a.val, ha⟩).val =
        ladicUnramifiedTwist K Ω ℓ r' χ (Φ a).val)

include hΦ in
private theorem ladicTorsionNumber_apply (a : {a // LadicHasSwan K Ω ℓ ι a s}) :
    ladicTorsionNumber K Ω ℓ (Φ a).val = ladicTorsionNumber K Ω ℓ a.val := by
  unfold ladicTorsionNumber
  apply Nat.card_congr
  apply Equiv.subtypeEquivRight
  intro χ
  obtain ⟨ha, hχ⟩ := hΦ χ a
  rw [← hχ]
  exact ⟨fun h => congrArg Subtype.val (Φ.injective (Subtype.ext h)),
    fun h => congrArg (fun c => (Φ c).val) (Subtype.ext h)⟩

include hΦ in
private theorem ladicOrbits_apply_eq_iff (a b : {a // LadicHasSwan K Ω ℓ ι a s}) :
    ladicUnramifiedOrbitClass K Ω ℓ r a.val = ladicUnramifiedOrbitClass K Ω ℓ r b.val ↔
      ladicUnramifiedOrbitClass K Ω ℓ r' (Φ a).val =
        ladicUnramifiedOrbitClass K Ω ℓ r' (Φ b).val := by
  rw [ladicOrbit_eq_iff K Ω ℓ, ladicOrbit_eq_iff K Ω ℓ]
  apply exists_congr
  intro χ
  obtain ⟨hb, hχ⟩ := hΦ χ b
  rw [← hχ]
  exact ⟨fun h => congrArg (fun c => (Φ c).val) (Subtype.ext h),
    fun h => congrArg Subtype.val (Φ.injective (Subtype.ext h))⟩

/-- A twist-equivariant bijection of fixed-Swan classes identifies the
refined orbit strata at every torsion number. -/
def ladicRefinedStratumEquiv (f : ℕ) :
    ladicRefinedStratum.{uK, uΩ, uW} K Ω ℓ ι r s f ≃
      ladicRefinedStratum.{uK, uΩ, uW} K Ω ℓ ι r' s f := by
  let A := {a : {a : IrreducibleLadicClass.{uK, uΩ, uW} K Ω ℓ r.succPNat //
      LadicHasSwan K Ω ℓ ι a s} // ladicTorsionNumber K Ω ℓ a.val = f}
  let left (a : A) : ladicRefinedStratum K Ω ℓ ι r s f :=
    ⟨ladicUnramifiedOrbitClass K Ω ℓ r a.val.val, ⟨a.val.val, rfl, a.val.property, a.property⟩⟩
  let right (a : A) : ladicRefinedStratum K Ω ℓ ι r' s f :=
    ⟨ladicUnramifiedOrbitClass K Ω ℓ r' (Φ a.val).val, ⟨(Φ a.val).val, rfl, (Φ a.val).property,
      (ladicTorsionNumber_apply K Ω ℓ ι Φ hΦ a.val).trans a.property⟩⟩
  have hleft : Function.Surjective left := by
    rintro ⟨o, ρ, hρ, hs, hf⟩
    exact ⟨⟨⟨ρ, hs⟩, hf⟩, Subtype.ext hρ⟩
  have hright : Function.Surjective right := by
    rintro ⟨o, ρ, hρ, hs, hf⟩
    let b : {b // LadicHasSwan K Ω ℓ ι b s} := ⟨ρ, hs⟩
    let a := Φ.symm b
    have hab : Φ a = b := Φ.apply_symm_apply b
    have ht := (ladicTorsionNumber_apply K Ω ℓ ι Φ hΦ a).symm
    rw [hab] at ht
    refine ⟨⟨a, ht.trans hf⟩, Subtype.ext ?_⟩
    change ladicUnramifiedOrbitClass K Ω ℓ r' (Φ a).val = o
    rw [hab]
    exact hρ
  have hFibers (a b : A) : left a = left b ↔ right a = right b := by
    rw [Subtype.ext_iff, Subtype.ext_iff]
    exact ladicOrbits_apply_eq_iff K Ω ℓ ι Φ hΦ a.val b.val
  refine Equiv.ofBijective (right ∘ Function.surjInv hleft) ⟨?_, ?_⟩
  · intro a b hab
    have heq := (hFibers _ _).mpr hab
    simpa only [Function.surjInv_eq] using heq
  · intro b
    obtain ⟨a, rfl⟩ := hright b
    exact ⟨left a, (hFibers _ _).mp (Function.surjInv_eq hleft _)⟩

end Langlands.Henniart.LocalNumerical

namespace Langlands.Henniart

open LocalNumerical
open scoped ValuativeRel

attribute [local instance] LocalField.Laurent.valuativeRel

/-- The ℓ-adic orbit comparison and twist-equivariant rank shift imply
Laumon's equal-characteristic count. -/
theorem laumonNumericalReduction_of_refinedOrbitEquiv :
    LaumonNumericalReductionStatement.{uK, uW} := by
  intro hOrbit hFourier k _ _ r s f X Ω hs _
  obtain ⟨ℓ, hlarger, hp⟩ := Nat.exists_infinite_primes (ringChar k + 1)
  let : Fact ℓ.Prime := ⟨hp⟩
  have hk : (ℓ : k) ≠ 0 := by
    intro h
    have he := (Nat.prime_dvd_prime_iff_eq (CharP.prime_ringChar k) hp).mp
      ((CharP.cast_eq_zero_iff k (ringChar k) ℓ).mp h)
    omega
  let ι := (GaloisRepresentation.padicAlgClComplexEquiv ℓ).toRingHom
  have hX : (ℓ : 𝓀[X]) ≠ 0 := by
    intro h
    apply hk
    simpa only [map_natCast, map_zero] using congrArg (LocalField.Laurent.residueEquiv k) h
  obtain ⟨e, _, he⟩ := hOrbit X Ω ℓ hX ι
  obtain ⟨Φ, hΦ⟩ := hFourier k ℓ hk ι r s hs
  have hcard := Set.encard_congr (ladicRefinedStratumEquiv X Ω ℓ ι Φ hΦ f)
  rw [← e.injective.encard_image, ← e.injective.encard_image, he, he] at hcard
  exact hcard

end Langlands.Henniart
