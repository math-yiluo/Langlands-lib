import Langlands.Correspondence.HenniartLocalNumerical
import Langlands.VirtualRepresentation.Weil.OrbitCarrierEquiv

/-!
# Changing the carrier universe in Weil orbit counts

Changing the carrier of a continuous irreducible Weil representation preserves
its Artin conductor and unramified-twist stabilizer. The resulting bijection of
refined orbit strata preserves the counts over nonarchimedean local fields.
-/

noncomputable section

set_option autoImplicit false

universe uK uΩ uV uW

namespace Langlands.Henniart.LocalNumerical

open FiniteRepresentation VirtualRepresentation
open Ramification.Local.SepClosed

variable (K : Type uK) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  (Ω : Type uΩ) [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]

local notation "W" =>
  (@Langlands.Weil.Local.SepClosed.localWeilGroup K _ _ _ _ Ω _ _ _ (IsSepClosure.sep_closed K))

local notation "degree" =>
  (@Langlands.Weil.Local.SepClosed.localDegree K _ _ _ _ Ω _ _ _ (IsSepClosure.sep_closed K))

/-- Change the carrier universe of the irreducible Weil classes of a fixed rank. -/
abbrev weilCarrierEquiv (n : ℕ+) :
    IrreducibleWeilClass.{uK, uΩ, uV} K Ω n ≃ IrreducibleWeilClass.{uK, uΩ, uW} K Ω n :=
  continuousIrreducibleCarrierEquiv W (n : ℕ)

private theorem hasArtinConductor_of_presentationEquiv {k a : ℕ}
    {σ : IrreducibleWeilClass.{uK, uΩ, uW} K Ω k.succPNat}
    {A : FiniteRepresentation.{0, uΩ, uV} ℂ W} {B : FiniteRepresentation.{0, uΩ, uW} ℂ W}
    (P : FiniteInertiaPresentation K Ω A)
    (hP : Function.Surjective (weilInertiaRestriction K Ω P.extension))
    (e : FiniteRepresentation.Equiv A B) (hB : classOf B = weilClassForget K Ω σ)
    (ha : P.artinConductor hP = (a : ℚ)) : HasArtinConductor K Ω σ a := by
  let T := finiteTopologicalData K Ω P.extension
  let π := (weilInertiaRestriction K Ω P.extension).toMonoidHom
  let eI : (localInertiaRepresentation K Ω A).Equiv (localInertiaRepresentation K Ω B) :=
    Representation.Equiv.mk e.toLinearEquiv fun i => e.isIntertwining' i
  let Q : FiniteInertiaPresentation K Ω B :=
    ⟨P.extension, Ramification.Local.kernel_le_of_equiv T K π P.kernel_le eI⟩
  refine ⟨B, Q, hP, hB, ?_⟩
  exact (Ramification.Local.artinConductorOfQuotient_equiv T K π hP
    P.kernel_le Q.kernel_le eI).symm.trans ha

/-- A change of carrier preserves and reflects the Artin conductor relation,
using the same finite inertia quotient on equivalent representatives. -/
theorem hasArtinConductor_weilCarrierEquiv_iff {k a : ℕ}
    (σ : IrreducibleWeilClass.{uK, uΩ, uV} K Ω k.succPNat) :
    HasArtinConductor K Ω (weilCarrierEquiv.{uK, uΩ, uV, uW} K Ω k.succPNat σ) a ↔
      HasArtinConductor K Ω σ a := by
  constructor
  · rintro ⟨B, P, hP, hB, ha⟩
    obtain ⟨A, hA⟩ := Quotient.exists_rep (weilClassForget K Ω σ)
    obtain ⟨e⟩ := (continuousIrreducibleCarrierEquiv_rep_iff σ A B hA.symm).mp hB.symm
    exact hasArtinConductor_of_presentationEquiv K Ω P hP e.symm hA ha
  · rintro ⟨A, P, hP, hA, ha⟩
    let B := transport.{uΩ, uV, uW} A
    let e := (coordinatesEquiv A).symm
    have hB := (continuousIrreducibleCarrierEquiv_rep_iff σ A B hA.symm).mpr ⟨e⟩
    exact hasArtinConductor_of_presentationEquiv K Ω P hP e hB.symm ha

/-- The same natural Swan exponent is witnessed after a change of carrier. -/
theorem hasWeilSwan_weilCarrierEquiv_iff {k s : ℕ}
    (σ : IrreducibleWeilClass.{uK, uΩ, uV} K Ω k.succPNat) :
    HasWeilSwan K Ω (weilCarrierEquiv.{uK, uΩ, uV, uW} K Ω k.succPNat σ) s ↔
      HasWeilSwan K Ω σ s := by
  simp only [HasWeilSwan, hasArtinConductor_weilCarrierEquiv_iff]

/-- The unramified characters fixing a Weil class fix its image under a change
of carrier, giving the same torsion number. -/
theorem weilTorsionNumber_weilCarrierEquiv {k : ℕ}
    (σ : IrreducibleWeilClass.{uK, uΩ, uV} K Ω k.succPNat) :
    weilTorsionNumber K Ω (weilCarrierEquiv.{uK, uΩ, uV, uW} K Ω k.succPNat σ) =
      weilTorsionNumber K Ω σ := by
  let e := weilCarrierEquiv.{uK, uΩ, uV, uW} K Ω k.succPNat
  have h : {z : ℂˣ | weilUnramifiedTwist K Ω k z (e σ) = e σ} =
      {z : ℂˣ | weilUnramifiedTwist K Ω k z σ = σ} := by
    ext z
    have hz : e (weilUnramifiedTwist K Ω k z σ) = weilUnramifiedTwist K Ω k z (e σ) :=
      continuousIrreducibleCarrierEquiv_twist _ σ
    change weilUnramifiedTwist K Ω k z (e σ) = e σ ↔ weilUnramifiedTwist K Ω k z σ = σ
    rw [← hz, Equiv.apply_eq_iff_eq]
  exact congrArg (fun S : Set ℂˣ => Nat.card S) h

/-- Changing the carrier universe gives a bijection of Weil twist orbits of
each rank, Swan exponent and torsion number. -/
def weilRefinedStratumCarrierEquiv (k s f : ℕ) :
    weilRefinedStratum.{uK, uΩ, uV} K Ω k s f ≃
      weilRefinedStratum.{uK, uΩ, uW} K Ω k s f := by
  let e := weilCarrierEquiv.{uK, uΩ, uV, uW} K Ω k.succPNat
  let E := Weil.unramifiedOrbitCarrierEquiv.{uΩ, uV, uW} degree
  refine Equiv.subtypeEquiv E fun c => ?_
  change c ∈ weilRefinedStratum K Ω k s f ↔ E c ∈ weilRefinedStratum K Ω k s f
  constructor
  · rintro ⟨σ, hσ, hs, hf⟩
    exact ⟨e σ, (Weil.unramifiedOrbitCarrierEquiv_class degree _ σ).symm.trans (congrArg E hσ),
      (hasWeilSwan_weilCarrierEquiv_iff K Ω σ).mpr hs,
      (weilTorsionNumber_weilCarrierEquiv K Ω σ).trans hf⟩
  · rintro ⟨τ, hτ, hs, hf⟩
    obtain ⟨σ, rfl⟩ := e.surjective τ
    exact ⟨σ, E.injective ((Weil.unramifiedOrbitCarrierEquiv_class degree _ σ).trans hτ),
      (hasWeilSwan_weilCarrierEquiv_iff K Ω σ).mp hs,
      (weilTorsionNumber_weilCarrierEquiv K Ω σ).symm.trans hf⟩

/-- Refined Weil orbit counts, as extended natural numbers, are independent of
the carrier universe. -/
theorem weilRefinedStratum_encard_carrierEquiv (k s f : ℕ) :
    (weilRefinedStratum.{uK, uΩ, uV} K Ω k s f).encard =
      (weilRefinedStratum.{uK, uΩ, uW} K Ω k s f).encard :=
  Set.encard_congr (weilRefinedStratumCarrierEquiv K Ω k s f)

theorem weilTwistIrreducibleCount_carrierEquiv (k s : ℕ) :
    weilTwistIrreducibleCount.{uK, uΩ, uV} K Ω k s =
      weilTwistIrreducibleCount.{uK, uΩ, uW} K Ω k s :=
  weilRefinedStratum_encard_carrierEquiv K Ω k s 1

theorem weilConductorCount_carrierEquiv (k j : ℕ) :
    weilConductorCount.{uK, uΩ, uV} K Ω k j = weilConductorCount.{uK, uΩ, uW} K Ω k j := by
  unfold weilConductorCount
  exact Finset.sum_congr rfl fun d _ =>
    Finset.sum_congr rfl fun s _ => weilTwistIrreducibleCount_carrierEquiv K Ω (d - 1) s

end Langlands.Henniart.LocalNumerical
