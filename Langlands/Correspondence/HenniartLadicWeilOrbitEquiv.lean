import Langlands.Correspondence.HenniartLadicFiniteImageModel
import Langlands.Correspondence.HenniartLadicStatement
import Langlands.Correspondence.HenniartLadicWeilClassTwist

/-! # Unramified-twist orbit comparison for ℓ-adic Galois and complex Weil classes -/

noncomputable section

set_option autoImplicit false

universe uK uΩ uW

namespace Langlands.Henniart.LocalNumerical

open FiniteRepresentation VirtualRepresentation
open Weil.Local.SepClosed

variable (K : Type uK) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (Ω : Type uΩ) [Field Ω] [Algebra K Ω] [IsSepClosure K Ω] [IsSepClosed Ω]
    (ℓ : ℕ) [Fact ℓ.Prime] (ι : PadicAlgCl ℓ →+* ℂ)

local notation "W" => localWeilGroup K Ω
local notation "d" => localDegree K Ω

private abbrev LadicRankClasses :=
  Σ k : ℕ, IrreducibleLadicClass.{uK, uΩ, uW} K Ω ℓ k.succPNat

omit [IsSepClosed Ω] in
private theorem weilClassForget_inj {k : ℕ}
    {σ σ' : IrreducibleWeilClass.{uK, uΩ, uW} K Ω k.succPNat}
    (h : weilClassForget K Ω σ = weilClassForget K Ω σ') : σ = σ' :=
  Subtype.ext (forgetPropertyClass_injective _ h)

private theorem weilClassForget_twist (k : ℕ) (z : ℂˣ)
    (σ : IrreducibleWeilClass.{uK, uΩ, uW} K Ω k.succPNat) :
    weilClassForget K Ω (weilUnramifiedTwist K Ω k z σ) =
      twistClass (localUnramifiedCharacter K Ω z).toMonoidHom (weilClassForget K Ω σ) :=
  forget_continuousIrreducibleTwistEquiv (localUnramifiedCharacter K Ω z) (k + 1) σ

private theorem matches_unramifiedTwist {k : ℕ}
    {ρ : IrreducibleLadicClass.{uK, uΩ, uW} K Ω ℓ k.succPNat}
    {σ : IrreducibleWeilClass.{uK, uΩ, uW} K Ω k.succPNat}
    (h : weilClassForget K Ω σ = ladicWeilTransport K Ω ℓ ι (ladicClassForget K Ω ℓ ρ))
    (χ : ladicUnramifiedCharacters K Ω ℓ) :
    weilClassForget K Ω (weilUnramifiedTwist K Ω k (ladicWeilTwistParameter K Ω ℓ ι χ) σ) =
      ladicWeilTransport K Ω ℓ ι (ladicClassForget K Ω ℓ (ladicUnramifiedTwist K Ω ℓ k χ ρ)) := by
  rw [weilClassForget_twist, ladicWeilTransport_unramifiedTwist, h]

/-- The unramified-twist stabilizers of matching ℓ-adic and complex Weil classes
have the same cardinality. -/
theorem ladicTorsionNumber_eq_weilTorsionNumber {k : ℕ}
    {ρ : IrreducibleLadicClass.{uK, uΩ, uW} K Ω ℓ k.succPNat}
    {σ : IrreducibleWeilClass.{uK, uΩ, uW} K Ω k.succPNat}
    (h : weilClassForget K Ω σ = ladicWeilTransport K Ω ℓ ι (ladicClassForget K Ω ℓ ρ)) :
    ladicTorsionNumber K Ω ℓ ρ = weilTorsionNumber K Ω σ := by
  let f : {χ : ladicUnramifiedCharacters K Ω ℓ // ladicUnramifiedTwist K Ω ℓ k χ ρ = ρ} →
      {z : ℂˣ // weilUnramifiedTwist K Ω k z σ = σ} := fun χ =>
    ⟨ladicWeilTwistParameter K Ω ℓ ι χ.val, by
      have ht := matches_unramifiedTwist K Ω ℓ ι h χ.val
      rw [χ.property] at ht
      exact weilClassForget_inj K Ω (ht.trans h.symm)⟩
  have hinj : Function.Injective f := fun _ _ heq =>
    Subtype.ext (ladicWeilTwistParameter_injective K Ω ℓ ι (congrArg Subtype.val heq))
  have hsurj : Function.Surjective f := by
    rintro ⟨z, hz⟩
    have ht := congrArg (weilClassForget K Ω) hz
    rw [weilClassForget_twist, h] at ht
    obtain ⟨χ, hχ, hρ⟩ := exists_ladicUnramified_of_transport_twist K Ω ℓ ι ρ ρ z ht.symm
    exact ⟨⟨χ, hρ.symm⟩, Subtype.ext hχ⟩
  exact Nat.card_congr (Equiv.ofBijective f ⟨hinj, hsurj⟩)

variable (hT : ∀ (k : ℕ) (ρ : IrreducibleLadicClass.{uK, uΩ, uW} K Ω ℓ k.succPNat),
    ∃ σ : IrreducibleWeilClass.{uK, uΩ, uW} K Ω k.succPNat,
      weilClassForget K Ω σ = ladicWeilTransport K Ω ℓ ι (ladicClassForget K Ω ℓ ρ))

private def transportBasis (a : LadicRankClasses.{uK, uΩ, uW} K Ω ℓ) :
    Weil.IrreducibleBasis.{uΩ, uW} W :=
  ⟨a.1.succPNat, (hT a.1 a.2).choose⟩

private theorem transportBasis_eq {k : ℕ}
    {ρ : IrreducibleLadicClass.{uK, uΩ, uW} K Ω ℓ k.succPNat}
    {σ : IrreducibleWeilClass.{uK, uΩ, uW} K Ω k.succPNat}
    (h : weilClassForget K Ω σ = ladicWeilTransport K Ω ℓ ι (ladicClassForget K Ω ℓ ρ)) :
    transportBasis K Ω ℓ ι hT ⟨k, ρ⟩ = ⟨k.succPNat, σ⟩ :=
  congrArg (Sigma.mk k.succPNat) (weilClassForget_inj K Ω ((hT k ρ).choose_spec.trans h.symm))

private def ladicWeilOrbitMap :
    LadicUnramifiedOrbitClasses.{uK, uΩ, uW} K Ω ℓ → Weil.UnramifiedOrbitClasses.{uΩ, uW} d := by
  let := ladicUnramifiedTwistAction.{uK, uΩ, uW} K Ω ℓ
  refine Quotient.lift (fun a : LadicRankClasses.{uK, uΩ, uW} K Ω ℓ =>
    Weil.unramifiedOrbitClass d (transportBasis K Ω ℓ ι hT a))
    (fun a b h => ?_)
  obtain ⟨χ, hχ⟩ := MulAction.mem_orbit_iff.mp h
  rw [← hχ]
  obtain ⟨k, ρ⟩ := b
  have ht := matches_unramifiedTwist K Ω ℓ ι (hT k ρ).choose_spec χ
  change Weil.unramifiedOrbitClass d
    (transportBasis K Ω ℓ ι hT ⟨k, ladicUnramifiedTwist K Ω ℓ k χ ρ⟩) = _
  rw [transportBasis_eq K Ω ℓ ι hT ht]
  exact unramifiedOrbitClass_twist K Ω (ladicWeilTwistParameter K Ω ℓ ι χ)
    (transportBasis K Ω ℓ ι hT ⟨k, ρ⟩)

private theorem ladicWeilOrbitMap_injective : Function.Injective (ladicWeilOrbitMap K Ω ℓ ι hT) := by
  let := ladicUnramifiedTwistAction.{uK, uΩ, uW} K Ω ℓ
  intro a b h
  revert h
  refine Quotient.inductionOn₂ a b ?_
  rintro ⟨k, ρ⟩ ⟨l, τ⟩ h
  change Weil.unramifiedOrbitClass d (transportBasis K Ω ℓ ι hT ⟨k, ρ⟩) =
    Weil.unramifiedOrbitClass d (transportBasis K Ω ℓ ι hT ⟨l, τ⟩) at h
  obtain ⟨z, hz⟩ := (Weil.unramifiedOrbitClass_eq_iff d _ _).mp h
  have hr := congrArg (fun b : Weil.IrreducibleBasis.{uΩ, uW} W => (b.1 : ℕ)) hz
  change l + 1 = k + 1 at hr
  have hl : l = k := Nat.succ.inj hr
  subst l
  have ht := congrArg (weilClassForget K Ω) (irreducibleBasis_mk_injective hz).symm
  change weilClassForget K Ω (hT k ρ).choose =
    weilClassForget K Ω (weilUnramifiedTwist K Ω k z (hT k τ).choose) at ht
  rw [weilClassForget_twist, (hT k ρ).choose_spec, (hT k τ).choose_spec] at ht
  obtain ⟨χ, _, hρ⟩ := exists_ladicUnramified_of_transport_twist K Ω ℓ ι τ ρ z ht
  exact Quotient.sound (MulAction.mem_orbit_iff.mpr ⟨χ, congrArg (Sigma.mk k) hρ.symm⟩)

private theorem ladicWeilOrbitMap_surjective : Function.Surjective (ladicWeilOrbitMap K Ω ℓ ι hT) := by
  intro b
  refine Quotient.inductionOn b ?_
  rintro ⟨n, σ⟩
  obtain ⟨k, rfl⟩ : ∃ k : ℕ, k.succPNat = n := ⟨n.natPred, PNat.succPNat_natPred n⟩
  obtain ⟨z, ρ, hρ⟩ := exists_unramifiedTwist_ladicWeilTransport K Ω ℓ ι k σ
  refine ⟨ladicUnramifiedOrbitClass K Ω ℓ k ρ, ?_⟩
  change Weil.unramifiedOrbitClass d (transportBasis K Ω ℓ ι hT ⟨k, ρ⟩) = _
  rw [transportBasis_eq K Ω ℓ ι hT hρ]
  exact unramifiedOrbitClass_twist K Ω z ⟨k.succPNat, σ⟩

/-- Continuous irreducible ℓ-adic Galois classes and complex Weil classes
have equivalent unramified-twist orbit spaces when each transport is continuous
and irreducible. -/
def ladicWeilOrbitEquiv :
    LadicUnramifiedOrbitClasses.{uK, uΩ, uW} K Ω ℓ ≃ Weil.UnramifiedOrbitClasses.{uΩ, uW} d :=
  Equiv.ofBijective (ladicWeilOrbitMap K Ω ℓ ι hT)
    ⟨ladicWeilOrbitMap_injective K Ω ℓ ι hT, ladicWeilOrbitMap_surjective K Ω ℓ ι hT⟩

theorem ladicWeilOrbitEquiv_apply {k : ℕ}
    {ρ : IrreducibleLadicClass.{uK, uΩ, uW} K Ω ℓ k.succPNat}
    {σ : IrreducibleWeilClass.{uK, uΩ, uW} K Ω k.succPNat}
    (h : weilClassForget K Ω σ = ladicWeilTransport K Ω ℓ ι (ladicClassForget K Ω ℓ ρ)) :
    ladicWeilOrbitEquiv K Ω ℓ ι hT (ladicUnramifiedOrbitClass K Ω ℓ k ρ) =
      Weil.unramifiedOrbitClass d ⟨k.succPNat, σ⟩ :=
  congrArg (Weil.unramifiedOrbitClass d) (transportBasis_eq K Ω ℓ ι hT h)

/-- The orbit equivalence carries each refined Swan and torsion stratum to
its complex Weil counterpart. -/
theorem ladicWeilOrbitEquiv_image_refinedStratum (k s f : ℕ) :
    ladicWeilOrbitEquiv K Ω ℓ ι hT '' ladicRefinedStratum K Ω ℓ ι k s f =
      weilRefinedStratum.{uK, uΩ, uW} K Ω k s f := by
  ext b
  constructor
  · rintro ⟨_, ⟨ρ, rfl, ⟨σ, hσ, hs⟩, hf⟩, rfl⟩
    exact ⟨σ, (ladicWeilOrbitEquiv_apply K Ω ℓ ι hT hσ).symm, hs,
      (ladicTorsionNumber_eq_weilTorsionNumber K Ω ℓ ι hσ).symm.trans hf⟩
  · rintro ⟨σ, rfl, hs, hf⟩
    obtain ⟨z, ρ, hρ⟩ := exists_unramifiedTwist_ladicWeilTransport K Ω ℓ ι k σ
    refine ⟨ladicUnramifiedOrbitClass K Ω ℓ k ρ,
      ⟨ρ, rfl, ⟨_, hρ, (hasWeilSwan_weilUnramifiedTwist_iff K Ω σ z s).mpr hs⟩, ?_⟩, ?_⟩
    · rw [ladicTorsionNumber_eq_weilTorsionNumber K Ω ℓ ι hρ,
        weilTorsionNumber_weilUnramifiedTwist, hf]
    · rw [ladicWeilOrbitEquiv_apply K Ω ℓ ι hT hρ]
      exact unramifiedOrbitClass_twist K Ω z ⟨k.succPNat, σ⟩

end Langlands.Henniart.LocalNumerical

namespace Langlands.Henniart

open LocalNumerical

/-- The class-level transport theorem gives the comparison on all refined
unramified-twist strata. -/
theorem ladicWeilOrbitComparison_of_transport
    (hT : LadicWeilTransportStatement.{uK, uΩ, uW}) :
    LadicWeilOrbitComparisonStatement.{uK, uΩ, uW} := by
  intro K _ _ _ _ Ω _ _ _ ℓ _ hℓ ι
  let := IsSepClosure.sep_closed K (K := Ω)
  exact ⟨ladicWeilOrbitEquiv K Ω ℓ ι (hT K Ω ℓ hℓ ι),
    fun _ _ _ h => ladicWeilOrbitEquiv_apply K Ω ℓ ι (hT K Ω ℓ hℓ ι) h,
    ladicWeilOrbitEquiv_image_refinedStratum K Ω ℓ ι (hT K Ω ℓ hℓ ι)⟩

end Langlands.Henniart
