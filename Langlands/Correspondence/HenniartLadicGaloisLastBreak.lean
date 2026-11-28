import Langlands.Correspondence.HenniartLadicStatement
import Langlands.Correspondence.HenniartLocalWeilSwanBreak

/-! # The last upper break of an ℓ-adic Galois representation -/

noncomputable section

set_option autoImplicit false

namespace Langlands.Henniart.LocalNumerical

open FiniteRepresentation Weil.Local.SepClosed
open Ramification.Local VirtualRepresentation.LocalWeil.SepClosed.Ramification
open scoped ValuativeRel

universe uK uΩ uW

variable (K : Type uK) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  (Ω : Type uΩ) [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]
  (ℓ : ℕ) [Fact ℓ.Prime]

local notation "E" => PadicAlgCl ℓ
local notation "Γ" => Ω ≃ₐ[K] Ω
local notation "π" =>
  (@localProjection K _ _ _ _ Ω _ _ _ (IsSepClosure.sep_closed K))
local notation "iI" =>
  (@localInertiaInclusion K _ _ _ _ Ω _ _ _ (IsSepClosure.sep_closed K))

/-- The real `sInf` of the nonnegative upper indices at which the Galois
ramification subgroup acts trivially on this finite-dimensional algebraic
action. It is the usual last upper break for a nonempty threshold set and
is zero for an empty threshold set by `Real.sInf_empty`. -/
def ladicGaloisLastBreak (A : FiniteRepresentation.{0, uΩ, uW} E Γ) : ℝ :=
  sInf {r : ℝ | 0 ≤ r ∧
    ∀ g ∈ localAbsoluteUpperRamificationGroup K Ω r, A.representation g = 1}

private theorem scalarExtension_restrict_isTrivialAt_iff
    (A : FiniteRepresentation.{0, uΩ, uW} E Γ) (ι : E →+* ℂ)
    {r : ℝ} (hr : 0 ≤ r) :
    IsTrivialAt K Ω (ladicScalarExtension ℓ ι (restrict (π).toMonoidHom A)) r ↔
      ∀ g ∈ localAbsoluteUpperRamificationGroup K Ω r, A.representation g = 1 := by
  let : IsSepClosed Ω := IsSepClosure.sep_closed K
  let : Algebra E ℂ := ι.toAlgebra
  have hI : localAbsoluteUpperRamificationGroup K Ω r ≤
      LocalGalois.SepClosed.absoluteInertia K Ω :=
    (localAbsoluteUpperRamificationGroup_antitone K Ω hr).trans
      (le_of_eq (absoluteUpperInertia K Ω))
  have hbase : Function.Injective (Module.End.baseChangeHom E ℂ A) :=
    LinearMap.baseChangeHom_injective E A ℂ
  constructor
  · intro h g hg
    let w := iI ⟨g, hI hg⟩
    have hw : w ∈ upperGroup K Ω r := (mem_upperGroup K Ω r w).mpr hg
    apply hbase
    rw [map_one]
    exact h w hw
  · intro h w hw
    change Module.End.baseChangeHom E ℂ A (A.representation (π w)) = 1
    rw [h (π w) ((mem_upperGroup K Ω r w).mp hw), map_one]

/-- Restriction to the local Weil group and extension of coefficients preserve
the threshold set and hence its `sInf`, including the empty-set value. -/
theorem lastBreak_ladicScalarExtension_restrict
    (A : FiniteRepresentation.{0, uΩ, uW} E Γ) (ι : E →+* ℂ) :
    lastBreak K Ω (ladicScalarExtension ℓ ι (restrict (π).toMonoidHom A)) =
      ladicGaloisLastBreak K Ω ℓ A := by
  apply congrArg sInf
  ext r
  exact and_congr_right fun hr =>
    scalarExtension_restrict_isTrivialAt_iff K Ω ℓ A ι hr

/-- For a continuous irreducible Weil class identified with the transported
action, the natural Swan predicate is equality in `ℝ` with the rank times
the Galois last break of the ℓ-adic representative. -/
theorem hasWeilSwan_iff_ladicGaloisLastBreak
    (ι : E →+* ℂ) {k s : ℕ}
    (σ : IrreducibleWeilClass.{uK, uΩ, uW} K Ω k.succPNat)
    {A : FiniteRepresentation.{0, uΩ, uW} E Γ}
    (hσ : weilClassForget K Ω σ = ladicWeilTransport K Ω ℓ ι (classOf A)) :
    HasWeilSwan K Ω σ s ↔ (s : ℝ) = ((k + 1 : ℕ) : ℝ) * ladicGaloisLastBreak K Ω ℓ A := by
  refine (hasWeilSwan_iff_eq_weilSwanConductor K Ω σ).trans ?_
  rw [weilSwanConductor_eq_rank_mul_lastBreak K Ω hσ.symm,
    lastBreak_ladicScalarExtension_restrict]
  rfl

/-- Given class transport and `ℓ` distinct from the residue characteristic,
the natural Swan predicate is equality in `ℝ` with the rank times the
Galois last break of a representative. -/
theorem ladicHasSwan_iff_ladicGaloisLastBreak
    (hT : LadicWeilTransportStatement.{uK, uΩ, uW})
    (hℓ : (ℓ : 𝓀[K]) ≠ 0) (ι : E →+* ℂ) {k s : ℕ}
    (ρ : IrreducibleLadicClass.{uK, uΩ, uW} K Ω ℓ k.succPNat)
    {A : FiniteRepresentation.{0, uΩ, uW} E Γ}
    (hA : classOf A = ladicClassForget K Ω ℓ ρ) :
    LadicHasSwan K Ω ℓ ι ρ s ↔ (s : ℝ) = ((k + 1 : ℕ) : ℝ) * ladicGaloisLastBreak K Ω ℓ A := by
  constructor
  · rintro ⟨σ, hσ, hs⟩
    exact (hasWeilSwan_iff_ladicGaloisLastBreak K Ω ℓ ι σ (hA ▸ hσ)).mp hs
  · intro hs
    obtain ⟨σ, hσ⟩ := hT K Ω ℓ hℓ ι k ρ
    exact ⟨σ, hσ, (hasWeilSwan_iff_ladicGaloisLastBreak K Ω ℓ ι σ (hA ▸ hσ)).mpr hs⟩

/-- Given class transport and `ℓ` distinct from the residue characteristic,
changing the coefficient embedding into `ℂ` preserves the natural Swan
predicate. -/
theorem ladicHasSwan_iff_of_embeddings
    (hT : LadicWeilTransportStatement.{uK, uΩ, uW})
    (hℓ : (ℓ : 𝓀[K]) ≠ 0) (ι ι' : E →+* ℂ) {k s : ℕ}
    (ρ : IrreducibleLadicClass.{uK, uΩ, uW} K Ω ℓ k.succPNat) :
    LadicHasSwan K Ω ℓ ι ρ s ↔ LadicHasSwan K Ω ℓ ι' ρ s := by
  obtain ⟨A, hA⟩ := Quotient.exists_rep (ladicClassForget K Ω ℓ ρ)
  exact (ladicHasSwan_iff_ladicGaloisLastBreak K Ω ℓ hT hℓ ι ρ hA).trans
    (ladicHasSwan_iff_ladicGaloisLastBreak K Ω ℓ hT hℓ ι' ρ hA).symm

end Langlands.Henniart.LocalNumerical
