import Langlands.Correspondence.HenniartLadicClasses
import Langlands.Correspondence.HenniartLocalNumerical
import Langlands.LocalField.LaurentSeries

/-! # ℓ-adic Swan strata, Weil transport and Laumon's twist bijection -/

noncomputable section

namespace Langlands.Henniart.LocalNumerical

universe uK uΩ uW

variable (K : Type uK) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (Ω : Type uΩ) [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]
    (ℓ : ℕ) [Fact ℓ.Prime] (ι : PadicAlgCl ℓ →+* ℂ)

/-- The transported ℓ-adic class has Swan exponent `s` as a continuous irreducible Weil class. -/
def LadicHasSwan {k : ℕ} (ρ : IrreducibleLadicClass.{uK, uΩ, uW} K Ω ℓ k.succPNat)
    (s : ℕ) : Prop :=
  ∃ σ : IrreducibleWeilClass.{uK, uΩ, uW} K Ω k.succPNat,
    weilClassForget K Ω σ = ladicWeilTransport K Ω ℓ ι (ladicClassForget K Ω ℓ ρ) ∧
      HasWeilSwan K Ω σ s

/-- Unramified-twist orbits containing a class of rank `k + 1`, Swan exponent `s`
and torsion number `f`. -/
def ladicRefinedStratum (k s f : ℕ) : Set (LadicUnramifiedOrbitClasses.{uK, uΩ, uW} K Ω ℓ) :=
  {c | ∃ ρ : IrreducibleLadicClass.{uK, uΩ, uW} K Ω ℓ k.succPNat,
    ladicUnramifiedOrbitClass K Ω ℓ k ρ = c ∧
      LadicHasSwan K Ω ℓ ι ρ s ∧ ladicTorsionNumber K Ω ℓ ρ = f}

end Langlands.Henniart.LocalNumerical

namespace Langlands.Henniart

open LocalNumerical ValuativeRel
open Langlands.LocalGalois.SepClosed (absoluteInertia)
open Langlands.VirtualRepresentation
open Langlands.Weil.Local.SepClosed (localDegree)

/-- An irreducible ℓ-adic Galois representation over a finite coefficient extension
has finite inertia image when `ℓ` differs from the residue characteristic. -/
def LadicFiniteInertiaStatement.{uK, uΩ, uW} : Prop :=
  ∀ (K : Type uK) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (Ω : Type uΩ) [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]
    (ℓ : ℕ) [Fact ℓ.Prime], ((ℓ : ℕ) : 𝓀[K]) ≠ 0 →
    ∀ (_ι : PadicAlgCl ℓ →+* ℂ)
      (A : FiniteRepresentation.{0, uΩ, uW} (PadicAlgCl ℓ) (Ω ≃ₐ[K] Ω)),
      IsLadicContinuous ℓ A → IsLadicDefinedOverFiniteExtension ℓ A →
        Representation.IsIrreducible A.representation →
          (A.representation '' (absoluteInertia K Ω : Set (Ω ≃ₐ[K] Ω))).Finite

/-- Restriction and scalar extension transport an irreducible ℓ-adic Galois class to a
continuous irreducible complex Weil class of the same rank when `ℓ` differs from the residue
characteristic. -/
def LadicWeilTransportStatement.{uK, uΩ, uW} : Prop :=
  ∀ (K : Type uK) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (Ω : Type uΩ) [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]
    (ℓ : ℕ) [Fact ℓ.Prime], ((ℓ : ℕ) : 𝓀[K]) ≠ 0 →
    ∀ (ι : PadicAlgCl ℓ →+* ℂ) (k : ℕ)
      (ρ : IrreducibleLadicClass.{uK, uΩ, uW} K Ω ℓ k.succPNat),
      ∃ σ : IrreducibleWeilClass.{uK, uΩ, uW} K Ω k.succPNat,
        weilClassForget K Ω σ = ladicWeilTransport K Ω ℓ ι (ladicClassForget K Ω ℓ ρ)

/-- Transport induces an equivalence of unramified-twist orbit spaces that identifies
all refined strata when `ℓ` differs from the residue characteristic. -/
def LadicWeilOrbitComparisonStatement.{uK, uΩ, uW} : Prop :=
  ∀ (K : Type uK) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (Ω : Type uΩ) [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]
    (ℓ : ℕ) [Fact ℓ.Prime], ((ℓ : ℕ) : 𝓀[K]) ≠ 0 →
    ∀ (ι : PadicAlgCl ℓ →+* ℂ),
      letI := IsSepClosure.sep_closed K (K := Ω)
      ∃ e : LadicUnramifiedOrbitClasses.{uK, uΩ, uW} K Ω ℓ ≃
          Weil.UnramifiedOrbitClasses.{uΩ, uW} (localDegree K Ω),
        (∀ (k : ℕ) (ρ : IrreducibleLadicClass.{uK, uΩ, uW} K Ω ℓ k.succPNat)
          (σ : IrreducibleWeilClass.{uK, uΩ, uW} K Ω k.succPNat),
          weilClassForget K Ω σ = ladicWeilTransport K Ω ℓ ι (ladicClassForget K Ω ℓ ρ) →
            e (ladicUnramifiedOrbitClass K Ω ℓ k ρ) =
              Weil.unramifiedOrbitClass (localDegree K Ω) ⟨k.succPNat, σ⟩) ∧
        ∀ k s f : ℕ, e '' ladicRefinedStratum K Ω ℓ ι k s f =
          weilRefinedStratum K Ω k s f

/-- Laumon's rank shift at fixed positive Swan exponent over a finite field's Laurent
series field, equivariant for the continuous unramified ℓ-adic Galois characters. -/
def LaumonLadicTwistBijectionStatement.{uK, uW} : Prop :=
  ∀ (𝓀 : Type uK) [Field 𝓀] [Finite 𝓀] (ℓ : ℕ) [Fact ℓ.Prime], (ℓ : 𝓀) ≠ 0 →
    ∀ (ι : PadicAlgCl ℓ →+* ℂ) (k s : ℕ), 1 ≤ s →
      let X := LaurentSeries 𝓀
      letI : ValuativeRel X := LocalField.Laurent.valuativeRel 𝓀
      let Ω := SeparableClosure X
      let A := {ρ : IrreducibleLadicClass.{uK, uK, uW} X Ω ℓ k.succPNat //
        LadicHasSwan X Ω ℓ ι ρ s}
      let B := {ρ' : IrreducibleLadicClass.{uK, uK, uW} X Ω ℓ (k + s).succPNat //
        LadicHasSwan X Ω ℓ ι ρ' s}
      ∃ Φ : A ≃ B, ∀ (χ : ladicUnramifiedCharacters X Ω ℓ) (ρ : A),
        ∃ h : LadicHasSwan X Ω ℓ ι (ladicUnramifiedTwist X Ω ℓ k χ ρ.1) s,
          (Φ ⟨ladicUnramifiedTwist X Ω ℓ k χ ρ.1, h⟩).1 =
            ladicUnramifiedTwist X Ω ℓ (k + s) χ (Φ ρ).1

end Langlands.Henniart
