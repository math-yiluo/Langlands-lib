import Langlands.Correspondence.HenniartLadicStatement
import Langlands.Correspondence.Laumon.Slopes

/-!
# Laumon's `s(V)` and the transported Swan exponent

The interface of Laumon's numerical statement measures an irreducible ℓ-adic Galois class by
`Langlands.Henniart.LocalNumerical.LadicHasSwan`: restrict a representative to the Weil group,
extend scalars to `ℂ` along `ι : E →+* ℂ` and take the Swan exponent of the resulting complex
Weil class, defined from the Artin exponent at a finite inertia presentation by subtracting the
rank in `ℕ`. Laumon works with the slope-weighted Swan conductor `s(V)` of (2.1.2.5),
`ladicSwan`. `TransportedLadicSwanStatement` asserts that the two agree.
-/

noncomputable section

open ValuativeRel
open Langlands.Henniart.LocalNumerical (IrreducibleLadicClass LadicHasSwan ladicClassForget
  ladicUnramifiedCharacters ladicUnramifiedTwist)

namespace Langlands.Henniart.Laumon

/-- Bridge (b3) on the class side (Laumon (2.1.2.5)–(2.1.2.6); Serre IV §3 and VI §2;
Henniart 1988 §§4.1–4.2): for `ℓ` different from the residue characteristic, every
`ι : E →+* ℂ`, every irreducible ℓ-adic class `ρ` and every `s : ℕ`, `LadicHasSwan K Ω ℓ ι ρ s`
holds if and only if `s(V) = s` for some representative `V` of `ρ`, if and only if `s(V) = s` for
every representative; consequently `LadicHasSwan` does not depend on `ι` and is invariant under
the unramified twists `ladicUnramifiedTwist`. -/
def TransportedLadicSwanStatement.{uK, uΩ, uW} : Prop :=
  ∀ (K : Type uK) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (Ω : Type uΩ) [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]
    (ℓ : ℕ) [Fact ℓ.Prime], ((ℓ : ℕ) : 𝓀[K]) ≠ 0 →
    ∀ (ι : PadicAlgCl ℓ →+* ℂ) (k : ℕ)
      (ρ : IrreducibleLadicClass.{uK, uΩ, uW} K Ω ℓ k.succPNat) (s : ℕ),
      (LadicHasSwan K Ω ℓ ι ρ s ↔
        ∃ A : FiniteRepresentation.{0, uΩ, uW} (PadicAlgCl ℓ) (Ω ≃ₐ[K] Ω),
          FiniteRepresentation.classOf A = ladicClassForget K Ω ℓ ρ ∧
            ladicSwan (MonoidHom.id (Ω ≃ₐ[K] Ω)) A = s) ∧
      (LadicHasSwan K Ω ℓ ι ρ s ↔
        ∀ A : FiniteRepresentation.{0, uΩ, uW} (PadicAlgCl ℓ) (Ω ≃ₐ[K] Ω),
          FiniteRepresentation.classOf A = ladicClassForget K Ω ℓ ρ →
            ladicSwan (MonoidHom.id (Ω ≃ₐ[K] Ω)) A = s) ∧
      (∀ ι' : PadicAlgCl ℓ →+* ℂ, LadicHasSwan K Ω ℓ ι' ρ s ↔ LadicHasSwan K Ω ℓ ι ρ s) ∧
      (∀ χ : ladicUnramifiedCharacters K Ω ℓ,
        LadicHasSwan K Ω ℓ ι (ladicUnramifiedTwist K Ω ℓ k χ ρ) s ↔ LadicHasSwan K Ω ℓ ι ρ s)

end Langlands.Henniart.Laumon
