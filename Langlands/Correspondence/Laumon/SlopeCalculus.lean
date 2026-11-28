import Langlands.Correspondence.Laumon.SlopeIntegrality
import Langlands.Weil.Representation.Twist

/-!
# Slope calculus: irreducible modules, unramified twists, transport and Swan-one lines

Laumon 1987, (2.1.2.4)–(2.1.2.7), pp. 152–154, and Katz 1983, pp. 211–215: an irreducible
module has a single slope; twisting by a character trivial on wild inertia (in particular by an
unramified line) and transport along an isomorphism of local fields (in particular the coordinate
negation `t ↦ -t` of an end trait) preserve the slope decomposition; and twisting by a line of
Swan conductor one moves the slopes as in Laumon's Proposition (2.1.2.7).

A rank-one module `L` given by a character `χ` is `ladicCharacterLine χ`, and `V ⊗ L` is the
twist `FiniteRepresentation.twist χ V`, which keeps the carrier of `V`; so the slope summands of
`V` and of `V ⊗ L` are subspaces of the same vector space.
-/

noncomputable section

open ValuativeRel
open Langlands.Ramification.Local (localAbsoluteUpperRamificationGroup localWildInertia)
open Langlands.Henniart.LocalNumerical (IsLadicContinuous IsLadicDefinedOverFiniteExtension)
open Langlands.LocalGalois.SepClosed (absoluteInertia)

namespace Langlands.Henniart.Laumon

/-- The rank-one representation of `H` on `E = PadicAlgCl ℓ` given by a character `χ`: the twist
of the trivial representation on `E` by `χ`. -/
abbrev ladicCharacterLine {H : Type*} [Group H] {ℓ : ℕ} [Fact ℓ.Prime]
    (χ : H →* (PadicAlgCl ℓ)ˣ) : FiniteRepresentation.{0, _, 0} (PadicAlgCl ℓ) H :=
  FiniteRepresentation.twist χ
    (FiniteRepresentation.of (1 : Representation (PadicAlgCl ℓ) H (PadicAlgCl ℓ)))

/-- Laumon (2.1.2.4)–(2.1.2.5): for `ℓ` different from the residue characteristic, an irreducible
continuous ℓ-adic representation with a finite model of rank `r` (of a group `H` embedded in the
Galois group with image containing wild inertia) has the single slope `s(V)/r`, and its
slope-`s(V)/r` summand is the whole space. -/
def IrreducibleSingleSlopeStatement.{u₁, u₂, u₃, u₄} : Prop :=
  ∀ (K : Type u₁) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (Ω : Type u₂) [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]
    (ℓ : ℕ) [Fact ℓ.Prime], ((ℓ : ℕ) : 𝓀[K]) ≠ 0 →
    ∀ (H : Type u₃) [Group H] [TopologicalSpace H] (f : H →* (Ω ≃ₐ[K] Ω)),
      Topology.IsEmbedding f → localWildInertia K Ω ≤ f.range →
      ∀ A : FiniteRepresentation.{0, u₃, u₄} (PadicAlgCl ℓ) H,
        IsLadicContinuous ℓ A → IsLadicDefinedOverFiniteExtension ℓ A →
        Representation.IsIrreducible A.representation →
          slopeSupport f A = {ladicSwan f A / (A.rank : ℝ)} ∧
          slopeSummand f A (ladicSwan f A / (A.rank : ℝ)) = ⊤

/-- Invariance of the slope decomposition (Laumon (2.1.2.4)–(2.1.2.5); Serre IV §3):

* twisting by a character of `H` trivial on wild inertia, in particular by a line trivial on
  inertia, leaves every slope summand unchanged, hence also the slopes and `s(V)`;
* transport of structure: if `τ : Ω ≃+* Ω'` restricts to a valuation-preserving isomorphism
  `τ₀ : K ≃+* K'` and `c` is the induced conjugation `σ ↦ τ σ τ⁻¹` of Galois groups, then the
  slope summands of a representation, computed over `K'` through `f'` or over `K` through
  `c⁻¹ ∘ f'`, are equal. The coordinate negation `t ↦ -t` of an end trait completed to `k((t))`
  is the case `K = K'`, `τ₀` the negation and `τ` any extension of it to `Ω`. -/
def UnramifiedTwistSwanStatement.{u₁, u₂, u₁', u₂', u₃, u₄} : Prop :=
  (∀ (K : Type u₁) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (Ω : Type u₂) [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]
    (ℓ : ℕ) [Fact ℓ.Prime]
    (H : Type u₃) [Group H] (f : H →* (Ω ≃ₐ[K] Ω))
    (A : FiniteRepresentation.{0, u₃, u₄} (PadicAlgCl ℓ) H) (χ : H →* (PadicAlgCl ℓ)ˣ),
      (∀ h : H, f h ∈ localWildInertia K Ω → χ h = 1) →
        (∀ μ : ℝ, slopeSummand f (FiniteRepresentation.twist χ A) μ = slopeSummand f A μ) ∧
        slopeSupport f (FiniteRepresentation.twist χ A) = slopeSupport f A ∧
        ladicSwan f (FiniteRepresentation.twist χ A) = ladicSwan f A) ∧
  (∀ (K : Type u₁) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (Ω : Type u₂) [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]
    (K' : Type u₁') [Field K'] [ValuativeRel K'] [TopologicalSpace K']
    [IsNonarchimedeanLocalField K']
    (Ω' : Type u₂') [Field Ω'] [Algebra K' Ω'] [IsSepClosure K' Ω']
    (τ₀ : K ≃+* K') (τ : Ω ≃+* Ω'),
      (∀ a b : K, τ₀ a ≤ᵥ τ₀ b ↔ a ≤ᵥ b) →
      (∀ x : K, τ (algebraMap K Ω x) = algebraMap K' Ω' (τ₀ x)) →
      ∀ c : (Ω ≃ₐ[K] Ω) ≃* (Ω' ≃ₐ[K'] Ω'), (∀ (σ : Ω ≃ₐ[K] Ω) (x : Ω), c σ (τ x) = τ (σ x)) →
      ∀ (ℓ : ℕ) [Fact ℓ.Prime] (H : Type u₃) [Group H] (f' : H →* (Ω' ≃ₐ[K'] Ω'))
        (A : FiniteRepresentation.{0, u₃, u₄} (PadicAlgCl ℓ) H) (μ : ℝ),
        slopeSummand (c.symm.toMonoidHom.comp f') A μ = slopeSummand f' A μ)

/-- Laumon, Proposition (2.1.2.7), and the slope behaviour in its proof: for `ℓ` different from
the residue characteristic, a group `H` embedded in the Galois group with image containing
inertia, a line `L` given by a character `χ` of `H` with Swan conductor `1`, and a continuous
ℓ-adic representation `V` with a finite model, write `B = V ⊗ L` (the twist by `χ`) and `V_μ`,
`B_μ` for the slope summands. Then

* `V_μ ⊆ B_1` for `μ < 1`, `B_μ = V_μ` for `μ > 1`, and `V_1 ⊆ ⊕_{μ ≤ 1} B_μ`, with
  `B_μ ⊆ V_1` for `μ < 1`;
* (i) `s(V ⊗ L) = r(V_{[0,1[}) + s(V_1 ⊗ L) + s(V_{]1,∞[})`, where `s(V_1 ⊗ L)` is computed from
  the slope decomposition of `V_1 ⊗ L`, whose slope-`μ` part is `B_μ ∩ V_1`;
* (ii) `s(V_1 ⊗ L) ≤ r(V_1)`, and if `V_1 ≠ 0`, equality holds if and only if
  `(V_1 ⊗ L)^{G^{1-ε}} = 0` for some `ε ∈ [0, 1/r(V_1)[`. -/
def SwanOneTensorStatement.{u₁, u₂, u₃, u₄} : Prop :=
  ∀ (K : Type u₁) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (Ω : Type u₂) [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]
    (ℓ : ℕ) [Fact ℓ.Prime], ((ℓ : ℕ) : 𝓀[K]) ≠ 0 →
    ∀ (H : Type u₃) [Group H] [TopologicalSpace H] (f : H →* (Ω ≃ₐ[K] Ω)),
      Topology.IsEmbedding f → absoluteInertia K Ω ≤ f.range →
      ∀ χ : H →* (PadicAlgCl ℓ)ˣ,
        IsLadicContinuous ℓ (ladicCharacterLine χ) →
        IsLadicDefinedOverFiniteExtension ℓ (ladicCharacterLine χ) →
        ladicSwan f (ladicCharacterLine χ) = 1 →
      ∀ A : FiniteRepresentation.{0, u₃, u₄} (PadicAlgCl ℓ) H,
        IsLadicContinuous ℓ A → IsLadicDefinedOverFiniteExtension ℓ A →
        let B := FiniteRepresentation.twist χ A
        let r₁ : ℝ := Module.finrank (PadicAlgCl ℓ) (slopeSummand f A 1)
        let s₁ : ℝ := ∑ᶠ μ : ℝ,
          μ * (Module.finrank (PadicAlgCl ℓ) ↥(slopeSummand f B μ ⊓ slopeSummand f A 1) : ℝ)
        (∀ μ : ℝ, μ < 1 → slopeSummand f A μ ≤ slopeSummand f B 1) ∧
        (∀ μ : ℝ, 1 < μ → slopeSummand f B μ = slopeSummand f A μ) ∧
        (∀ μ : ℝ, μ < 1 → slopeSummand f B μ ≤ slopeSummand f A 1) ∧
        slopeSummand f A 1 ≤ ⨆ (μ : ℝ) (_ : μ ≤ 1), slopeSummand f B μ ∧
        ladicSwan f B =
          (∑ᶠ (μ : ℝ) (_ : μ < 1), (Module.finrank (PadicAlgCl ℓ) (slopeSummand f A μ) : ℝ)) +
            s₁ + ∑ᶠ (μ : ℝ) (_ : 1 < μ),
              μ * (Module.finrank (PadicAlgCl ℓ) (slopeSummand f A μ) : ℝ) ∧
        s₁ ≤ r₁ ∧
        (slopeSummand f A 1 ≠ ⊥ →
          (s₁ = r₁ ↔ ∃ ε : ℝ, 0 ≤ ε ∧ ε < 1 / r₁ ∧
            slopeSummand f A 1 ⊓ fixedVectors B.representation
              ((localAbsoluteUpperRamificationGroup K Ω (1 - ε)).comap f) = ⊥))

end Langlands.Henniart.Laumon
