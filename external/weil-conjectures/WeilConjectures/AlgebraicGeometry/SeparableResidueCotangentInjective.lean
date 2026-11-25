/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.Ideal.Cotangent
public import Mathlib.RingTheory.Kaehler.Basic
public import WeilConjectures.FieldTheory.SeparableExtension
import Mathlib.RingTheory.Smooth.Field

/-!
# Separable residue field: the cotangent space injects into the differentials

Source: Stacks Project, Algebra, Lemma Tag 00TU (blueprint:
lem-weil-pbc-separable-residue-cotangent-injective).
-/

@[expose] public section

universe u v

open scoped TensorProduct

namespace Algebra

/-- For a Noetherian local `k`-algebra with residue field finitely generated as a field
and separable over `k`,
the cotangent space injects into the base-changed Kähler differentials.
Source: Stacks Project, Algebra, Lemma Tag 00TU, lines 38687, 38702--38737
(blueprint: lem-weil-pbc-separable-residue-cotangent-injective).

The tensor factors are reversed relative to the source: tensor symmetry takes
`1 ⊗ d a` to `d a ⊗ 1`, so injectivity is unchanged.

Proof:
1. Put `A = R/m²` and `n = m/m²`, so `n² = 0` and `A/n = κ`. Use the computation of
   Kähler differentials modulo a power of an ideal (Tag 02HQ, exponent one)
   to identify `Ω[R/k] ⊗[R] κ` with `Ω[A/k] ⊗[A] κ`, preserving `d a ⊗ 1`.
   The map from `m/m²` to `n` is the identity on residue classes; reduce to `A`.
2. Choose a separating transcendence basis `x̄₁, …, x̄ᵣ` of `κ/k`, using
   `def-weil-pbc-separable-field-extension` and `def-weil-pbc-transcendence-basis`.
   Finite field generation makes this basis finite and makes `κ` finite over
   `F = k(x̄₁, …, x̄ᵣ)`. By `def-weil-pbc-separable-algebraic-extension` and
   `lem-weil-pbc-finite-separable-extension-primitive-element` (Tag 030N), write
   `κ = F(ȳ)` with separable minimal polynomial `P`, hence `P'(ȳ) ≠ 0`.
3. Lift the basis elements to `A`. By algebraic independence, nonzero polynomials
   over `k` have nonzero residue, hence evaluate to units in this local ring.
   Evaluation therefore extends to a map `φ : F → A` splitting the residue map on `F`.
4. Lift `ȳ` to `y₀`. Then `c = P^φ(y₀)` is in `n`, while `u = (P')^φ(y₀)` is a unit.
   Set `δ = -u⁻¹c` and `y = y₀ + δ`. Since `n² = 0`, expansion gives
   `P^φ(y) = c + uδ = 0`. Evaluation yields `F[T]/(P) → A`, hence a `k`-algebra
   section `σ : κ → A`, since its residue fixes `F` and sends `ȳ` to itself.
5. Apply `lem-weil-pbc-square-zero-section-conormal-retraction` (Tag 02HP) to
   `A → κ` with kernel `n` and section `σ`. Its conormal map has a left inverse,
   so is injective. Tensor symmetry and the differential comparison in step 1
   identify this with the asserted map for `R`. -/
theorem separable_residue_cotangent_injective
    (k : Type u) (R : Type v) [Field k] [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] [Algebra k R]
    (hfg : (⊤ : IntermediateField k (IsLocalRing.ResidueField R)).FG)
    (hsep : Algebra.IsSeparableExtension k (IsLocalRing.ResidueField R)) :
    Function.Injective
      ((KaehlerDifferential.kerCotangentToTensor k R (IsLocalRing.ResidueField R)).comp
        (Ideal.Cotangent.equivOfEq (IsLocalRing.maximalIdeal R)
          (RingHom.ker (algebraMap R (IsLocalRing.ResidueField R)))
          IsLocalRing.ker_residue.symm).toLinearMap) := by
  classical
  let K := IsLocalRing.ResidueField R
  obtain ⟨s, hs, hseps⟩ := hsep ⊤ hfg
  have hseps' : Algebra.IsSeparable
      (IntermediateField.adjoin k (Set.range ((↑) : s → (⊤ : IntermediateField k K))))
      (⊤ : IntermediateField k K) := by
    have hr : Set.range ((↑) : s → (⊤ : IntermediateField k K)) = s := by
      exact Subtype.range_coe_subtype
    rw [hr]
    exact hseps
  have : FormallySmooth k (⊤ : IntermediateField k K) :=
    FormallySmooth.of_algebraicIndependent_of_isSeparable hs.1
  have : FormallySmooth k K := FormallySmooth.of_equiv IntermediateField.topEquiv
  let f := IsScalarTower.toAlgHom k R K
  have hf : Function.Surjective f := IsLocalRing.residue_surjective
  have hq : Function.Surjective f.kerSquareLift :=
    Ideal.Quotient.lift_surjective_of_surjective _ _ hf
  have hn : IsNilpotent (RingHom.ker f.kerSquareLift.toRingHom) := by
    exact ⟨2, by rw [AlgHom.ker_kerSquareLift, Ideal.cotangentIdeal_square]; rfl⟩
  let σ := FormallySmooth.liftOfSurjective (AlgHom.id k K) f.kerSquareLift hq hn
  have hσ : f.kerSquareLift.comp σ = AlgHom.id k K :=
    FormallySmooth.comp_liftOfSurjective _ _ _ _
  obtain ⟨l, hl⟩ :=
    (retractionKerCotangentToTensorEquivSection (R := k) hf).symm ⟨σ, hσ⟩
  have hi : Function.Injective (KaehlerDifferential.kerCotangentToTensor k R K) := by
    apply Function.LeftInverse.injective (g := l)
    intro x
    exact LinearMap.congr_fun hl x
  exact hi.comp (Ideal.Cotangent.equivOfEq (IsLocalRing.maximalIdeal R)
    (RingHom.ker (algebraMap R K)) IsLocalRing.ker_residue.symm).injective

end Algebra
