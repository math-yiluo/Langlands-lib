/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.FieldTheory.SeparableExtension
public import Mathlib.RingTheory.AlgebraicIndependent.Basic
public import Mathlib.RingTheory.Kaehler.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import WeilConjectures.FieldTheory.SeparablyGeneratedDifferentialsBasis
import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis

/-!
# Differentials of a separably generated field extension

Source: Stacks Project, Algebra, proof of Tag 031W and the dimension assertion in the
proof of Tag 00TV (blueprint: lem-weil-pbc-separably-generated-differentials-dimension).
-/

@[expose] public section

universe u v

namespace KaehlerDifferential

/-- The differentials of a separating transcendence basis form a basis, and the dimension
of the differentials is the transcendence degree.
Source: Stacks Project, Algebra, proofs of Tags 031W and 00TV.
(blueprint: lem-weil-pbc-separably-generated-differentials-dimension)

Proof:
1. Put F = k(x₁, …, xᵣ). Algebraic independence gives an injective evaluation map from
   P = k[X₁, …, Xᵣ] to K. Its fraction field identifies with F: the fractions of
   polynomial values form precisely the smallest subfield containing k and the xᵢ
   (def-weil-pbc-transcendence-basis).
2. The polynomial differentials are free on dXᵢ by Tag 00RX
   (lem-weil-pbc-polynomial-ring-kahler-basis). Localizing at the nonzero polynomials
   gives Ω[F/k] free on dxᵢ by Tag 00RT
   (lem-weil-pbc-kahler-differentials-localization). The localization map carries
   dXᵢ to dxᵢ (def-weil-pbc-kahler-differentials).
3. K/F is separable algebraic (def-weil-pbc-separable-algebraic-extension). It is
   finite because the finitely many field generators of K/k also generate K/F,
   and each is algebraic. The canonical map K ⊗[F] Ω[F/k] → Ω[K/k] is an isomorphism
   by lem-weil-pbc-separable-algebraic-differentials-base-change (Tag 090W).
4. Tensor the basis of step 2 with K and transport it along the isomorphism of step 3.
   Its vectors map to dxᵢ, yielding the required K-basis. There are r vectors, and
   r is the transcendence degree (def-kun-transcendence-degree). This proves finite
   dimensionality and the dimension equality, including r = 0. -/
theorem exists_basis_differentials_of_separating_transcendenceBasis
    {k : Type u} {K : Type v} [Field k] [Field K] [Algebra k K]
    (hfg : (⊤ : IntermediateField k K).FG)
    (hsep : Algebra.IsSeparableExtension k K)
    {r : ℕ} (x : Fin r → K) (hx : IsTranscendenceBasis k x)
    (hxs : Algebra.IsSeparable (IntermediateField.adjoin k (Set.range x)) K) :
    (∃ b : Module.Basis (Fin r) K (KaehlerDifferential k K),
      ∀ i : Fin r, b i = D k K (x i)) ∧
    FiniteDimensional K (KaehlerDifferential k K) ∧
    (Module.finrank K (KaehlerDifferential k K) : Cardinal.{v}) = Algebra.trdeg k K := by
  obtain ⟨b, hb⟩ := exists_basis_differentials_of_separating_transcendenceBasis_basis
    hfg hsep x hx hxs
  refine ⟨⟨b, hb⟩, Module.Finite.of_basis b, ?_⟩
  rw [Module.finrank_eq_card_basis b]
  have hcard := hx.lift_cardinalMk_eq_trdeg
  simpa using hcard

end KaehlerDifferential
