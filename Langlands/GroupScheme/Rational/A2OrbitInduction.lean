import Langlands.GroupScheme.Rational.A2OrbitPieces
import Langlands.GroupScheme.Rational.OrthogonalOrbitDescent

/-! # Galois induction along the pieces of an `A₂` orbit

A point of `G(K)` fixed by the stabilizer of the base piece is transported to every piece of
the Galois orbit of the merged root. If the transports commute, their ordered product is
fixed by the whole Galois group. -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme.GaloisPointComparison

namespace Langlands.GroupScheme

namespace GaloisCompatiblePinningData

variable {k K : Type u} [Field k] [Field K] [Algebra k K]
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  (D : GaloisCompatiblePinningData k K G)

attribute [local instance] rootIndexMulAction

variable {m₀ : D.pinning.rootIndex}

/-- The Galois element carrying the base piece to the piece `c`, compatibly with the chosen
orientations: it carries `pairA (basePair m₀)` to `pairA c`. -/
def transportElement (c : D.PairOrbit m₀) : K ≃ₐ[k] K :=
  D.pairElement c * (D.pairElement (D.basePair m₀))⁻¹

theorem transportElement_smul (c : D.PairOrbit m₀) :
    D.transportElement c • D.basePair m₀ = c := by
  apply Subtype.ext
  change (D.pairElement c * (D.pairElement (D.basePair m₀))⁻¹) • m₀ = c.1
  have h0 : D.pairElement (D.basePair m₀) • m₀ = m₀ := D.pairElement_smul (D.basePair m₀)
  rw [mul_smul, inv_smul_eq_iff.mpr h0.symm, D.pairElement_smul]

theorem action_transportElement_pairA {p₀ : D.pinning.base.support} (c : D.PairOrbit m₀) :
    D.action (D.transportElement c) (D.pairA p₀ (D.basePair m₀)) = D.pairA p₀ c := by
  simp only [transportElement, pairA, map_mul, Equiv.Perm.mul_apply, map_inv]
  rw [Equiv.Perm.inv_def, Equiv.symm_apply_apply]

theorem action_transportElement_pairB {q₀ : D.pinning.base.support} (c : D.PairOrbit m₀) :
    D.action (D.transportElement c) (D.pairB q₀ (D.basePair m₀)) = D.pairB q₀ c := by
  simp only [transportElement, pairB, map_mul, Equiv.Perm.mul_apply, map_inv]
  rw [Equiv.Perm.inv_def, Equiv.symm_apply_apply]

/-- The transport of a point of `G(K)` from the base piece to the piece `c`. -/
def inducedPoint (h₀ : rationalPoints (baseChanged k K G)) (c : D.PairOrbit m₀) :
    rationalPoints (baseChanged k K G) :=
  rationalConjugate k K G (D.transportElement c) h₀

/-- Galois conjugation permutes the transports, provided the base point is fixed by the
stabilizer of the base piece. -/
theorem rationalConjugate_inducedPoint {h₀ : rationalPoints (baseChanged k K G)}
    (hfix : ∀ g : K ≃ₐ[k] K, g • D.basePair m₀ = D.basePair m₀ →
      rationalConjugate k K G g h₀ = h₀)
    (σ : K ≃ₐ[k] K) (c : D.PairOrbit m₀) :
    rationalConjugate k K G σ (D.inducedPoint h₀ c) = D.inducedPoint h₀ (σ • c) := by
  set g := (D.transportElement (σ • c))⁻¹ * σ * D.transportElement c with hg
  have hgc : g • D.basePair m₀ = D.basePair m₀ := by
    rw [hg, mul_smul, mul_smul, D.transportElement_smul, inv_smul_eq_iff,
      D.transportElement_smul]
  have hσ : σ * D.transportElement c = D.transportElement (σ • c) * g := by
    rw [hg]; group
  unfold inducedPoint
  rw [← rationalConjugate_mul, hσ, rationalConjugate_mul, hfix g hgc]

/-- **Galois induction.** If the transports of `h₀` to distinct pieces commute, their ordered
product is fixed by every Galois automorphism. -/
theorem rationalConjugate_inducedProduct {h₀ : rationalPoints (baseChanged k K G)}
    (hfix : ∀ g : K ≃ₐ[k] K, g • D.basePair m₀ = D.basePair m₀ →
      rationalConjugate k K G g h₀ = h₀)
    (hcomm : ∀ c c' : D.PairOrbit m₀, c ≠ c' →
      Commute (D.inducedPoint h₀ c) (D.inducedPoint h₀ c'))
    (σ : K ≃ₐ[k] K) :
    rationalConjugate k K G σ
        (List.ofFn fun l => D.inducedPoint h₀ (D.pieceEquiv m₀ l)).prod =
      (List.ofFn fun l => D.inducedPoint h₀ (D.pieceEquiv m₀ l)).prod := by
  rw [map_list_prod, List.map_ofFn]
  let π : Equiv.Perm (Fin (Nat.card (D.PairOrbit m₀))) :=
    ((D.pieceEquiv m₀).trans (MulAction.toPerm σ)).trans (D.pieceEquiv m₀).symm
  have hπ : ∀ l, D.pieceEquiv m₀ (π l) = σ • D.pieceEquiv m₀ l := fun l => by
    simp only [π, Equiv.trans_apply, Equiv.apply_symm_apply]
    rfl
  have h1 : (List.ofFn (rationalConjugate k K G σ ∘ fun l =>
      D.inducedPoint h₀ (D.pieceEquiv m₀ l))) =
      List.ofFn ((fun l => D.inducedPoint h₀ (D.pieceEquiv m₀ l)) ∘ π) := by
    apply List.ofFn_inj.mpr
    funext l
    simp only [Function.comp_apply]
    rw [D.rationalConjugate_inducedPoint hfix, hπ]
  rw [h1]
  apply List.Perm.prod_eq' (Equiv.Perm.ofFn_comp_perm π _)
  rw [List.pairwise_ofFn]
  intro l l' hll'
  exact hcomm _ _ (fun h => (ne_of_lt hll') (π.injective ((D.pieceEquiv m₀).injective h)))

end GaloisCompatiblePinningData

end Langlands.GroupScheme
