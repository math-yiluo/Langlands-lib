import Langlands.Representation.Induction.CompactFixedVectorModel

/-!
# Fixed vectors over a double-coset transversal and conjugation (Renard III.2.2, III.2.4)

For a compact open subgroup `K`, restriction to a system of representatives `Ω` of
`P \ G / K` identifies the `K`-fixed vectors of smooth induction with all functions on `Ω`
whose value at `ω` is fixed by `P ∩ ω K ω⁻¹`, and those of compact induction with the finitely
supported such functions. Conjugation by an element carrying `P` onto `Q` transports compact
induction, by `f ↦ (x ↦ f(c⁻¹ x))`.
-/

namespace Langlands.Induction

universe uR uG uV

/-- Renard III.2.2, Lemma: let `K` be a compact open subgroup of `G` and `Ω` a system of
representatives of the double cosets `P \ G / K`. Restriction of functions to `Ω` is a linear
isomorphism from the `K`-fixed vectors of `Ind_P^G σ` onto the functions `f` on `Ω` with
`f(ω)` fixed by `P ∩ ω K ω⁻¹`, and from the `K`-fixed vectors of `ind_P^G σ` onto the finitely
supported such functions. -/
def InducedFixedVectorTransversalStatement : Prop :=
  ∀ (R : Type uR) (G : Type uG) (V : Type uV) [CommRing R] [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [AddCommGroup V] [Module R V]
    (P : Subgroup G) (σ : Representation R P V) (K : OpenSubgroup G),
    IsCompact (K : Set G) →
    ∀ (Ω : Set G),
      (∀ x : G, ∃ ω ∈ Ω, ∃ p ∈ P, ∃ k ∈ K, x = p * ω * k) →
      Function.Injective (fun ω : Ω => DoubleCoset.mk P K.toSubgroup (ω : G)) →
      (∃ e : fixedVectors (smoothInduced P σ) K.toSubgroup ≃ₗ[R]
          ((ω : Ω) → fixedVectors σ (conjOpenSubgroup P K ω).toSubgroup),
        ∀ (f : fixedVectors (smoothInduced P σ) K.toSubgroup) (ω : Ω),
          ((e f ω : fixedVectors σ (conjOpenSubgroup P K ω).toSubgroup) : V) =
            eval P σ f.val ω) ∧
      ∃ e : fixedVectors (compactInduced P σ) K.toSubgroup ≃ₗ[R]
          (Π₀ ω : Ω, fixedVectors σ (conjOpenSubgroup P K ω).toSubgroup),
        ∀ (f : fixedVectors (compactInduced P σ) K.toSubgroup) (ω : Ω),
          ((e f ω : fixedVectors σ (conjOpenSubgroup P K ω).toSubgroup) : V) =
            eval P σ f.val.val ω

/-- Renard III.2.4, Lemma, compact induction: if `c` conjugates `P` onto `Q`, by
`e p = c p c⁻¹`, and `τ (e p) = σ p` (Renard's `ρ^c` when `P = Q` is normalized by `c`), then
`(A f)(x) = f(c⁻¹ x)` defines an equivalence of `ind_P^G σ` with `ind_Q^G τ`. -/
def CompactConjugateInducedStatement : Prop :=
  ∀ (R : Type uR) (G : Type uG) (V : Type uV) [CommRing R] [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [AddCommGroup V] [Module R V]
    (P Q : Subgroup G) (σ : Representation R P V) (τ : Representation R Q V)
    (c : G) (e : P ≃* Q),
    (∀ p : P, (e p : G) = c * p * c⁻¹) → (∀ p : P, τ (e p) = σ p) →
    ∃ A : (compactInduced P σ).Equiv (compactInduced Q τ),
      ∀ (f : CompactFunctions P σ) (x : G),
        eval Q τ (A f).val x = eval P σ f.val (c⁻¹ * x)

end Langlands.Induction
