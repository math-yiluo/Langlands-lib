import Langlands.GroupScheme.SimplyConnected.InnerTypeANormOneStatement
import Mathlib.Data.Fin.Rev
import Mathlib.NumberTheory.LocalField.Basic

/-!
# Actual local rank-one Tits indices

This module states the enumeration of the actual local rank-one indices.
Its five alternatives compare every Cartan entry, every distinguished vertex
and the full absolute Galois star action. The enumeration is not proved here.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

variable {K : Type u} [Field K]
  {G : GroupScheme (Spec (CommRingCat.of K))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]

namespace TitsIndexData

variable (d : TitsIndexData G)

/-- An actual numbering preserving all Cartan entries and exactly the
distinguished vertices. The predicate `marked` uses zero-based indices. -/
def IsNumberingOf {n : ℕ} (M : Matrix (Fin n) (Fin n) ℤ)
    (marked : Fin n → Prop) (e : d.Vertex ≃ Fin n) : Prop :=
  (∀ a b, d.cartan a b = M (e a) (e b)) ∧
    ∀ a, a ∈ d.distinguishedVertices ↔ marked (e a)

/-- Every element of the full absolute Galois group fixes every vertex. -/
def StarIsTrivial : Prop :=
  ∀ (σ : SeparableClosure K ≃ₐ[K] SeparableClosure K) (a : d.Vertex),
    d.star σ a = a

/-- Under the supplied numbering, the full star image is exactly the identity
and a specified nonidentity permutation. The disjunction is outside the vertex
quantifier, so one permutation describes each Galois element globally. -/
def StarImagePair {n : ℕ} (e : d.Vertex ≃ Fin n) (τ : Equiv.Perm (Fin n)) : Prop :=
  τ ≠ 1 ∧
    (∀ σ : SeparableClosure K ≃ₐ[K] SeparableClosure K,
      (∀ a, e (d.star σ a) = e a) ∨ (∀ a, e (d.star σ a) = τ (e a))) ∧
    ∃ σ : SeparableClosure K ≃ₐ[K] SeparableClosure K,
      ∀ a, e (d.star σ a) = τ (e a)

/-- The index `¹A_(2*degree-1),1^(degree)`: trivial full star action and the
single distinguished vertex numbered `degree` in one-based notation. -/
def HasRankOneInnerAIndex (degree : ℕ) : Prop :=
  0 < degree ∧
    (∃ e : d.Vertex ≃ Fin (2 * degree - 1),
      d.IsNumberingOf (CartanMatrix.A (2 * degree - 1))
        (fun i => i.val + 1 = degree) e) ∧
    d.StarIsTrivial

/-- The indices `²A_2,1^(1)` and `²A_3,1^(1)`: distinguished endpoints and
full star image the identity and the reversal of the chain. -/
def HasRankOneOuterAIndex (n : ℕ) : Prop :=
  (n = 2 ∨ n = 3) ∧
    ∃ e : d.Vertex ≃ Fin n,
      d.IsNumberingOf (CartanMatrix.A n) (fun i => i.val = 0 ∨ i.val + 1 = n) e ∧
        d.StarImagePair e Fin.revPerm

/-- The indices `C_2,1^(2)` and `C_3,1^(2)`: trivial full star action and
the single distinguished vertex numbered 2 in one-based notation. -/
def HasRankOneCIndex (n : ℕ) : Prop :=
  (n = 2 ∨ n = 3) ∧
    (∃ e : d.Vertex ≃ Fin n,
      d.IsNumberingOf (CartanMatrix.C n) (fun i => i.val = 1) e) ∧
    d.StarIsTrivial

/-- The index `²D_4,1^(2)`: distinguished central vertex, and full star image
the identity and the transposition of the last two fork tips. -/
def HasRankOneOuterD4Index : Prop :=
  ∃ e : d.Vertex ≃ Fin 4,
    d.IsNumberingOf (CartanMatrix.D 4) (fun i => i.val = 1) e ∧
      d.StarImagePair e (Equiv.swap (2 : Fin 4) (3 : Fin 4))

/-- The index `¹D_5,1^(2)`: trivial full star action and the single
distinguished vertex numbered 2 in one-based notation. -/
def HasRankOneInnerD5Index : Prop :=
  (∃ e : d.Vertex ≃ Fin 5,
    d.IsNumberingOf (CartanMatrix.D 5) (fun i => i.val = 1) e) ∧
    d.StarIsTrivial

/-- The inner-A index alternative supplies the actual type predicate used
by the separate norm-one identification statement. -/
theorem HasRankOneInnerAIndex.hasInnerTypeA {degree : ℕ}
    (h : d.HasRankOneInnerAIndex degree) : d.HasInnerTypeA (2 * degree - 1) := by
  rcases h with ⟨hdegree, ⟨e, hcartan, _⟩, hstar⟩
  exact ⟨by omega, ⟨e, hcartan⟩, hstar⟩

/-- The two-element full-star condition rules out inner type. -/
theorem StarImagePair.not_starIsTrivial {n : ℕ} {e : d.Vertex ≃ Fin n}
    {τ : Equiv.Perm (Fin n)} (h : d.StarImagePair e τ) : ¬ d.StarIsTrivial := by
  rcases h with ⟨hne, _, ⟨σ, hσ⟩⟩
  intro hstar
  apply hne
  apply Equiv.ext
  intro i
  obtain ⟨a, rfl⟩ := e.surjective i
  change τ (e a) = e a
  rw [← hσ a, hstar σ a]

end TitsIndexData

/-- Over every nonarchimedean local field, the actual index of a simply
connected absolutely almost-simple group of split rank one is one of the five
listed indices. This is an unproved prerequisite, in every characteristic. -/
def LocalRankOneTitsIndexStatement : Prop :=
  ∀ (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (G : GroupScheme (Spec (CommRingCat.of K))) [IsAffineHom G.X.hom]
    [LocallyOfFiniteType G.X.hom] (d : TitsIndexData G),
    IsSimplyConnected G → IsAbsolutelyAlmostSimple G → splitRank G = 1 →
      (∃ degree : ℕ, d.HasRankOneInnerAIndex degree) ∨
      (∃ n : ℕ, d.HasRankOneOuterAIndex n) ∨
      (∃ n : ℕ, d.HasRankOneCIndex n) ∨
      d.HasRankOneOuterD4Index ∨ d.HasRankOneInnerD5Index

end Langlands.GroupScheme
