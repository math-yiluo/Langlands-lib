import Langlands.GroupScheme.Reductive.TitsIndex
import Langlands.GroupScheme.Reductive.AbsolutelyAlmostSimple
import Mathlib.LinearAlgebra.Matrix.Cartan.Basic

/-! # Exact Cartan matrices of actual absolutely almost-simple groups -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

namespace TitsIndexData

variable {k : Type u} [Field k]
  {G : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  (d : TitsIndexData G)

/-- An equivalence of the actual simple vertices with every ordered entry of
the supplied integral Cartan matrix. No marking or star condition is imposed. -/
def HasCartanMatrix {n : ℕ} (M : Matrix (Fin n) (Fin n) ℤ) : Prop :=
  ∃ e : d.Vertex ≃ Fin n, ∀ a b, d.cartan a b = M (e a) (e b)

/-- The nine irreducible finite Cartan families, with exact ordered entries.
Rank-two B and C are both permitted; uniqueness is not asserted. -/
def HasIrreducibleCartanType : Prop :=
  (∃ n : ℕ, 1 ≤ n ∧ d.HasCartanMatrix (CartanMatrix.A n)) ∨
  (∃ n : ℕ, 2 ≤ n ∧ d.HasCartanMatrix (CartanMatrix.B n)) ∨
  (∃ n : ℕ, 2 ≤ n ∧ d.HasCartanMatrix (CartanMatrix.C n)) ∨
  (∃ n : ℕ, 4 ≤ n ∧ d.HasCartanMatrix (CartanMatrix.D n)) ∨
  d.HasCartanMatrix (CartanMatrix.E 6) ∨
  d.HasCartanMatrix (CartanMatrix.E 7) ∨
  d.HasCartanMatrix (CartanMatrix.E 8) ∨
  d.HasCartanMatrix CartanMatrix.F₄ ∨
  d.HasCartanMatrix CartanMatrix.G₂

end TitsIndexData

namespace TitsIndexEquiv

variable {k : Type u} [Field k]
  {G H : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  [IsAffineHom H.X.hom] [LocallyOfFiniteType H.X.hom]
  {d : TitsIndexData G} {e : TitsIndexData H}

/-- Exact Cartan presentations are preserved by equivalence of actual indices. -/
theorem hasCartanMatrix_iff (f : TitsIndexEquiv d e)
    {n : ℕ} (M : Matrix (Fin n) (Fin n) ℤ) :
    d.HasCartanMatrix M ↔ e.HasCartanMatrix M := by
  constructor
  · rintro ⟨a, ha⟩
    refine ⟨f.vertices.symm.trans a, ?_⟩
    intro i j
    calc
      e.cartan i j =
          d.cartan (f.vertices.symm i) (f.vertices.symm j) := by
        simpa using f.cartan_eq (f.vertices.symm i) (f.vertices.symm j)
      _ = M (a (f.vertices.symm i)) (a (f.vertices.symm j)) := ha _ _
  · rintro ⟨a, ha⟩
    refine ⟨f.vertices.trans a, ?_⟩
    intro i j
    exact (f.cartan_eq i j).symm.trans (ha _ _)

/-- The finite-family property is independent of equivalent actual index data. -/
theorem hasIrreducibleCartanType_iff (f : TitsIndexEquiv d e) :
    d.HasIrreducibleCartanType ↔ e.HasIrreducibleCartanType := by
  simp only [TitsIndexData.HasIrreducibleCartanType, f.hasCartanMatrix_iff]

end TitsIndexEquiv

/-- Over every field, every actual Tits index of an absolutely almost-simple
group has an exact numbering by one of the irreducible finite Cartan matrices.
This is an unproved structural prerequisite, with no local-field hypothesis. -/
def AbsolutelyAlmostSimpleCartanClassificationStatement : Prop :=
  ∀ (k : Type u) [Field k]
    (G : GroupScheme (Spec (CommRingCat.of k))) [IsAffineHom G.X.hom]
    [LocallyOfFiniteType G.X.hom] (d : TitsIndexData G),
    IsAbsolutelyAlmostSimple G → d.HasIrreducibleCartanType

end Langlands.GroupScheme
