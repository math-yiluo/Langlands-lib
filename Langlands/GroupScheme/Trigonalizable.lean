import Langlands.GroupScheme.Reductive.Basic

/-! # Trigonalizable group schemes over a field (Milne 16.1)

A coordinate vector spans a stable line of a matrix representation when every point, with values
in any scheme, maps it to a multiple of itself. A group scheme over a field is trigonalizable when
every nonzero finite-dimensional representation has a stable line, that is, a one-dimensional
subrepresentation.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped Matrix

namespace Langlands.GroupScheme

namespace MatrixRepresentation

variable {R : CommRingCat.{u}} {G : GroupScheme (Spec R)} {n : Type} [Fintype n] [DecidableEq n]

/-- The coordinate vector `v ∈ Rⁿ` spans a line stable under `ρ`: for every scheme `T` over
`Spec R` and every point `g ∈ G(T)`, the matrix `ρ(g)` sends the image of `v` in `Γ(T, 𝒪_T)ⁿ`
to a `Γ(T, 𝒪_T)`-multiple of that image. -/
def IsStableLine (ρ : MatrixRepresentation G n) (v : n → R) : Prop :=
  ∀ (T : Over (Spec R)) (g : T ⟶ G.X), ∃ c : Γ(T.left, ⊤),
    (ρ.pointMatrix T g : Matrix n n Γ(T.left, ⊤)) *ᵥ (fun i => scalarMap T (v i)) =
      c • fun i => scalarMap T (v i)

/-- A fixed vector spans a stable line, with every multiplier equal to `1`. -/
theorem IsFixedVector.isStableLine {ρ : MatrixRepresentation G n} {v : n → R}
    (hv : ρ.IsFixedVector v) : ρ.IsStableLine v := fun T g =>
  ⟨1, by rw [one_smul]; exact hv T g⟩

end MatrixRepresentation

section Field

variable {k : Type u} [Field k]

/-- Milne 2017, Definition 16.1: a group scheme `G` over a field `k` is trigonalizable if every
nonzero finite-dimensional representation of `G` has a one-dimensional subrepresentation, that
is, a nonzero vector spanning a stable line. -/
def IsTrigonalizable (G : GroupScheme (Spec (CommRingCat.of k))) : Prop :=
  ∀ (n : Type) [Fintype n] [DecidableEq n] [Nonempty n] (ρ : MatrixRepresentation G n),
    ∃ v : n → k, v ≠ 0 ∧ ρ.IsStableLine v

/-- Unipotent group schemes are trigonalizable: a nonzero fixed vector spans a stable line. -/
theorem IsUnipotent.isTrigonalizable {G : GroupScheme (Spec (CommRingCat.of k))}
    (hG : IsUnipotent G) : IsTrigonalizable G := by
  intro n _ _ _ ρ
  obtain ⟨v, hv, hfix⟩ := hG n ρ
  exact ⟨v, hv, hfix.isStableLine⟩

end Field

end Langlands.GroupScheme
