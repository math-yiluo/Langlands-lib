import Langlands.Representation.Category.Basic
import Langlands.Representation.Smooth.Contragredient.Definitions
import Mathlib.Analysis.Complex.Basic

/-! # Hermitian representations (Renard IV.2.1)

A smooth representation `(π, V)` is hermitian if it carries a nondegenerate `G`-invariant
hermitian form. Its hermitian contragredient `π^h` is the complex conjugate of the smooth
dual, so an isomorphism `π^h ≅ π` is a `G`-equivariant conjugate-linear bijection from `V`
onto its smooth dual. If `π^h ≅ π`, then `π` is hermitian; conversely an admissible hermitian
representation satisfies `π^h ≅ π` (Remark 1). On an irreducible admissible representation,
two nondegenerate invariant hermitian forms differ by a nonzero scalar (Remark 2).
-/

noncomputable section

universe u v

open CategoryTheory

namespace Langlands.Renard.CompactRepresentation

/-- Renard IV.2.1, Remark 1, first assertion: let `G` be a Hausdorff, locally compact, totally
disconnected group and `π` a smooth representation. If there is a
`G`-equivariant conjugate-linear bijection `e` from `π` onto its smooth dual (that is,
`π^h ≅ π`), then `π` is hermitian: there is a form `B`, conjugate-linear in the first and
linear in the second variable, which is hermitian (`B(w, v) = conj B(v, w)`), nondegenerate
and `G`-invariant. -/
def HermitianOfSelfDualStatement : Prop :=
  ∀ (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G]
    (π : SmoothRep.{0, u, v} ℂ G),
    (∃ e : π ≃ₗ⋆[ℂ] SmoothDual π.representation, ∀ (g : G) (x : π),
      e (π.representation g x) = smoothContragredient π.representation g (e x)) →
    ∃ B : π →ₗ⋆[ℂ] π →ₗ[ℂ] ℂ,
      (∀ x y : π, B y x = starRingEnd ℂ (B x y)) ∧ (∀ x : π, (∀ y, B x y = 0) → x = 0) ∧
        ∀ (g : G) (x y : π), B (π.representation g x) (π.representation g y) = B x y

/-- Renard IV.2.1, Remark 1, converse: let `G` be a Hausdorff, locally compact, totally
disconnected group and `π` an admissible representation with a nondegenerate `G`-invariant
hermitian form `B`. Then `x ↦ B(x, ·)` is a `G`-equivariant conjugate-linear bijection from
`π` onto its smooth dual; in particular `π^h ≅ π`. -/
def SelfDualOfHermitianStatement : Prop :=
  ∀ (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G]
    (π : SmoothRep.{0, u, v} ℂ G), π.IsAdmissible →
    ∀ B : π →ₗ⋆[ℂ] π →ₗ[ℂ] ℂ,
      (∀ x y : π, B y x = starRingEnd ℂ (B x y)) → (∀ x : π, (∀ y, B x y = 0) → x = 0) →
      (∀ (g : G) (x y : π), B (π.representation g x) (π.representation g y) = B x y) →
      ∃ e : π ≃ₗ⋆[ℂ] SmoothDual π.representation,
        (∀ x y : π, (e x : Module.Dual ℂ π) y = B x y) ∧
          ∀ (g : G) (x : π),
            e (π.representation g x) = smoothContragredient π.representation g (e x)

/-- Renard IV.2.1, Remark 2: let `G` be a Hausdorff, locally compact, totally disconnected
group and `π` an irreducible admissible representation. Any two nondegenerate `G`-invariant
hermitian forms `B` and `B'` on `π` satisfy `B' = c B` for a nonzero real number `c`. -/
def HermitianFormUniquenessStatement : Prop :=
  ∀ (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G]
    (π : SmoothRep.{0, u, v} ℂ G), π.IsIrreducible → π.IsAdmissible →
    let IsInvariantHermitian : (π →ₗ⋆[ℂ] π →ₗ[ℂ] ℂ) → Prop := fun B =>
      (∀ x y : π, B y x = starRingEnd ℂ (B x y)) ∧ (∀ x : π, (∀ y, B x y = 0) → x = 0) ∧
        ∀ (g : G) (x y : π), B (π.representation g x) (π.representation g y) = B x y
    ∀ B B' : π →ₗ⋆[ℂ] π →ₗ[ℂ] ℂ, IsInvariantHermitian B → IsInvariantHermitian B' →
      ∃ c : ℝ, c ≠ 0 ∧ ∀ x y : π, B' x y = (c : ℂ) * B x y

/-- The three statements above. -/
def HermitianRepresentationStatements.{u', v'} : Prop :=
  HermitianOfSelfDualStatement.{u', v'} ∧ SelfDualOfHermitianStatement.{u', v'} ∧
    HermitianFormUniquenessStatement.{u', v'}

end Langlands.Renard.CompactRepresentation
