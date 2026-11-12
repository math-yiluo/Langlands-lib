import Langlands.Cohomology.HyperextSpectralSequence
import Langlands.Cohomology.HyperextAbutmentFiltration
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
import Mathlib.Algebra.Homology.DerivedCategory.TStructure

/-!
# Convergence of the hyperext spectral sequence in Cartan–Eilenberg's Case 1

Let `t` be a t-structure on a triangulated category `C`, and let `K` and `B` be objects of `C`.
Worker 61's hyperext spectral sequence `hyperextSpectralSequence t K B` applies `Hom(-, B)` to the
truncations of `K`. Its object in position `(p, q)` on page 2 is
`Hom(heartPiece t K q, B⟦p + q⟧)`, its intended abutment in total degree `n` is `Hom(K, B⟦n⟧)`,
and that group is filtered by the subgroups `F^p` of morphisms factoring through
`K ⟶ τ_{≥ p - n} K`, with graded pieces `gr^p = F^p / F^{p+1}` (`HyperextAbutment.graded`).

The first group of propositions asserts convergence when `K` lies in degrees `≤ b` and `B` lies
in degrees `≥ c` (Cartan–Eilenberg, Chapter XVII §3, Case 1). For each position `(p, q)` and
every page `r` with `r ≥ 2`, `r ≥ p - c + 1` and `r ≥ q + b + 2`, the differentials of page `r`
leaving and entering `(p, q)` vanish, and the object in position `(p, q)` is isomorphic to
`gr^p` of `Hom(K, B⟦p + q⟧)`.

The second proposition concerns the covariant form, obtained by applying the construction in the
opposite of the derived category `D(C)` of an abelian category `C`, with the opposite of the
standard t-structure, to `op K` and `op A` for an object `A` of `C` in degree `0`. It asserts
that the object in position `(p, q)` on page 2 is `Ext^p(A, H^q(K))` for `p ≥ 0` and zero for
`p < 0`, and that the abutment in degree `n` is `Hom(A, K⟦n⟧)`. In the opposite category `op K`
lies in degrees `≤ b` when `K` lies in degrees `≥ -b`, and `op A` lies in degrees `≥ 0`, so the
first group of propositions applies to it.

All isomorphisms and vanishing statements are conclusions; none is supplied as data.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
  CategoryTheory.Triangulated Opposite

namespace Langlands.Cohomology

namespace HyperextConvergence

universe w w' v u

section Generic

variable (C : Type u) [Category.{v} C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C] [IsTriangulated C]

/-- Vanishing of the differentials at stable positions in Cartan–Eilenberg's Case 1. For every
t-structure `t` on `C`, every object `K` lying in degrees `≤ b` and every object `B` lying in
degrees `≥ c` for `t`, every page `r ≥ 2` and every position `(p, q)` with `r ≥ p - c + 1` and
`r ≥ q + b + 2`, the differentials of page `r` of the hyperext spectral sequence of `K` and `B`
leaving `(p, q)` and entering `(p, q)` are zero. -/
def HyperextHalfBoundedDifferentialStatement : Prop :=
  ∀ (t : TStructure C) (K B : C) (b c : ℤ) [t.IsLE K b] [t.IsGE B c] (r : ℤ) (hr : 2 ≤ r)
    (p q : ℤ), p - c + 1 ≤ r → q + b + 2 ≤ r → ∀ pq : ℤ × ℤ,
      ((HyperextSpectralSequence.hyperextSpectralSequence t K B).page r hr).d ⟨p, q⟩ pq = 0 ∧
        ((HyperextSpectralSequence.hyperextSpectralSequence t K B).page r hr).d pq ⟨p, q⟩ = 0

/-- Identification of the stable positions with the graded pieces of the abutment in
Cartan–Eilenberg's Case 1. For every t-structure `t` on `C`, every object `K` lying in degrees
`≤ b` and every object `B` lying in degrees `≥ c` for `t`, every page `r ≥ 2` and every position
`(p, q)` with `r ≥ p - c + 1` and `r ≥ q + b + 2`, the object of page `r` of the hyperext spectral
sequence of `K` and `B` in position `(p, q)` is isomorphic to the graded piece
`gr^p = F^p / F^{p+1}` of the abutment filtration on `Hom(K, B⟦p + q⟧)`. -/
def HyperextHalfBoundedStablePageStatement : Prop :=
  ∀ (t : TStructure C) (K B : C) (b c : ℤ) [t.IsLE K b] [t.IsGE B c] (r : ℤ) (hr : 2 ≤ r)
    (p q : ℤ), p - c + 1 ≤ r → q + b + 2 ≤ r →
      Nonempty (((HyperextSpectralSequence.hyperextSpectralSequence t K B).page r hr).X ⟨p, q⟩ ≅
        AddCommGrpCat.of (HyperextAbutment.graded t K B (p + q) p))

/-- Convergence of the hyperext spectral sequence of `K` and `B` when `K` is bounded above and
`B` is bounded below for the t-structure: vanishing of the differentials at stable positions and
identification of the stable positions with the graded pieces of the abutment filtration. -/
def HyperextHalfBoundedConvergenceStatements : Prop :=
  HyperextHalfBoundedDifferentialStatement C ∧ HyperextHalfBoundedStablePageStatement C

end Generic

section Covariant

open CategoryTheory.Pretriangulated.Opposite

variable (C : Type u) [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]

/-- The covariant hyperext spectral sequence, its second page and its abutment. Let `C` be an
abelian category with a model of its derived category, and with `Ext` groups in universe `w'`.
For every object `K` of the derived category and every object `A` of `C`, consider the hyperext
spectral sequence, in the opposite of the derived category with the opposite of the standard
t-structure, of `op K` and `op A`, where `A` is placed in degree `0`. Then:
the object in position `(p, q)` on page 2 is isomorphic to `Ext^p(A, H^q(K))` for `p : ℕ`;
it is zero for `p < 0`; and the abutment `op K ⟶ (op A)⟦n⟧` in total degree `n` is isomorphic to
`Hom(A, K⟦n⟧)`. -/
def CovariantSecondPageStatement : Prop :=
  ∀ [HasExt.{w'} C] (K : DerivedCategory C) (A : C),
    (∀ (p : ℕ) (q : ℤ), Nonempty
      (((HyperextSpectralSequence.hyperextSpectralSequence
          (HyperextSpectralSequence.opTStructure DerivedCategory.TStructure.t) (op K)
          (op ((DerivedCategory.singleFunctor C 0).obj A))).page 2).X ⟨(p : ℤ), q⟩ ≃+
        Abelian.Ext.{w'} A ((DerivedCategory.homologyFunctor C q).obj K) p)) ∧
    (∀ p q : ℤ, p < 0 →
      IsZero (((HyperextSpectralSequence.hyperextSpectralSequence
          (HyperextSpectralSequence.opTStructure DerivedCategory.TStructure.t) (op K)
          (op ((DerivedCategory.singleFunctor C 0).obj A))).page 2).X ⟨p, q⟩)) ∧
    (∀ n : ℤ, Nonempty
      ((op K ⟶ (op ((DerivedCategory.singleFunctor C 0).obj A))⟦n⟧) ≃+
        ShiftedHom ((DerivedCategory.singleFunctor C 0).obj A) K n))

end Covariant

end HyperextConvergence

end Langlands.Cohomology
