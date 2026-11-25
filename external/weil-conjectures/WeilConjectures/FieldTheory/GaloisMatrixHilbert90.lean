/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.FieldTheory.IsSepClosed
public import Mathlib.FieldTheory.KrullTopology
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.Topology.LocallyConstant.Basic
import WeilConjectures.FieldTheory.GaloisMatrixHilbert90Normalized

/-!
# Matrix Hilbert 90 over a separable closure

Source: Stacks Project, Tag 03R7, injectivity argument, expanded as an invariant-basis
proof of the general-linear Hilbert 90 theorem.
(blueprint: lem-sc-galois-matrix-hilbert90)
-/

@[expose] public section

universe u
namespace Field

/-- A locally constant general-linear Galois cocycle admits an invariant matrix basis.

Proof: compactness of the absolute Galois group implies that the locally constant map
b has finite image and is constant on cosets of an open normal subgroup. The cocycle
identity implies b(1)=1. Shrink that subgroup to fix every entry of the finite image;
then b is 1 on the subgroup and descends to a cocycle with coefficients in its finite
Galois fixed field L. On L^n put T(v)=sum_g b(g)g(v). Reindexing the sum and using the
cocycle identity shows that T(v) is invariant for the semilinear action b(g)g(-).
These vectors span L^n: otherwise a nonzero row lambda annihilates all T(v). Evaluating
on v=r*e_j gives sum_g (lambda*b(g))_j*g(r)=0 for all r in L. Linear independence of
distinct field automorphisms makes every coefficient zero. The coefficient at 1 is
lambda_j since b(1)=1, contradicting lambda being nonzero. Choose a basis from these
invariant vectors and put them in the columns of t. Its columns are independent, so
t is invertible, and columnwise invariance gives b(g)g(t)=t. Embed L in the separable
closure to obtain the asserted t for every absolute Galois automorphism. When n=0,
the general linear group of the zero-dimensional space is trivial, so t=1 works.
The argument uses no division by the group order and works in every characteristic.

Source: Stacks Project, Tag 03R7, injectivity, general-linear descent argument.
(blueprint: lem-sc-galois-matrix-hilbert90). -/
theorem exists_galois_matrix_invariant_basis (K : Type u) [Field K] (n : ℕ)
    (b : Gal(SeparableClosure K/K) →
      Matrix.GeneralLinearGroup (Fin n) (SeparableClosure K))
    (hb : IsLocallyConstant b)
    (hcoc : ∀ g h, b g * Matrix.GeneralLinearGroup.map g.toRingHom (b h) = b (g * h)) :
    ∃ t : Matrix.GeneralLinearGroup (Fin n) (SeparableClosure K),
      ∀ g, b g * Matrix.GeneralLinearGroup.map g.toRingHom t = t := by
  by_cases hn : n = 0
  · subst n
    refine ⟨1, ?_⟩
    intro g
    apply Subsingleton.elim
  · exact exists_galois_matrix_invariant_basis_normalized K n b hb hn hcoc

end Field
