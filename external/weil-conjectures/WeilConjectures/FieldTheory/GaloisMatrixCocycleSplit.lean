/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.FieldTheory.IsSepClosed
public import Mathlib.FieldTheory.KrullTopology
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.Topology.LocallyConstant.Basic
import WeilConjectures.FieldTheory.GaloisMatrixCocycleDescent

/-!
# Splitting an algebra with a genuine matrix descent cocycle

Source: Stacks Project, Tag 03R7, injectivity argument; Section 0DVG.
-/

@[expose] public section

universe u

namespace Field

open scoped TensorProduct

/-- A genuine locally constant matrix descent cocycle makes a split form split over K.

Proof: compactness of the absolute Galois group makes the locally constant map b have
finite image. Its cocycle identity forces b(1)=1. Choose an open normal subgroup N on
whose cosets b is constant, fixing every entry of its image, and fixing the finitely many
coefficients of e and its inverse in K-bases (the existence of e implies D is finite
dimensional). Then b restricts to 1 on N and descends to a cocycle of the finite Galois
extension L=S^N/K with values in GL_n(L). To prove matrix Hilbert 90 without dividing
by the group order, use T(v)=sum_g b(g)g(v). The cocycle identity makes T(v) invariant
under the semilinear action v ↦ b(g)g(v). These vectors span L^n: otherwise a nonzero
row lambda annihilates them. Applying it to v=r*e_j for every r in L gives
sum_g (lambda*b(g))_j*g(r)=0. Linear independence of distinct field automorphisms
forces every coefficient to vanish. In particular lambda*b(1)=lambda=0, a contradiction.
Choose n linearly independent vectors from this spanning set. If t has these invariant
vectors as columns, it is invertible and b(g)g(t)=t, so b(g)=t*g(t) inverse.
Conjugate e by t inverse on the
left and t on the right. The displayed descent identity then says that all images of
1 tensor d have Galois-fixed entries. The fixed elements of the separable closure are
K, so this restricts to a K-algebra map D → M_n(K). Its scalar extension is the
conjugated equivalence e, hence it is bijective by faithful scalar extension. This also
covers n=0: both sides are zero algebras whenever such e exists. No central simplicity,
Brauer class or scalar-defect hypothesis is used.
Source: Stacks Project, Tag 03R7, injectivity via descent of vector spaces.
(blueprint: lem-sc-galois-matrix-cocycle-split). -/
theorem nonempty_algEquiv_matrix_of_galois_cocycle (K : Type u) [Field K]
    (D : Type u) [Ring D] [Algebra K D] (n : ℕ)
    (e : (SeparableClosure K ⊗[K] D) ≃ₐ[SeparableClosure K]
      Matrix (Fin n) (Fin n) (SeparableClosure K))
    (b : Gal(SeparableClosure K/K) →
      Matrix.GeneralLinearGroup (Fin n) (SeparableClosure K))
    (hb : IsLocallyConstant b)
    (hdesc : ∀ (g : Gal(SeparableClosure K/K)) (a : D),
      (e (1 ⊗ₜ[K] a)).map g =
        ((b g)⁻¹).val * e (1 ⊗ₜ[K] a) * (b g).val)
    (hcoc : ∀ g h, b g * Matrix.GeneralLinearGroup.map g.toRingHom (b h) = b (g * h)) :
    Nonempty (D ≃ₐ[K] Matrix (Fin n) (Fin n) K) := by
  obtain ⟨f, hf⟩ := exists_algHom_matrix_of_galois_cocycle K D n e b hb hdesc hcoc
  have hfbij : Function.Bijective f := hf
  have ef : D ≃ₐ[K] Matrix (Fin n) (Fin n) K := AlgEquiv.ofBijective f hfbij
  exact ⟨ef⟩

end Field
