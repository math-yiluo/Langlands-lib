/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.Algebra.Module.Projective
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
import WeilConjectures.Algebra.Homology.AbelianVariety.UniversalH0SplitFactorization

/-! # A generalized inverse for the first differential

Source: Stacks Project, Tags 00O0 and 00NX, fixed-affine adaptation.
(blueprint: lem-sc-universal-h0-split-differential).
-/

@[expose] public section
set_option autoImplicit false
universe v
open CategoryTheory CategoryTheory.Limits

namespace CochainComplex

/-- Universal rank-one zeroth homology makes the first differential a split map onto
its image, with the image a direct summand of the next term.

Source: Stacks Project, Tags 00O0 and 00NX; the local algebra and splitting
steps of lem-sc-connective-universal-h0-zero-differential.
(blueprint: lem-sc-universal-h0-split-differential).

Proof: Only the terms in degrees minus one, zero, and one affect H0. Scalar
extension preserves the zero term in degree minus one, so H0 after each extension
is the kernel of the extended first differential. Localize at a prime to obtain
a map of finite free modules over a local ring A. Its residue kernel has dimension
one by the residue-algebra test. If the source rank is n, the residue matrix has
rank n minus one. A corresponding minor is a unit in A. Elementary row and column
operations put the matrix into an identity block of size n minus one and a remaining
map A to a finite free module. The kernel of that remaining map is isomorphic to A
by the A-algebra test. Its inclusion into A is multiplication by a non-zero-divisor
c. The remaining matrix entries are killed by c and hence are zero. The matrix is
therefore equivalent to an identity block and a zero block, and its cokernel is
finite free at every prime. The global cokernel is finitely presented (as a cokernel
of a map between finite presented modules), flat by the local criterion for flatness,
and projective by Tag 00NX. The quotient of P.X 1 onto this cokernel splits. Its kernel,
the image of d, is a projective direct summand of P.X 1. The surjection from P.X 0
onto this image also splits. Compose the projection onto the image with this second
section to obtain s, which satisfies d s d = d. The empty identity block when n = 1
causes no exception; source rank zero is excluded at each prime by residue H0 rank
one. If the ring is zero there are no primes and all maps are zero, so take s = 0. -/
theorem universalH0_split_differential
    (R : Type v) [CommRing R]
    (P : CochainComplex (ModuleCat.{v} R) ℤ)
    (hf0 : Module.Finite R (P.X 0))
    (hf1 : Module.Finite R (P.X 1))
    (hp0 : Module.Projective R (P.X 0))
    (hp1 : Module.Projective R (P.X 1))
    (hneg : IsZero (P.X (-1)))
    (hzero : ∀ (B : Type v) [CommRing B] (φ : R →+* B),
      let PB := ((ModuleCat.extendScalars φ).mapHomologicalComplex (.up ℤ)).obj P
      Nonempty (PB.homology 0 ≅ ModuleCat.of B B)) :
    ∃ s : P.X 1 ⟶ P.X 0, P.d 0 1 ≫ s ≫ P.d 0 1 = P.d 0 1 := by
  obtain ⟨I, e, p, r, q, hfac, her, hpq⟩ :=
    universalH0_split_factorization R P hf0 hf1 hp0 hp1 hneg hzero
  refine ⟨q ≫ r, ?_⟩
  calc
    P.d 0 1 ≫ (q ≫ r) ≫ P.d 0 1 = (e ≫ p) ≫ (q ≫ r) ≫ e ≫ p := by rw [hfac]
    _ = e ≫ (p ≫ q) ≫ r ≫ e ≫ p := by simp only [Category.assoc]
    _ = e ≫ r ≫ e ≫ p := by simp only [hpq, Category.id_comp]
    _ = P.d 0 1 := by
      rw [← Category.assoc r e p, her, Category.id_comp, ← hfac]
end CochainComplex
