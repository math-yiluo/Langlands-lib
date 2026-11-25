/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Weil.WeilKoszulJoinGraded
import WeilConjectures.AlgebraicGeometry.Weil.WeilKoszulJoinBijectivePositive
import WeilConjectures.AlgebraicGeometry.Weil.WeilKoszulJoinBijectiveNonpositive

/-! # Bijectivity of graded exterior multiplication

Source: Stacks Project, More on Algebra, Tag 0664.
(blueprint: lem-weil-pbc-koszul-join-graded-bijective).
-/

@[expose] public section

set_option autoImplicit false

universe u

namespace AlgebraicGeometry.Scheme

/-- Exterior multiplication is bijective in each degree, independently of any differential.

Source: Stacks Project, Tag 0664, lemma-join-sequences-koszul-complex.
(blueprint: lem-weil-pbc-koszul-join-graded-bijective).

Proof: for i > 0 every tensor summand has a positive-degree factor and hence is zero;
the target is also zero. For i = -n, only summands (-j,-k) with j+k=n contribute.
The first exterior factor has rank one, so j is 0 or 1. Identify its exterior
powers in these degrees with A by the empty wedge and the first basis vector.
The two surviving summands are the tail exterior powers of degrees n and n-1
(the latter absent at n=0). Multiplication includes the former as wedges without
e_0 and sends the latter to e_0 wedge the tail wedge. The ordered subset bases
of these two summands partition the full exterior basis, so the map is bijective.
At n=0 it is scalar multiplication A tensor A to A; when n>r+1 both bases are
empty. This argument works over the zero ring, for r=0, and in all characteristics. -/
theorem koszulJoinGraded_bijective {A : Type (u + 1)} [CommRing A]
    (r : ℕ) (a : Fin (r + 1) → A) (m : ℕ) (i : ℤ) :
    Function.Bijective (koszulJoinGraded r a m i).hom := by
  by_cases hi : i ≤ 0
  · exact koszulJoinGraded_bijective_of_nonpositive r a m i hi
  · exact koszulJoinGraded_bijective_of_pos r a m i (by omega)

end AlgebraicGeometry.Scheme
