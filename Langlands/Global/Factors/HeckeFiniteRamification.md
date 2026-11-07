# Finite ramification of actual Hecke characters

Worker 1692, supporting work for the proof of
`Langlands.Global.HeckeGlobalFunctionalEquationStatement`.

This module constructs the actual inclusion of the product of completed local
integer units into full ideles, with all infinite coordinates equal to one. It
proves that every actual Hecke character is unramified outside a finite set.
The predicate is the existing `HeckeCharacter.IsUnramifiedAt`; no local or
global analytic conclusion is assumed.

The proof first treats a continuous complex character on an arbitrary product
of topological groups. The inverse image of the ball of radius one half about
one contains a product neighborhood constraining only finitely many coordinates.
For a coordinate outside that finite set, every power of each single-coordinate
element belongs to the neighborhood. The published elementary complex-number
lemma `complex_eq_one_of_forall_norm_pow_sub_one_lt` then shows that its
character value equals one. This argument needs neither local compactness nor
an open kernel for the entire product.

For a number field in arbitrary universe `u`, `integralProductMap` is the
literal restricted-product inclusion of the product of completed integer rings.
The units-of-product equivalence, followed by this ring map on units and the
published `finiteIdelesInclusion`, gives `integralUnitIdeles`. Its continuity
uses the restricted-product structure map and the actual units topology,
including continuity of the inverse coordinates. The comparison for a single
local integral unit is proved coordinate by coordinate. Applying the product
lemma to the pullback of the actual Hecke character proves the result.

This is an internal derived lemma for the finite exceptional set in Tate,
*Number theoretic background* (1979), §3.5, printed pp.15–16, specifically the
finite product of local constants in (3.5.2) and Theorem 3.5.3. The registered
original `tate-1979-number-theoretic-background` was read at printed pp.12–17.
This module proves only the multiplicative character's finite ramification.
The additive conductor, normalization of local Haar measures, convergence,
continuation and global functional equation remain separate obligations.
