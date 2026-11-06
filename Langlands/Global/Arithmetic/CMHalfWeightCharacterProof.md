# Conjugate-inverse weight-one characters on CM fields

Authors: Worker 1692 and Worker 1690.

`Langlands.Global.cmHalfWeightCharacter` proves the unchanged Library proposition
`Langlands.Global.CMHalfWeightCharacterStatement.{u}`. For every CM number field
`K : Type u`, every integral infinity type `t` of pure weight one, and every
finite set `S` disjoint from its arithmetic conjugate, it constructs a Hecke
character `φ` with conjugate-inverse symmetry, the exact twist

`φ.atInfinity(x) * ∏τ |xτ| = InfinityType.toCharacter t x`,

and unramifiedness at every place of `S`. No additional class-field or
extension hypotheses are retained in the theorem.

The source is Harris–Taylor, *The Geometry and Cohomology of Some Simple
Shimura Varieties* (2001), proof of Corollary VII.2.8, printed pp.244–245
(PDF pp.252–253). Registered source:
`harris-taylor-2001-geometry-cohomology-simple-shimura`, SHA-256
`5be28164b61d6f6cc28dd9e6b990d669504f3470860b230ebbc97e3da10af56b`.
The proof below uses actual norm images and open neighborhoods as an internal
refinement of its finite-unit and sign compatibility argument.

Write `F` for the actual maximal real subfield of `K`. The normalized infinity
character `η = normalizedCharacter t` is the algebraic infinity character
divided by the product of ordinary complex absolute values. Worker 1690's
`CMHalfWeightInfinity` supplies its twist formula; `CMHalfWeightRealSign`
identifies its value on a principal element of `Fˣ` with the sign of the
rational field norm. `CMHalfWeightNormInfinity` proves that the pulled-back
infinity character is trivial on actual idele norms from `K` to `F`, after
inclusion back into `K`.

This module defines `supportedIntegralIdeles S`: ideles integral at every
finite place, with infinity projection one and finite coordinates one outside
`S`. It then defines `normAndSupportClasses S` as the join of their image in
the actual idele-class group with the range of
`ideleClassInclusion ∘ ideleClassNorm`. The actual Galois product formula and
the quadratic Galois group `{1, c}` show that this subgroup contains
`x * c(x)` for every class `x`. It also contains the image of every local
integral unit at the places of `S`.

`exists_principal_norm_support_of_mem` translates membership in this subgroup
into an actual idele factorization

`x = diagonalUnits K a * ideleInclusion (ideleNorm y) * s`,

where `s ∈ supportedIntegralIdeles S`. The join is the product of the two
subgroups because the idele-class group is commutative. Choosing an idele
representative for the norm class and lifting equality of quotient classes
produces the principal factor `a`.

`exists_open_subgroup_principal_norm_pos` intersects the open subgroup from
`CMHalfWeightFiniteControl` with that from `CMHalfWeightLocalNormControl`.
Both contain the entire infinity factor. In a factorization lying in this
intersection, the included norm is fixed by the actual CM involution.
The first subgroup therefore forces `a` to be real. The fixed-field theorem
writes it as the image of `aF : Fˣ`.

The second subgroup makes every finite coordinate of
`diagonalUnits F aF * ideleNorm y` a local norm. The quadratic norm-component
lemma makes the corresponding coordinate of `ideleNorm y` a norm from the
same selected completion. Dividing these witnesses makes `aF` a norm at
every finite place. `CMFiniteNormSign.norm_pos_of_finiteLocalNorm` then proves
that its rational norm is positive. That imported theorem discharges its
reciprocity input using proved local class formation, global reciprocity and
idele-class H1 vanishing; no unproved reciprocity premise is assumed here.

`exists_open_subgroup_normAndSupport_kernel` now proves the necessary
compatibility: the normalized infinity character of every such factorization
is one. Its principal-factor value is one by positive rational norm, its
included-norm value is one by the norm-infinity lemma, and its supported-factor
value is one because that factor has trivial infinity projection.

Finally, Worker 1690's `exists_heckeCharacter_of_open_kernel` descends this
character on the open subgroup to the quotient by `normAndSupportClasses S`
and extends it continuously using the proved complex-character extension
theorem. Killing `x * c(x)` gives conjugate-inverse symmetry; killing the
prescribed local integral-unit classes gives unramifiedness on `S`. Since the
open subgroup contains all infinity ideles, the extension has infinity
component exactly `η`. Its twist formula is precisely the equation of the
Library target, completing the proof at the original universe `u`.
