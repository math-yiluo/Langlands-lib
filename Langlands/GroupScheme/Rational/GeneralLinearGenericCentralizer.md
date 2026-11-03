# Generic cocharacters of the diagonal torus and their centralizers

Worker 176.

This helper proves the generic-centralizer component for the actual diagonal
torus of `GL_n`, over every field `k : Type u` and finite `n : Type` with
decidable equality. It uses the diagonal torus indexed by `ULift.{u} n`,
the actual relative roots and `IsGenericCocharacter`, and the published dynamic
subgroup definitions. It is intended for the final proof bundle of
`GeneralLinearRationalStatement`; it does not prove that entire statement.

It imports the `Torus.Lattice`, `Reductive.RootDatum`, `Torus.Weights`,
`Torus.Maximal`, `Rational.RelativeRoots` and `Dynamic.GeneralLinearOrbit`
interfaces, together with the explicit diagonal-torus root computation in
`Reductive.GeneralLinearRoots`. The proof below combines these concrete
interfaces without assuming the general reductive-group centralizer theorem.

## Implemented proof

`latticePairing_rootDatum_root_fintype` evaluates the pairing of the root attached
to `(i, j)` with a cocharacter `ν` as the difference between the `i` and `j`
coordinates of `cocharacterCoordEquiv n k ν`. The proof rewrites the pairing
as a dot product using `latticePairing_coord`, uses
`characterCoordEquiv_rootDatum_root`, and evaluates that dot product with
`sum_rootCoord_mul`.

`isGenericCocharacter_diagonalTorus_iff` says that the actual genericity
predicate for `diagonalTorus n k` is equivalent to injectivity of the
cocharacter's coordinate function. The forward direction applies genericity
to each root `e_i - e_j`, whose membership follows from
`roots_diagonalTorus`. In the reverse direction, the same root calculation
writes every relative root as a root of the standard root datum; its pairing
is nonzero because distinct indices have distinct weights. This also handles
the empty index type and the one-dimensional case.

`dynamicCentralizer_diagonalTorus_of_isGeneric` uses that injectivity in
`dynamicCentralizer_eq_torusCentralizer_of_injective_weights`. The diagonal
image hypothesis is `pointsEquiv_diagonalTorus_val`, and the cocharacter
factorization is the earlier lattice helper applied to that point formula.
The parent's `centralizer_diagonalCocharacter` supplies the dynamic
block-Levi equality. Distinct weights make its points diagonal, so they
commute with the image of the whole torus. The reverse inclusion is
`torusCentralizer_le_dynamicCentralizer`.

The conclusion is equality of subgroup functors, including on every test
scheme and after every refinement. No rational-point-only test, infinitude
assumption on the field, or representability assumption is added.

## Provenance

This is the derived `GL_n` specialization of Borel–Tits, *Groupes réductifs*
(1965), source ID `borel-tits-1965-groupes-reductifs`, Theorem 4.15(a),
printed pp.90–91 (PDF pp.37–38), and Milne, *Algebraic Groups* (2017), source
ID `milne-2017-algebraic-groups`, Theorem 25.6(b) and its proof,
printed pp.545–546 (PDF pp.561–562).

The coordinate and pairing conventions come from Milne §12.a, printed p.230
(PDF p.246), Theorem 12.9, printed p.233 (PDF p.249), and Example 12.15,
printed p.236 (PDF p.252), via the sibling lattice construction. The
calculation of the actual roots is Worker 274's implementation of Milne
Example 21.6, printed p.426 (PDF p.442). The scheme-level dynamic
block-Levi calculation is the parent's implementation of
Conrad–Gabber–Prasad, *Pseudo-reductive groups*, second edition (2015),
Example 2.1.1, printed pp.45–47 (PDF pp.71–73). This helper combines those
interfaces through the implemented matrix argument; it asserts no general
reductive-group centralizer theorem.

The pairing theorem uses the suffix `_fintype` to distinguish its arbitrary
finite-index-type interface from the `Fin N` theorem in
`GeneralLinearSimpleRootsProof`. Both statements retain their original scope.
