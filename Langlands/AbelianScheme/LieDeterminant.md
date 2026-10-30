# Determinants of actual order actions on abelian-scheme Lie modules

This internal specialization constructs local determinant polynomials from an
actual ring action on an actual abelian scheme. The acting ring `O` need not be
commutative or finite; in a PEL application it is the chosen integral order.
The scheme, abelian scheme, module and chart index lie in universe `u`, while
the ring and finite variable index may lie in independent universes `v` and `w`.

For `A` over `S` and a unital ring homomorphism `α : O → End A`,
`lieOrderAction` composes `α` with the published `lieEndAction`. The latter is
the actual differential functor on abelian-scheme endomorphisms. The
`lieLocalOrderAction` restricts those sheaf maps to an open `U`, and
`lieSectionOrderAction` evaluates them on actual Lie sections on each smaller
open `V`. These are ring homomorphisms. Their action on a section is exactly
evaluation of `lieMap (α a)`, and their restriction compatibility follows from
the naturality of the actual module-sheaf maps.

For a finite family `a : ι → O` and any finite sheaf trivialization `e` of the
actual Lie module on `U`, `lieSectionDeterminant` uses `LocalSectionDeterminant`
on the constructed local action. Its polynomial is computed from matrices in
the actual section basis. Agreement with every finite section basis follows
from arbitrary commutative ring basis independence. On an open `T` contained
in two possibly different chart opens, the two polynomials are equal: both
families of section endomorphisms reduce to the same differential action on
`T`, and basis independence compares their actual bases. This overlap statement
does not assume the charts have the same index type or open.

Restriction to a smaller open is the polynomial coefficient map of the actual
structure-sheaf restriction. Evaluation at any family of section scalars is the
intrinsic determinant of their linear combination acting on actual Lie
sections. The polynomial has homogeneous support of degree the number of
generators in the chart. No nonzero-polynomial claim is made.

The module also constructs a covering family of charts for every abelian scheme.
The theorem `lie_hasFiniteLocalBasis` reuses the published proofs that the
smooth relative differential sheaf has finite local bases, pullback to the
identity preserves such bases, and taking the internal dual preserves them.
It retains one common witness for local freeness and finite type.
`lieFiniteLocalBasisData` chooses from this proved existence theorem, not from
an assumed output. Its covering property is the `coversTop` field of the chosen
actual local generator datum. Local freeness makes each generator map an
isomorphism; finite type makes each generator index finite.
`lieFiniteLocalBasisTrivialization` is precisely that isomorphism, and
`lieChartDeterminant` computes the polynomial on its smaller opens. The chosen
cover is not asserted canonical; overlap independence supplies the relevant
independence of local polynomial computations.

Worker 57 derived this module from the actual Lie action, the published local
freeness proofs, and the section determinant construction. It adds no assumption
that the Lie determinant equals a Hodge polynomial and proves no such universal
equality. That equality is a separate condition on PEL moduli objects.
Arithmetic integrality, polarizations, level structures and moduli
representability remain separate mathematical obligations.
