# Finiteness of flat locally quasi-finite closed subgroups

This derived internal module proves finiteness of a flat locally quasi-finite
closed subgroup of a group of multiplicative type over an arbitrary scheme.
It does not assume that the subgroup has already been proved to be of
multiplicative type.

## Statements and construction

Work in any universe `u`. Let `S` be an arbitrary scheme and `H` an actual
group scheme over `S`. Assume that `H → S` is flat and locally quasi-finite.

For a finitely generated abelian group `Λ` and an actual closed subgroup
homomorphism `i : H → D_S(Λ)`, `closedSubgroupValuativeLift` constructs a
`LiftStruct` for every valuative commutative square for `H → S`. Its output
is an actual scheme morphism from the valuation-ring spectrum to `H`, with
both required triangle equalities.

The theorem `isFinite_of_flat_closedSubgroup` deduces that `H → S` is finite.
`IsDiagonalizable.isFinite_closedSubgroup` gives the same conclusion when
the ambient group is supplied by an isomorphism with a split model.
Finally, `IsMultiplicativeType.isFinite_closedSubgroup` proves it for a
multiplicative-type ambient group, with no restriction on `S`.

There is no nonempty-base, reducedness, noetherianity or subgroup-finiteness
hypothesis. Flatness and local quasi-finiteness of `H → S` are explicit
assumptions. Finite generation is part of the Library's relative
diagonalizability and multiplicative-type conventions.

## Implemented proof

Consider a valuative square with valuation ring `R`, fraction field `K`
and bottom map `b : Spec R → S`. Base-change the actual inclusion along `b`.
The canonical diagonalizable base-change comparisons identify the ambient
group with `D_R(Λ)`. The subgroup remains closed, flat and locally
quasi-finite. It is affine, since its ambient scheme is affine and its
inclusion is closed.

A valuation ring is an integral domain. The supporting
`Diagonalizable.isFinite_of_flat_closedSubgroup` therefore applies to this
base-changed group: the domain reconstruction identifies it with the
split group on its full coordinate character group, and local
quasi-finiteness forces finiteness. This invokes only the domain theorem;
it makes no claim that arbitrary-base flat coalgebras have linearly
independent group-like elements.

The base-changed group is finite and hence universally closed. Mathlib's
valuative criterion supplies a lift for the induced square over `Spec R`,
whose bottom map is the identity. Composing with the first pullback
projection produces the required lift of the original square. The two
triangle equalities follow from the lift equalities and the pullback
condition.

For the global finiteness theorem, the closed inclusion into `D_S(Λ)`
makes `H → S` affine, hence quasi-compact and separated. The constructed
lifts imply universal closedness. Finite generation of `Λ` makes the
ambient structure map locally of finite type; composition with the
closed inclusion gives this property for `H → S`. This step is explicit:
Mathlib's `LocallyQuasiFinite` convention alone does not imply local
finite type. Thus the structure map is proper and affine, hence finite.

An isomorphism of ambient groups transports the closed inclusion and
reduces the relatively diagonalizable case to the split case. For a
multiplicative-type ambient group, use its actual fppf splitting cover.
Flatness, local quasi-finiteness and closedness pass to every pullback.
The split result proves each pulled-back structure map finite, and the
published fpqc/fppf finite-descent interfaces descend this conclusion.
The same argument includes empty schemes and empty members of the cover.

## Provenance and scope

This is a derived construction from the actual subgroup/base-change
interfaces, the supporting domain closed-subgroup reconstruction,
Mathlib's valuative criterion and proper-affine finiteness theorem, and
the published finite-morphism descent results. No additional literature
claim is used.

For the host fibrewise central-isogeny problem this supplies kernel
finiteness once the actual flat locally quasi-finite kernel is embedded
as a closed subgroup of a multiplicative-type centre. Existence of that
centre and global centrality of the kernel remain separate obligations.
This module does not prove the full fibrewise criterion or the general
multiplicative-type closed-subgroup structure theorem.
