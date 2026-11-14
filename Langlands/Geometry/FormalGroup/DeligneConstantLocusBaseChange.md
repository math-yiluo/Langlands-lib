# Base change of constancy on the actual Pi-zero loci

This derived compatibility proves preservation of condition (a) in Drinfeld
1976, Section 2 A, printed p.110 (PDF p.4), opening paragraph. The source is
`drinfeld-1976-coverings-p-adic-symmetric-regions`, SHA256
`7dd09e1967f46c29195ec87a400e145a17374368fc3b9dd0a782b5b7bfc44e2f`.
The source requires the restriction of the homogeneous lattice sheaf eta^i
to the set S_i of zeros of Pi on the i-th tangent line to be constant with
fibre O^d. The actual restriction and constancy predicate used here are
those of `DeligneAdmissibility`.

The parameters are a commutative ring O, a positive integer d, an element
pi of O, an O-algebra field F, schemes S and S', and an arbitrary scheme
morphism f : S' -> S. All are in the same universe. D is the existing
`SheafPreDatum` over a ring map O -> Gamma(S, top). Its actual pullback
is the construction in `DelignePreDatumBaseChange`; its lattice components
are ordinary inverse images and its tangent components are the actual
structural pullbacks. No flatness, nilpotence or finite-presentation
hypothesis is needed for the result here.

## The square of subspaces

`SheafPreDatum.piZeroPullbackMap` is the existing continuous map of actual
Pi-zero-locus subspaces, applied to D's tangent line sheaf. Its point map
is x -> f(x), with membership established by the actual fibre-vanishing
equivalence in `DeligneZeroLocusBaseChange`.
`piZeroPullbackMap_inclusion` proves that this map commutes with the two
subspace inclusions and the original base map. The proof is pointwise
reflexivity. These are the actual subspace topologies; no scheme structure
on S_i is introduced.

## Comparison and transport

`componentOnPiZeroLocusPullbackIso` compares the restriction to S'_i of
the actual pulled eta^i with the inverse image along S'_i -> S_i of the
original restriction. The first inverse-image composition isomorphism
identifies restriction after base change with inverse image along
S'_i -> S' -> S. Equality of the continuous composites from the square
transports this object to inverse image along S'_i -> S_i -> S.
The inverse of the second composition comparison gives the displayed
isomorphism. These composition comparisons are the actual
`inverseImageCompIso` obtained from the inverse-image adjunctions; no
comparison is assumed as input.

`SheafPreDatum.ConstantOnPiZeroLoci.pullback` proves that if D satisfies
condition (a), then its constructed pullback satisfies condition (a).
For each i, it chooses an isomorphism witnessing the original constancy,
applies ordinary inverse image along S'_i -> S_i, and composes with the
comparison above and `inverseImageConstantIso`. The last isomorphism
identifies inverse image of the constant O^d sheaf with the constant
O^d sheaf on S'_i. The proof returns existence of an isomorphism; it
does not add a chosen trivialization to the preliminary data.

The source motivation is condition (a). The proof is derived directly
from the constructed zero-locus map, inverse-image composition and
preservation of constant sheaves, and may be applied to actual Nilp
bases. This unit does not prove transport of condition (b), determinant
normalization (c), full admissibility, a moduli functor, or
representability. It does not assert the special-formal-module
construction or Proposition 2.4 on printed p.110.
