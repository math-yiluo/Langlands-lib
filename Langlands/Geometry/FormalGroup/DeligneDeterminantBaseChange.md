# Actual determinant normalization under base change

This module constructs the exterior-power comparison between the actual total
rational determinant stalks and proves that the previously defined
`SheafPreDatum.DeterminantNormalized` predicate is preserved by scheme base
change. The component determinants and normalized frame determinants are
transported by the same actual comparison.

## Source and scope

The source motivation is V. G. Drinfeld, *Coverings of p-adic symmetric regions*
(1976), Section 2 A, printed pages 109–110 (PDF pages 3–4). The definition of the
four data ends at the page boundary with the rational frame r. At the beginning
of page 110, condition (c) compares the determinant of eta^i with
pi^(-i) wedge^d(Pi^i r O^d) on S_i, for every integer i. The source is registered
as `drinfeld-1976-coverings-p-adic-symmetric-regions`, with content SHA-256
`7dd09e1967f46c29195ec87a400e145a17374368fc3b9dd0a782b5b7bfc44e2f`.
These transport constructions and proofs are derived infrastructure for that
condition, using the literal stalk lattices already defined in
`DeligneDeterminantLattice`.

The general exterior and scalar transport results assume a commutative ring O,
an O-algebra field F and an F-linear map between F-modules. The translated-frame
results additionally use a positive natural number d, an element pi of O with
nonzero image in F, a continuous map f : X → Y and an actual
`FramedLatticePiSheaf` on Y. Its existing flat graded Pi-algebra lattice and
rational frame are retained. The final results take an actual `SheafPreDatum`
on a scheme S, with coefficient map O → Γ(S, top), and any scheme morphism
f : S' → S. All these data use the common universe of the imported Deligne
modules.

The comparisons are constructed from the actual inverse-image, rationalization
and stalk functors. No comparison equation, determinant normalization of the
pulled datum, representing object or universal object is supplied as extra
input. There is no flatness or surjectivity assumption on f and no nilpotence
assumption needed for these transport results.

The conclusion concerns the existing all-integer stalkwise normalization
predicate. This module does not prove integral injectivity, a tensor/stalk
comparison or equivalence with an independently constructed exterior-power
subsheaf equality. It does not combine conditions (a), (b) and (c) into the full
admissible moduli functor, construct the PGL action, or prove representability.

## Exterior products and scalar multiplication

`exteriorStalkMap F k g` is Mathlib's actual k-th exterior-power linear map,
packaged as an F-module morphism. The exterior powers are formed over F.
`exteriorStalkLattice_map` restricts that map to O-scalars and proves

    map (wedge^k g) (exteriorStalkLattice k V L)
      = exteriorStalkLattice k W (map g L).

Here `exteriorStalkLattice` is the O-span of the actual exterior products of
k vectors in L. The proof first uses the fact that a linear map sends a span
to the span of its image. It then identifies the generating sets: a tuple in
L maps to a tuple in its image; conversely, choose in L a representative of
each member of a finite tuple in the image. The defining exterior-map formula
identifies their products. This argument needs neither injectivity nor
surjectivity of g.

`scaleStalkLattice_map` proves that mapping the image of L under multiplication
by a scalar a of F gives multiplication by a of the image of L. The proof
composes the O-linear image maps and uses F-linearity of g. In particular, the
O-scalar restriction is applied after the exterior construction, and scalar
normalization is applied after the exterior lattice is formed.

## Translated frame determinants

`FramedLatticePiSheaf.translatedFrameStalkLattice_pullback` transports the
actual lattice Pi^n r O^d for every integer n. The proof restricts
`rationalPiStalkAut_zpow_pullback` to O-scalars, composes the submodule maps
and substitutes `frameStalkLattice_pullback`. Thus the actual pulled frame
lattice is identified using the already proved frame comparison; it is not
defined by the desired equality.

`normalizedFrameDeterminant_pullback` applies scalar transport, exterior
transport and the translated-frame equality in that order. The scalar
(algebraMap O F pi)^(-n) is the same on both bases. The result is equality of
the images of the literal normalized lattices for every n in the integers,
including negative n.

## Actual determinant comparison and normalization

`SheafPreDatum.determinantStalkPullbackMap` takes the d-th exterior power of
`rationalLatticeStalkPullbackIso` at x. Its source is the actual total rational
determinant stalk of D at f(x), and its target is that of the actual datum
`D.pullback f` at x.

`componentDeterminant_pullback` proves that the O-linear image of each original
component determinant under this map is the corresponding component determinant
of the pulled datum. The proof applies the general exterior transport identity
and the actual `componentStalkLattice_pullback` equality.

`DeterminantNormalized.pullback` assumes the original normalization predicate
and proves it for `D.pullback f`. For each integer n and each x on the pulled
Pi-zero locus, `LinePiSheaf.piZeroLocus_pullback` places f(x) on the original
Pi-zero locus. Apply the original determinant equality there, map both sides
by `determinantStalkPullbackMap`, and substitute the component and normalized
frame transport identities. This proves preservation of the actual existing
predicate for all integers and all points of the required loci. Reflection or
descent of this predicate is not asserted.
