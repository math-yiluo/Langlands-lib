# Actual rational frames on shifted Deligne sheaf data

This module constructs nonnegative grading shifts of the actual framed lattice
and of all four preliminary Deligne sheaf data. The shifted frame is constructed
from the actual rational homogeneous Pi path. The construction is functorial
for genuine homogeneous, frame-preserving morphisms and therefore descends to
preliminary isomorphism classes. It also computes the actual stalk lattices and
the literal determinant normalization after a shift.

## Source and provenance

The source input is V. G. Drinfeld, *Coverings of p-adic symmetric regions*
(1976), Section 2 A, printed pp.109–110 (PDF pp.3–4), registered as
`drinfeld-1976-coverings-p-adic-symmetric-regions`, SHA256
`7dd09e1967f46c29195ec87a400e145a17374368fc3b9dd0a782b5b7bfc44e2f`.
The end of p.109 gives the cyclically graded coefficient ring
`O[Pi] = O[X]/(X^d - pi)` and the lattice, tangent, homogeneous morphism and
rational-frame data. The beginning of p.110 completes the frame and states
conditions (a), (b) and (c). In (c), multiplication by `pi^(-i)` is performed
**after** taking the top exterior power, for every integer `i`.

The finite framed shifts and their transformation formulas are derived
infrastructure, rather than separately stated theorems of the article. They
use the actual grading shifts of `DeligneGradingShift`, the constructed
rational component isomorphisms of `DeligneHomogeneousPi`, and the actual
stalk and determinant lattices of `DeligneDeterminantLattice` and
`DeligneFrameDeterminant`. No representing scheme, universal object or
uniformization is supplied as input.

## Hypotheses and conventions

All coefficient rings, spaces and modules use the common universe `u`.
The general construction has a commutative ring `O`, an element `pi`, a nonzero
natural number `d`, a topological space `X`, a field `F` with an `O`-algebra
structure, and the explicit hypothesis `algebraMap O F pi != 0`.
The two integral naturality lemmas do not need the nonzero-`d` assumption.
For the four-data construction, `X` is the underlying topological space of a
scheme `S`, with the structural ring map `phi : O -> Gamma(S, top)`.
The algebraic arguments need no local-field or nilpotence hypothesis. Thus they
apply, in particular, to the nilpotent bases in the source. The imported actual
lattice object retains its flat-stalk condition.

The parameter `n` is a natural number, including zero. New degree `i` is old
degree `i+n` in `ZMod d`, and the total coefficient sheaf and its Pi operator
are unchanged. All Pi powers below act on the actual total rational lattice
or its actual stalk.

## Constructed frames and functors

`LatticePiSheaf.Hom.component_transport_naturality` verifies naturality of the
actual equality transports between degree indices.
`Hom.piIterate_naturality` proves by induction that a genuine homogeneous
lattice map commutes with every actual integral Pi iterate. Its successor
step uses the transport square and the degree-one Pi square, together with
cyclic-index arithmetic.

`LatticePiSheaf.rationalShiftIso F hpi i n` is the already constructed rational
Pi iterate from component `i` to component `i+n`, viewed as component `i` of
the shifted lattice. `rationalShiftIso_naturality` applies rationalization to
the integral iterate square.
`rationalPiAut_pow_hom` identifies the actual total rational power with the
rationalization of the integral total power. Consequently,
`rationalShiftIso_inclusion` identifies the component path followed by its
actual homogeneous inclusion with the original inclusion followed by the
total rational Pi power. These are equations of actual sheaf morphisms.

For an actual framed lattice `M`, `FramedLatticePiSheaf.shiftNat F hpi n` has
lattice `M.lattice.shift n` and frame

`M.frame` followed by `M.lattice.rationalShiftIso F hpi 0 n`.

The imported component isomorphism supplies both inverse equations; no new
invertibility assumption is imposed on the component map. `shiftNatMap` and
`shiftNatFunctor` use its proved naturality to shift genuine frame-preserving
morphisms. `frameToTotal_shiftNat` identifies the constructed frame into the
unchanged total rational sheaf with the original frame followed by `Pi^n`.

`SheafPreDatum.shiftNat hpi n` shifts both eta and the tangent grading, retaining
the actual total morphism `u`, its Pi compatibility and its local-generation
property, and reindexing its homogeneous component maps. `shiftNatMap` and
`shiftNatFunctor` give the corresponding functor on all four preliminary data.
`SheafPreDatum.IsoClass.shiftNat` is the quotient map supplied by the functor's
transport of genuine four-data isomorphisms.

## Actual stalk and determinant formulas

`rationalPiStalkAut_natCast_hom` uses the automorphism-group homomorphism of
the sheaf-to-presheaf and stalk composite functor to identify positive total
powers on stalks. Naturality of the actual germ map then proves
`frameStalkMap_shiftNat`. Restricting to O-valued coordinate vectors proves
`integralFrameStalkMap_shiftNat`, and taking actual linear-map ranges gives
`frameStalkLattice_shiftNat`:

`frameStalkLattice(shiftNat M n, x) = Pi^n r O^d`.

The existing `translatedFrameStalkLattice` permits every integer translate,
including negative ones. Composition of submodule images and addition of
integer powers give `translatedFrameStalkLattice_shiftNat`, for every
`i : Int`:

`translatedFrameStalkLattice(shiftNat M n, i, x)`
`  = translatedFrameStalkLattice(M, i+n, x)`.

The literal normalization is retained. `normalizedFrameDeterminant_shiftNat`
proves the equality of actual O-submodules

`normalizedFrameDeterminant(shiftNat M n, i, x)`
`  = pi^n * normalizedFrameDeterminant(M, i+n, x)`.

Here `*` means `scaleStalkLattice`: scalar multiplication **of the already
formed determinant lattice**. The proof substitutes the translate formula,
composes the scalar maps, and uses
`pi^n * pi^(-(i+n)) = pi^(-i)` in `F`. It does not move scalar multiplication
inside the exterior power.

## Four-data conditions and scope

`piQuotientResidueMap_shiftNat` and `residueFibreInjective_shiftNat_iff` show
that the total quotient-to-residue-fibre map and condition (b) are unchanged.
`piZeroLocus_shiftNat` translates the actual tangent Pi-zero loci.
`componentDeterminant_shiftNat` reindexes the actual component determinant.
`constantOnPiZeroLoci_shiftNat_iff` proves condition (a) in both directions:
the actual zero-locus subspace and its restricted component sheaf are the old
ones at degree `i+n`, and translation is a bijection on `ZMod d`.

`determinantNormalized_shiftNat_iff` spells out condition (c) for the shifted
four data using these formulas. For every integer `i` and point on the old
zero locus at `i+n`, the required equality is between the old component
determinant at `i+n` and `pi^n` times the old normalized frame determinant at
`i+n`. In particular, this module asserts no unconditional preservation of
condition (c) or full admissibility by a raw shift.

This module constructs nonnegative shifts and their actual determinant
law. It does not construct inverse or arbitrary-integer framed shifts,
zero/addition comparisons of framed shifts, a normalized GL/PGL action, or
its central-scalar laws. Compatibility with base change, an independent
exterior-subsheaf comparison, and formal representability remain outside this
module. The integer variable in the stalk formulas is a translate of a frame;
it does not enlarge the natural-number domain of `shiftNat`.
