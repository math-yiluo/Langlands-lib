# Actual integer Pi paths and framed Deligne shifts

This module constructs shifts by every integer of the actual framed Deligne
lattice and all four preliminary sheaf data. Its negative paths are constructed
inverses of the actual positive return paths. The resulting functors act on
genuine morphisms and preliminary isomorphism classes. The module computes
the actual stalk frames, translated lattices and determinant normalization.

## Source and provenance

The source input is V. G. Drinfeld, *Coverings of p-adic symmetric regions*
(1976), Section 2 A, printed pp.109–110 (PDF pp.3–4), registered as
`drinfeld-1976-coverings-p-adic-symmetric-regions`, SHA256
`7dd09e1967f46c29195ec87a400e145a17374368fc3b9dd0a782b5b7bfc44e2f`.
The end of p.109 specifies the cyclically graded coefficient algebra
`O[Pi] = O[X]/(X^d - pi)`, flat lattice eta, invertible tangent summands,
homogeneous map u, and the start of the rational-frame datum. The beginning of
p.110 completes the rational degree-zero frame and gives conditions (a), (b)
and (c). The formula in (c) ranges over **all integers** i and multiplies by
`pi^(-i)` **after** taking the d-th exterior power.

The integer paths, shifts and transformation identities are derived
infrastructure for these data. They are not separately stated theorems of the
article. The module imports `DeligneFramedShift`, retaining its actual
positive paths and the underlying constructions in `DeligneHomogeneousPi`,
`DeligneGradingShift`, `DeligneDeterminantLattice` and
`DeligneFrameDeterminant`. No representing object, universal object or
uniformization is assumed.

## Hypotheses and convention

All objects use the common universe u. The construction uses a commutative
ring O, an element pi, a nonzero natural number d, a topological space X,
and a field F with its actual O-algebra structure. The explicit hypothesis
`algebraMap O F pi != 0` makes the existing rational Pi maps invertible.
The component transport and index-arithmetic lemmas do not require nonzero d.
The lattice object retains its actual flat-stalk condition. The algebraic
arguments do not require O to be a local ring or a nilpotent element on X.
For the four-data construction, X is the underlying space of a scheme S and
`phi : O -> Gamma(S, top)` supplies its structural O action.

The shift parameter z is an arbitrary integer. New degree i is old degree
`i+z` in `ZMod d`. The total coefficient sheaf and its Pi operator are
unchanged. Integers that have the same cyclic image still give different
rational frames in general; the frame uses the integer Pi power.

## Actual integer component paths

`LatticePiSheaf.rationalTransport_inclusion` shows that the canonical
transport between equal rational-component indices respects their actual
inclusions. `rationalTransport_naturality` proves its naturality for the
component maps of every genuine homogeneous lattice morphism.

For a negative integer `z = -(n+1)`, `negativeReturn_degree` proves
`(i+z)+(n+1)=i` in the cyclic index group.
`rationalNegativeReturnIso F hpi i n` is the actual positive path of length
n+1 from component i+z, followed by this canonical index transport, ending
at component i. It uses the rational isomorphisms already constructed from
the integral complementary path and the inverse image of pi.

`rationalPiIntIso F hpi i z` uses the positive length-n path when z is the
nonnegative integer n, with canonical transport from its natural-number
index to its integer index. For negative z it uses the **inverse** of
`rationalNegativeReturnIso`. Thus both inverse equations come from actual
constructed isomorphisms, rather than extra inverse data.

`rationalNegativeReturnIso_inclusion` compares the return path followed by
the actual inclusion with inclusion followed by the total positive Pi
power. `rationalPiIntIso_inclusion` proves, for every integer z,

`PiPath(i,z) ; inclusion(i+z) = inclusion(i) ; Pi^z`.

In the negative branch the proof precomposes with the positive return
isomorphism, uses its proved inclusion equation and cancels the total
positive power with its inverse. This argument does not assume that
rationalization preserves monomorphisms. Likewise,
`rationalNegativeReturnIso_naturality` combines positive naturality with
index transport; `rationalPiIntIso_naturality` derives the negative square
by the inverse equations. Naturality holds for every genuine homogeneous
lattice morphism, not only isomorphisms.

## Constructed framed and four-data functors

`FramedLatticePiSheaf.shiftInt F hpi z` has underlying lattice shifted by
the cyclic image of z and frame

`M.frame ; M.lattice.rationalPiIntIso F hpi 0 z`.

`shiftIntMap` uses integer-path naturality to construct the actual
frame-preserving morphism. `shiftIntFunctor` supplies identity and
composition laws, using extensionality of actual lattice morphisms.
`frameToTotal_shiftInt` identifies the constructed frame in the unchanged
total rational sheaf with the original frame followed by the actual Pi^z.

`SheafPreDatum.shiftInt hpi z` shifts eta and the tangent grading by the
same cyclic index, retains the actual total u, its Pi compatibility and
local generation, and reindexes its specified homogeneous maps.
`shiftIntMap` and `shiftIntFunctor` construct the functor on all four
preliminary data. `SheafPreDatum.IsoClass.shiftInt` descends it to the
existing quotient by genuine four-data isomorphisms.

## Actual stalk and determinant identities

`rationalPiStalkAut_zpow_hom` applies preservation of integer powers by the
automorphism-group homomorphism of the actual sheaf-to-presheaf and stalk
composite functor. Naturality of the germ map then proves
`frameStalkMap_shiftInt`. Restriction to O-valued coordinate vectors gives
`integralFrameStalkMap_shiftInt`; taking its actual linear-map range gives
`frameStalkLattice_shiftInt`:

`frameStalkLattice(shiftInt M z, x) = Pi^z r O^d`.

Composition of submodule images and addition of integer powers proves
`translatedFrameStalkLattice_shiftInt`, for all integers i and z:

`translatedFrameStalkLattice(shiftInt M z, i, x)`
`  = translatedFrameStalkLattice(M, i+z, x)`.

`normalizedFrameDeterminant_shiftInt` retains the literal normalization:

`normalizedFrameDeterminant(shiftInt M z, i, x)`
`  = pi^z * normalizedFrameDeterminant(M, i+z, x)`.

Here scalar powers are in F, and `*` denotes `scaleStalkLattice`, the image
of the already formed exterior lattice under scalar multiplication. The
proof substitutes the translate formula, composes these scalar maps and
uses `pi^z pi^(-(i+z)) = pi^(-i)`. It does not place the scalar inside the
exterior power.

## Conditions and boundary

`piQuotientResidueMap_shiftInt` and
`residueFibreInjective_shiftInt_iff` show that the total residue map and
condition (b) are unchanged. `piZeroLocus_shiftInt` translates the actual
tangent Pi-zero locus and `componentDeterminant_shiftInt` reindexes the
actual component determinant. `constantOnPiZeroLoci_shiftInt_iff` proves
condition (a) in both directions: each actual subspace restriction is the
old one at i+z, and cyclic translation is a bijection.

`determinantNormalized_shiftInt_iff` gives the exact condition (c) after
an integer shift. At every integer i and point of the old zero locus at
i+z, the required equality is the old component determinant at i+z equal
to pi^z times the old normalized frame determinant at i+z.

This unit supplies arbitrary integer shifts and their determinant law.
It does not claim unconditional preservation of condition (c) or full
admissibility. Zero/addition comparisons and inverse equivalences of the
framed functors, the normalized GL/PGL action and its central laws,
compatibility with base change, an independent exterior-subsheaf comparison,
and representability remain outside this unit.
