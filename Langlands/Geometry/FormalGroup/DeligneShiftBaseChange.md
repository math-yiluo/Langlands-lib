# Actual shift and frame comparisons under arbitrary base change

This module constructs isomorphisms comparing integer grading shifts with
actual inverse image of Deligne's preliminary four data. It also proves
that inverse image commutes with rational reframing. The comparisons retain
the actual total lattice, structural tangent module, rational frame and u map.

The source motivation is V. G. Drinfel'd, *Coverings of p-adic Symmetric
Regions* (1976), Section 2 A, printed pp.109–110 (PDF pp.3–4): the graded
four-data description and conditions (a)–(c). Proposition 2.4 on printed
p.110 states base-change compatibility for the data attached to a special
formal module. Registered source: `drinfeld-1976-coverings-p-adic-symmetric-regions`,
SHA256 `7dd09e1967f46c29195ec87a400e145a17374368fc3b9dd0a782b5b7bfc44e2f`.
The shift comparisons here are derived infrastructure on the existing
four-data construction; they do not assert Proposition 2.4 or a comparison
with formal modules.

## Parameters and conventions

All carriers have a common universe u. The parameters are a commutative
ring O, a positive integer d, an element pi of O, and an O-algebra field F.
The integer-shift constructions require that the image of pi in F is
nonzero. Lattice inverse image uses an arbitrary continuous map f: X → Y;
the complete four-data comparison uses an arbitrary scheme map f: S' → S
and an actual map phi: O → Gamma(S, top). The resulting scalar map is the
constructed `pulledGlobalScalar f phi`. There is no flatness, discrete
valuation or nilpotence hypothesis on this base map.

As in the imported shift construction, new degree i is old degree i+k,
and the total lattice and its Pi operator are unchanged. For an integer
k, the rational frame uses the actual homogeneous integer Pi path,
including the inverse positive return path when k is negative. Reframing
precomposes the rational degree-zero frame by an actual F-linear
automorphism of F^d.

## Lattice and frame comparisons

`LatticePiSheaf.inverseImageShiftIso` compares inverse image after cyclic
translation with cyclic translation after inverse image. Both its total
map and its component maps are identities. Their homogeneous inclusions
agree definitionally: both are the pulled inclusion in old degree i+k,
followed by the same coefficient restriction comparison. The identity maps
therefore satisfy the genuine lattice morphism condition in both directions.

`inverseImageRationalLatticeIso_zpow` extends the imported intertwining
of total rational Pi operators to every integer power. The proof maps
automorphisms by the rational inverse-image functor and conjugates by the
actual rationalization comparison. This composite is a group homomorphism.
Its value on Pi is the pulled Pi automorphism by the existing intertwining
identity; preservation of integer powers then gives the asserted equation.
No separate negative-power compatibility is assumed.

`FramedLatticePiSheaf.inverseImage_reframe` is equality of the actual
framed objects. Naturality of the inverse constant-sheaf comparison moves
the frame automorphism through inverse image; the remaining rationalization
comparison and frame maps are identical.

`frameToTotal_inverseImage_shiftInt` compares the two rational frames in
the unchanged total rational sheaf. After cancellation of the constant-sheaf
comparison, the proof uses the imported frame-to-total pullback formula,
the total Pi power formula for the integer-shifted frame, and the preceding
integer-power intertwining theorem.

`inverseImageShiftIntIso` lifts the identity-total cyclic lattice comparison
to the actual framed-lattice category with `isoOfTotalFrame`. Thus it
preserves the full rational frame, rather than only its determinant or its
stalk lattice.

## Tangent and complete four-data comparisons

`GradedPiSheaf.pullbackShiftIso` compares structural pullback after cyclic
translation with translation after pullback. Both maps are the identity of
the actual total Pi-module. The pulled homogeneous components are the
ranges of the pulled inclusions, so reindexing them gives the same
submodules. The identity is homogeneous in both directions; its two
composites are identities.

`SheafPreDatum.pullback_reframe` lifts the framed-object equality to the
complete preliminary four-data structure. Reframing changes only the
rational frame; the tangent data, u and the homogeneous u maps agree.

`pullbackShiftInt_u` proves the actual total-u square for the constructed
framed and tangent comparisons. On their unchanged total sheaves these
comparisons are identities, while the two pulled u maps are the same
coefficient comparison followed by inverse image of the original u and
the structural pullback comparison. The proof reduces to the two functors'
identity laws and the categorical identity-composition laws.

`SheafPreDatum.pullbackShiftIntIso` assembles the preceding framed and
graded isomorphisms and this total-u square with `isoOfComponents`. The
imported assembler derives the inverse u square from the two inverses.
The resulting isomorphism therefore preserves the grading, Pi operator,
full rational frame and u on the actual four data for every integer k.

## Scope

The construction is on preliminary data. Preservation of the existing
admissibility predicate under the relevant operations is available in
separate modules; descent of these comparisons to those classes and
naturality of the projective action on the Nilp functor are subsequent
steps. The independent comparison of the existing determinant predicate
with an equality of exterior-power subsheaves remains open. This module
asserts no representing or universal object, formal-module comparison or
representability theorem.
