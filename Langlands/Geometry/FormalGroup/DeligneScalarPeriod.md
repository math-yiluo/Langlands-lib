# The actual scalar uniformizer period of Deligne's four data

This module constructs an actual isomorphism undoing the combination of
a grading shift by d and a scalar pi inverse reframe. Both total sheaf
maps are identities; component maps are actual transports of the cyclic
indices. Preservation of the rational frame follows from the previously
proved identity for the actual rational operator, `Pi^d = pi`.

The source motivation is V. G. Drinfel'd, *Coverings of p-adic symmetric
regions* (1976), Section 2 A, printed pp.109–110 (PDF pp.3–4). The source
defines the quotient coefficient algebra with relation `Pi^d = pi`, its
cyclic grading, and Deligne's four data on a scheme where pi is nilpotent;
the representability theorem identifies the relevant action on Deligne's
factor with a projective linear action. The registered source is
`drinfeld-1976-coverings-p-adic-symmetric-regions`, SHA256
`7dd09e1967f46c29195ec87a400e145a17374368fc3b9dd0a782b5b7bfc44e2f`.
The period isomorphism below is derived infrastructure for that action,
not a separately attributed source theorem.

## Hypotheses and zero-degree transport

All carriers share universe `u`. The constructions assume `NeZero d`.
For a graded Pi sheaf over any sheaf of commutative rings,
`GradedPiSheaf.shiftTrivialIso M k hk`, where `hk : k = 0` in `ZMod d`,
uses the identity on the actual total Pi sheaf in both directions.
Its homogeneous-map obligations use `i + k = i`, so the identity
preserves the transported homogeneous subsheaves. Extensionality proves
the inverse equations.

For a lattice, `O` is any commutative ring, `pi : O`, and `X : TopCat`.
`LatticePiSheaf.shiftTrivialIso M k hk` has total identity and component
map `eqToHom` induced by `i + k = i`. The existing component-transport
identity proves its inclusion squares. Equality on total maps proves
its two inverse equations. These auxiliary constructions apply to any
zero cyclic shift; they extend the previously available integer-zero
comparison to a supplied zero cyclic degree.

## The frame and the actual Pi power

Let `F` be a field with an `O`-algebra structure and assume only
`hpi : algebraMap O F pi ≠ 0`. For a framed lattice `M`,
`FramedLatticePiSheaf.uniformizerInverseReframeIso M hpi` constructs

```text
(M.shiftInt F hpi (d : Z)).reframe F
  (scalarReframeHom d F (Units.mk0 (algebraMap O F pi) hpi)⁻¹) ≅ M.
```

Its lattice isomorphism is the zero-degree comparison because the
integer d maps to zero in `ZMod d`. The proof uses
`isoOfTotalFrame`, checking the frame in the actual total rational
lattice. Rationalization of the total identity is the identity.
The integer-shift formula identifies the shifted total frame with the
original frame followed by `rationalPiAut^d`. The imported
`rationalPiAut_pow` identifies this automorphism with actual scalar pi
multiplication. The constant-sheaf comparison identifies the inverse
scalar reframe with actual scalar pi inverse multiplication on constant
vectors. Scalar naturality moves scalar pi across the frame; the product
pi inverse times pi equals one. This proves the total frame square,
and the existing split-inclusion argument supplies the actual
degree-zero frame square.

Although named for its intended application to a uniformizer, this
construction requires only nonzero image of pi. No discrete valuation,
injectivity of the coefficient map, or nilpotence premise is needed.

## The full four-data isomorphism

For any scheme `S`, structural map `phi : O → Γ(S, top)`, and preliminary
four datum `D`, the selected definition
`SheafPreDatum.uniformizerInverseReframeIso D hpi` constructs

```text
D.shiftReframe hpi
  (scalarReframeHom d F (Units.mk0 (algebraMap O F pi) hpi)⁻¹) (d : Z) ≅ D.
```

The lattice part is the preceding genuine framed isomorphism; the
tangent part is the zero-degree transport isomorphism. On both total
sheaves the maps are identities, so both u squares follow from the
identity laws for the actual scalar-forgetting functors. Extensionality
on the lattice and tangent parts proves the two inverse equations in
the full four-data category. The isomorphism is constructed for every
preliminary datum, without an admissibility assumption.

## Remaining scope

This module constructs the uniformizer period. It does not yet identify
this operation with the normalized action on admissible classes or
prove triviality for every field scalar. The integral-unit isomorphisms
are in the preceding scalar-isomorphism module. Combining the two cases
using the coefficient valuation and group laws, constructing the PGL
quotient action, arbitrary base-change comparison, the complete Nilp
functor, and representability remain further work. No representing or
universal object is assumed.
