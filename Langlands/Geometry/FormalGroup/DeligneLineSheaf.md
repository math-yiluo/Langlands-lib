# The line-sheaf part of Deligne's data

Drinfeld (1976), §2 A, printed p.109 (PDF p.3), describes the T-part of
Deligne's data as a Z/dZ-graded sheaf of O_S[Π]-modules whose homogeneous
components are invertible. Printed p.110 (PDF p.4), condition (a), uses
the zero loci of the degree-one maps Π:T^i→T^(i+1). This module builds
that line-sheaf part and the underlying point sets of those loci.

The construction uses the actual graded module sheaves of `DelignePiSheaf`.
A homogeneous morphism is a genuine linear sheaf map that commutes with Π
and preserves every homogeneous subsheaf. These morphisms form a category.
Restriction to any homogeneous component is a functor, and the resulting
component maps commute with Π. In particular a graded isomorphism induces
actual isomorphisms on all components.

`schemeScalar` restricts a global structure-sheaf section a to all opens.
For a scheme S, `IsLineSheaf S M` means that every point has an open
neighbourhood on which the actual sheaf M is isomorphic to the structure
module. The implementation proves invariance under an actual isomorphism
by restricting that isomorphism and composing the local trivializations.
`LinePiSheaf` requires this property for every homogeneous component of a
`GradedPiSheaf d S.sheaf (schemeScalar S a)`, for nonzero d. Its quotient
by actual graded isomorphisms is constructed. In the intended nilpotent
algebra application, S is Spec B and a is the image of the uniformizer;
the present construction allows any scheme and any global section.

`fibreComponent` and `fibrePi` are the actual pullbacks to Spec of the
residue field at a point. `piZeroLocus i` is the set of points where the
pulled-back degree-i map is zero. Its invariance under graded isomorphism
is proved by the component naturality square, functoriality of pullback,
and cancellation of the resulting isomorphism. No closed subscheme
structure, closedness assertion or covering assertion for these sets is
included here.

This is a derived formulation of the T-data in the cited source: giving
an operator with Π^d=a on an actually decomposed module sheaf supplies the
quotient action by the previously constructed evaluation map. It imposes
none of the additional conditions involving η, u or the rational frame r,
and makes no claim to construct the full Deligne point functor or its PGL
action. No representing or universal object is an input.
