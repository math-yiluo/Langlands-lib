# Integral relation descent and positive basis extraction

This module states the integral-lattice steps used to descend paired
generators to their spans and extract positive basis images. These are
proposition definitions; no proof of their truth is supplied here.

The sole project dependency is the independently accepted and published
artifact `b8c38a4e-6268-44a4-b9cd-99d752b42e47`, version 1, module
`Langlands.VirtualRepresentation.Integral`. Its Lean SHA-256 is
`785418baa91b4ed140707b9a2a4acdd05b0f6ef9dab0efe3f271e2fef76a652d`;
its paired Markdown SHA-256 is
`676c34871f15c312e0fed03e9c2231c5109cc98986251ee075afa4c472f0790c`.
Both files match their effective published versions at Library commit
`843c574c920aa9926ab56adf662c74b3cd4ed0e1`.
Worker 24 authored that construction; Worker 30 authored this statement pair.

## Mathematical objects and source

The lattices are the actual modules of finitely supported integer-valued
functions `ι →₀ ℤ` and `κ →₀ ℤ`, with independent basis universes.
`J` indexes paired generators and has a third independent universe.
`pairing` is the sum of products of integral coefficients.
`generated` is the integral submodule span, and `relations` is the actual
kernel of the linear evaluation map from the free lattice on `J`.
`degree` extends a specified natural-number weight linearly to an
integer-valued degree on virtual vectors. The theorems use these concrete
objects, not fields postulating isometry or the desired correspondence.

The original source is Henniart 2000, *Une preuve simple des conjectures
de Langlands pour GL(n) sur un corps p-adique*, §§2.5–2.8,
printed pp.445–448. Literature ID `henniart-2000-simple-proof`; retained
PDF `C:/Central-Library/Henniart--Une preuve simple des conjectures de Langlands pour GL(n) sur un corps p-adique--2000.pdf`;
SHA-256 `be283c3e8187f1eed365537c72379c3e06e7791756954c2ac783c6beea2979de`.
These original passages were read. The generalization here extracts the
elementary integral-lattice argument from the concrete local application.
It does not claim that Henniart states these exact generic Lean types.

## Separated conclusions

The closing `IntegralDescentAndPositivityStatement` conjoins the following
ten reusable component propositions, using the one-lattice components on
each side when appropriate.

| Component after `Langlands.VirtualRepresentation.` | Precisely asserted step |
| --- | --- |
| `IntegralPairingDefinitenessStatement` | The self-pairing is nonnegative, and is zero exactly for the zero lattice vector. |
| `IntegralRelationDescentStatement` | Equality of pairings of paired generators implies equality of their integral-relation kernels. |
| `IntegralGeneratedEquivalenceStatement` | Equal kernels yield a unique linear equivalence of the generated sublattices mapping each specified generator to its partner. |
| `IntegralGeneratedIsometryStatement` | A linear map of these spans respecting the specified generators preserves pairings if the generator pairings agree. |
| `IntegralGeneratedDegreeStatement` | Such a map preserves degrees if the degrees of paired generators agree. |
| `IntegralNormOneSignedBasisStatement` | A norm-one integral vector is a positive or negative basis vector, at a unique index. |
| `IntegralPositiveDegreeBasisStatement` | A norm-one vector of positive degree is a positive basis vector. Natural-number weights suffice; no positivity of every weight is assumed in this component. |
| `IntegralIsometryInjectivityStatement` | An integral linear isometry is injective, without a degree hypothesis. |
| `IntegralIsometrySignedBasisStatement` | Such an isometry induces an injective map of basis indices and signs in `{1,-1}`. |
| `IntegralIsometryPositiveBasisStatement` | If source basis degrees are positive and the isometry preserves degree, all those signs are positive and the basis-index injection preserves the weights. |

The source's §2.8, p.448, expands equality of generator pairings to
equality of self-pairings of all integral combinations. Positive
definiteness then identifies the relations. Descent to generated spans
gives the unique map of §2.5, p.446, and the pairing assertion of
§2.6(b), p.447. The degree assertion is §2.6(a), p.446, justified on
generators in §2.8, p.448.

The norm-one and sign steps are the argument following the corollary in
§2.6, p.447: a sum of squares of integers can equal one only with a
single coefficient equal to `1` or `-1`. An image of a positive-degree
basis vector cannot be a negative target basis vector, since target
weights are nonnegative. Orthogonality of distinct source generators
then prevents their signed images from using the same target index.
The generic injectivity assertion follows from positive definiteness
applied to a vector in the kernel. These are propositions to be proved,
not proofs supplied by this pair.

`IntegralGeneratedEquivalenceStatement` assumes equality of the relation
kernels, whereas `IntegralRelationDescentStatement` has that equality as
its conclusion. Similarly, the two isometry-to-basis statements
explicitly assume an isometry whose existence must be established in
the application. No structure packages those conclusions as already
proved, and no LLC map or equivalence is an input.

## Application boundary

This generic lattice family is a prerequisite, not the entire local
representation theorem. For the Henniart application, `ι` and `κ` must
be instantiated with the actual irreducible Weil and supercuspidal
classes, respectively, across **positive** ranks. The target is not a
ring freely generated by all irreducible admissible `GL_n` classes.
The natural-number weights are those actual ranks.

The global branch must still construct the actual paired weak-association
generators and prove their pairings agree using the local-factor
comparison. The finite-character branch must supply integral Brauer
spanning to put the required finite-image classes into the source
span. Restricting the global isomorphism to such a sublattice can
produce an injection of local basis classes without producing a
surjection onto every supercuspidal class. The finite-witness
choice-independence argument and numerical surjectivity theorem are
therefore separate later obligations. This file makes no finiteness
claim about the full bases or their rank strata.

The environment is artifact `2ecc41bc-2901-4e34-96c5-6d98fbb3c74d`
version 1, Lean 4.34.0 and Mathlib commit
`5ed2965256430c3649e86755f9576b54eca72435`. The only project import is
the concrete `Integral` construction identified above.

All eleven elaborated proposition definitions were printed and inspected
during development, including the subtype coercions for generated spans,
both integer sign alternatives, and the independent `u`, `v`, and `w`
universes. The published dependency has the same source bytes as the
construction used in that check. Compilation and inspection establish
well-formedness of the statements; mathematical proofs remain separate
obligations.
