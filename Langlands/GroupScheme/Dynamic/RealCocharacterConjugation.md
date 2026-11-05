# Internal Hermitian conjugation over real coefficient fields

Author: Worker 1655.

This internal construction proves scalar-extension comparisons and real
internal cocharacter unitarization. Both coefficient fields have arbitrary
universe `u`, and the matrix index is a finite type in `Type`.

`cocharacterEvalExtensionUnit` evaluates Laurent coordinates at a unit
of a test algebra. Naturality at the universal Laurent unit gives the
finite expansion of the actual cocharacter value as the sum of its
extended projectors multiplied by the unit's integer powers. Extension
preserves projector multiplication and the sum-to-identity relation.
The cocharacter value therefore acts by the corresponding scalar power
on every extended projector.

`HasHermitianExtensionWeightProjectors` says that every actual Laurent
weight projector becomes Hermitian after the stated scalar extension.
Normality of a cocharacter value over the extension at a unit separating
the finite support implies this property, by the finite-support
normal-projector criterion.

If scalar conjugation fixes the extended coefficients and the extension
unit has norm one, naturality under the scalar conjugation algebra map
shows that entrywise conjugation inverts the cocharacter value. A unit
whose order divides a power of two has norm one: its norm is nonnegative
and the same positive power of its norm is one. The extension comparison
for an inner scheme automorphism identifies the value of the conjugated
cocharacter with conjugation by the extended base matrix.

An invertible extension matrix fixed by entrywise conjugation descends to
an invertible real matrix. The proof takes real parts of the matrix and
its inverse. Their scalar extensions recover the two original matrices;
injectivity of real scalar extension then reflects both inverse
identities. In a compatible real scalar tower, extending this real
matrix to the base field supplies a base-field lift. These descent
lemmas themselves do not require the base field to be real.

For the remaining results the base and extension are `RCLike` fields in
a compatible tower over the real numbers, and every element of the
base field is fixed by its scalar conjugation. Each base element is
therefore its real part, so its extension is fixed by conjugation too.
This makes the scalar extension commute with star and allows
Hermitianity of every extended projector to reflect to the base field.

The actual representation comparison identifies the image of a
cocharacter point over the extension test algebra with the corresponding
general-linear cocharacter value. For a closed representation,
membership of an extended base matrix in the representation range
reflects to membership over the base field. This uses the published
description of the actual range by polynomial equations: evaluation of
each defining polynomial commutes with scalar extension, and the field
map is injective.

`exists_real_internal_conjugate_hermitian` additionally assumes that the
extension field is algebraically closed and that the actual
representation image over that extension is stable under matrix
adjoint. A primitive root of sufficiently large power-of-two order
separates the finite weight support. Its cocharacter value lies in the
actual extension image, has power-of-two torsion, and is inverted by
entrywise scalar conjugation. The imported real internal unitarization
theorem supplies an entrywise real conjugator in that polynomially
defined, adjoint-stable image. The matrix descent and polynomial
membership comparisons then give a conjugator in the actual base-field
representation image. Conjugation introduces no new weights, so the
same root separates the conjugated support. Unitarity implies normality;
the normal-projector criterion makes the extended projectors Hermitian,
and reflection gives Hermitian projectors for the original base-field
representation after conjugation.

This proof is an internal derivation from the imported finite-projector,
polynomial-image, and real internal two-power unitarization results. It
does not construct an initial representation or prove adjoint stability
over the extension from adjoint stability over the base field. Its
representation, common cocharacter, and stronger extension stability
are explicit inputs. The unconditional archimedean existence target
remains open.
