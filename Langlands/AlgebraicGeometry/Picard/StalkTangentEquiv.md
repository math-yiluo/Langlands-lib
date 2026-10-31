# All rational tangent maps arise from the actual stalk

This internal adapter completes the existing `StalkTangent` injection for an
arbitrary scheme over an arbitrary field. Its carriers are the existing
augmented algebra maps on the actual point stalk and actual dual-number scheme
maps satisfying `IsTangentVectorAt`. No finite type hypothesis is needed.

The first-coordinate augmentation of the dual numbers is a local homomorphism:
an element is a unit exactly when its first coordinate is a unit. Thus its
spectrum takes the field's closed point to the dual numbers' closed point.
The tangent restriction equation then identifies the image of that closed
point with the specified rational point.

For an arbitrary tangent map, Mathlib's
`Scheme.Spec_stalkClosedPointTo_fromSpecStalk` factors it through the spectrum
of that actual stalk. Its equation over the field gives an algebra map by
`Spec.homEquivAlgHom`. The restriction equation, cancellation of the monomorphic
map `fromSpecStalk`, and the existing stalk augmentation formula show that its
first coordinate is the prescribed augmentation. This proves surjectivity.
The published injection then gives `rationalStalkTangentEquiv`. Its forward
value is exactly spectrum of the algebra map followed by `fromSpecStalk`.

This construction is derived from the existing stalk adapter and Mathlib's
local-ring factorization, with no additional comparison hypothesis. It does
not identify the sheaf-defined tangent module or cohomology.
