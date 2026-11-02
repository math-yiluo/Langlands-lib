# Extension of self-product line bundles over a trait

`Langlands.AbelianScheme.discreteValuationRingSelfProductLineBundleExtension.{u}`
proves exactly the published proposition
`Langlands.AbelianScheme.DiscreteValuationRingSelfProductLineBundleExtensionStatement.{u}`.
It has no outer hypotheses, and `u` is arbitrary.

For every discrete valuation domain `R`, every specified fraction field `K`
with its given `R`-algebra structure, every Library abelian scheme `A` over
`Spec R`, and every actual line bundle `D` on the generic self-product, the
proof produces an actual line bundle `E` on the total self-product and

```text
Nonempty (((LineBundle.pullback q).obj E).obj ≅ D.obj),
```

where `q` is exactly the canonical product map in the published statement.
These are actual locally free rank-one module sheaves and an actual
module-sheaf isomorphism. The specified field and algebra structure are
retained throughout.

The proof first identifies `K` as localization away from a uniformizer `π`
of `R`. The powers of `π` are nonzero, and every nonzero element of a DVR
divides a power of `π`. Mathlib's comparison of localizations therefore
identifies localization at those powers with the given fraction field.
`IsOpenImmersion.of_isLocalization` makes the actual map `Spec K → Spec R`
an open immersion. The published self-product base-change isomorphism
identifies `mumfordProductBaseChangeMap A b` with that open immersion's
base change after an isomorphism. Thus the exact canonical map `q` is open.

Next, `smoothDVR_factorialStalks` transports the published unconditional
theorem `Langlands.CommutativeAlgebra.smoothDVRFactorialLocalizations`
from affine prime localizations to scheme stalks. Given a smooth scheme
over `Spec R`, its affine cover supplies a smooth algebra of sections.
Its stalk is isomorphic to the localization at the associated prime; the
cover's open immersion supplies the stalk isomorphism back to the original
scheme. Unique factorization transports along these ring isomorphisms.
This affine-cover transport adapts the argument in
`Langlands/AlgebraicGeometry/SmoothAlgClosedFactorialStalksProof.lean`
using the smooth-DVR theorem in place of its field input.

The actual total self-product is smooth over `Spec R` by base change and
composition. The preceding result makes every one of its stalks factorial.
Its structure map is locally of finite type over the Noetherian DVR
spectrum, which also makes the self-product locally Noetherian.

Finally, the published unconditional theorem
`Langlands.AlgebraicGeometry.Picard.openImmersionLineBundleExtension`
extends `D` across `q`. It requires factoriality only outside the image;
the stronger all-stalk result just proved supplies this premise. Its
witness and restriction isomorphism have precisely the required types,
because `mumfordProductBaseChangeMap A b` is definitionally the explicit
`pullback.map` in the target.

The implemented argument specializes the regularity explanation in
Raynaud's proof of Lemme XI 1.5, printed p.162, through the general
open-immersion extension theorem. Raynaud's original passage and its
chosen-field specialization are documented in the unchanged target
statement pair. The imported ring theorem documents its smooth
regularity and regular-local factoriality argument; the imported
open-immersion theorem documents its actual ideal extension and gluing
construction. This module proves their geometric application and adds
no separate source assertion.

Worker 339 authored the geometric assembly and adapted stalk transport.
Worker 59 contributed the open-immersion interface and proof route.
The imported published proofs retain their own authorship.

The conclusion requires no unit-axis condition on `D`, ampleness,
projectivity, henselianity, completeness, or restriction on the residue
field or characteristic. The proof uses none of
`ValuationRingTwoAxisExtensionStatement`, `ValuationRingAmpleExtensionStatement`,
`PicardZeroValuativeExtensionStatement`,
`RelativeDualSchemeValuativeExistenceStatement`, or results depending on
those conclusions. It asserts the DVR case only.
