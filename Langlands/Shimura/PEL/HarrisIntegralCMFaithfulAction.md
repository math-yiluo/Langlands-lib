# Faithfulness of Harris action families from their dimension

`rationalEnd_nontrivial_of_relativeDimension` concerns an abelian scheme of
positive relative dimension over a nonempty universe-zero base on which
every positive integer is a unit. If the rational endomorphism ring had
equal identity and zero, `Langlands.AbelianScheme.Tate.ofHom_injective`
would give that equality for actual homomorphisms. On the total scheme
the zero homomorphism factors through the base and the unit section.
The equality would make the structure morphism an isomorphism. At a
unit point the relative dimension would then be zero, contradicting
the positive smooth relative dimension.

`harrisIntegralCMAction_injective_of_dimension` applies this argument
to the actual pulled-back abelian scheme of relative dimension
\([E:\mathbf Q]n^2\) on a nonempty test `T` over an `F`-scheme.
The composite structure map to `Spec F` makes every positive integer a
unit on `T`. Simplicity of the Harris algebra gives injectivity of the
unital rational action.

`harrisIntegralCMFullActionPolarizedActionOfDimension` takes the actual
polarized ambient family, the positive auxiliary integral order action
on its pullback to the nonempty quasi-separated test, and the full
Rosati and determinant condition. Its polarized action has that same
rational action, the canonical pulled-back dual and polarization, and
the involution preserved by the Rosati equations. The normalized
determinant and dimension comparison uses the unchanged reflex scalar
map through the test's structure morphism. Where a pointed frame is given,
the result equals `harrisIntegralCMFullActionPolarizedAction` on that same family.
Faithfulness follows from dimension before choosing any frame.

The setup is the actual positive-involution action and polarization
in Kottwitz, *Points on Some Shimura Varieties over Finite Fields*, §5,
printed p. 390 (PDF p. 18). The characteristic-zero comparison uses
`harrisIntegralCMFullActionCondition`. The original
source uses the prime-to-\(p\) moduli over the localized reflex ring.
Here the family lives over the characteristic-zero Harris base field.

Source `kottwitz-1992-points-shimura-finite-fields`, SHA-256
`c7cede3d0a5e201068e6100acbb3832adb67767d69248ec65458e7cc74ee46f1`,
§5, printed p. 390 (PDF p. 18).
