# From tensor preservation to arbitrary affine test pullbacks

`isIso_localizedHom_of_algEquiv` uses the identity and composition clauses
of the localized affine functoriality proposition to give inverse
analytic maps for an actual algebra equivalence.

`affineTestPullbackPreservation_of_tensor` derives the spectrum-map form
of affine pullback preservation from the published tensor-product
proposition and the localized functoriality proposition, both supplied
as explicit premises. It reflects the given presheaf pullback through
the scheme Yoneda embedding, forgets the base scheme, reflects it through
the spectrum functor, and reverses arrows to obtain a ring pushout.
Reflection through the forgetful functor from algebras retains the
ground-field structure. The two maps out of the base algebra specify
its algebra structures on the factors. The tensor pushout universal
property identifies the given top algebra with their tensor product.
Its existing finite polynomial presentation transfers finite type to
the tensor product. The assumed tensor preservation then transports
along the analytic isomorphism induced by this algebra equivalence.

## Provenance: internal

This is an algebraic and categorical reduction, with both analytic input
propositions left as hypotheses. It does not prove either input or assert
an unconditional analytification theorem.
