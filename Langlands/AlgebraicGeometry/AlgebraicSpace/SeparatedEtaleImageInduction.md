# Finite-field-fibre induction for separated etale images

This internal extension of `EtaleLocalImageInduction` replaces a monomorphism to
the scheme base by a closed diagonal on the sheaf and an etale structural chart
composite. No schemehood conclusion is assumed.

The proposition `CompactImageDescent` isolates effective descent of an already
compact represented saturation. Strong induction on the finite field-fibre bound
of an affine etale base map reduces local image representation to that step.
For bound at most one, the base map and its pullback are open immersions. For a
larger bound, the off-diagonal has a smaller bound. Its chart composite remains
etale by base change, and the new sheaf has closed diagonal by the affine
pullback lemma. The inductively represented off-diagonal image and the original
affine open chart give a compact represented saturation; the supplied descent
step gives the result. Every affine etale morphism has a finite bound, yielding
the last theorem. All construction and finite-bound inputs are published APIs.
