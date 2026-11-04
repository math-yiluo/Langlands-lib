# The same valuation apartment under the adjoint torus vector space

For an actual square `h : IsAdjointSplitTorusImage q i j p` and one supplied
`D : KPApartmentData i ω`, this module changes the translation coordinates
of that same type `D.Apartment` to the actual vector space `V T_ad`.
It uses the unique `translationEquiv` induced by the actual torus map `p`.
There is no choice of a point or origin.

`adjointTranslate D v x` is the original translation of `x` by
`translationEquiv.symm v`. In particular,
`adjointTranslate_cocharacterMapReal` says that a vector coming from
`V T` acts by the original quotient translation of that vector.
`adjointAddTorsor D` packages this action as an `AddTorsor (V T_ad)`
on the unchanged valuation points. Its subtraction is exactly
`adjointDisplacement D x y`. This torsor is explicit data: a consumer can
install it with `letI := h.adjointAddTorsor D`. For adjoint subtraction
notation, also install its `toVSub` locally: the original apartment has a
separately registered quotient subtraction. The new torsor is not a global
instance competing with the original quotient torsor.

The actual source normalizer continues to act on these same valuations.
`smul_adjointTranslate` is the affine compatibility formula.
`adjointNormalizerAffineEquiv D` packages this original action as a
homomorphism into affine automorphisms for the adjoint torsor. Its
derivative is precisely `normalizerAction j (h.normalizerPointsMap n)`.
The identities follow from the equivariance of `translationEquiv` and the
original `D.smul_vadd`, and the inverse coordinate formula follows by
cancelling `translationEquiv`. No lift of an adjoint rational point is used.

This is internal transport of the existing affine structure along its
constructed linear equivalence. The torsor laws reduce to the original
torsor laws and the inverse identities for that equivalence. It adds no
external source assertion. The affine and source monomorphism instances
remain explicit, and the target monomorphism is needed for the normalizer
action. The supplied adjoint image square implies these instances.

The points remain valuations of the source root datum. This module does not
construct a valuation apartment of the adjoint group, an action of every
adjoint normalizer point, the canonical derived and central splitting,
cross-torus A2, or the existence of valid building data.
