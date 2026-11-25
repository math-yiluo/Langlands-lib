# Trivializing the actual Levi moduli at a supplied stable Levi

This internal construction supplies a local chart for the actual Levi moduli.
Over an arbitrary base scheme, take a relative parabolic in a reductive group,
a supplied radical inclusion and a supplied Levi inclusion. The hypotheses
explicitly require the literal pullbacks of these last two inclusions to remain
a radical and a Levi after every base change. No unconditional stability result
is asserted in this module.

The radical scheme represents the actual Levi images by sending a point to
the conjugate of the supplied Levi image. On each test, unique conjugacy gives
the bijection through `LeviImage.conjugationEquiv`. The underlying point of
the pulled-back group is precisely `pulledBackPoint`, the comparison fixed by
the target's representation interface.

The proof of naturality uses the published compatibility of subgroup
restriction and conjugation. The range of the iterated pullback of the
supplied Levi becomes the range of its direct pullback under the canonical
comparison, by naturality of that comparison and invariance of ranges under
an isomorphism of the source. Multiplication of radical points becomes
successive conjugation, proving equivariance for the regular action.

This is derived from the published image, restriction, point-comparison and
unique-conjugacy APIs. It supplies a representation in the presence of the
stated stable local model; it makes no assertion that a global Levi exists
on an arbitrary base.
