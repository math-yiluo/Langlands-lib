# Relative quotients and local orbit fibers for finite free actions

This internal adapter takes a scheme `U` over `S`, a finite free action `A` preserving
its structure morphism, and an `A.EffectiveQuotient` supplied by
`FiniteFreeQuasiAffineQuotient`. The coequalizer descends `U.hom` to a structure
morphism on the quotient. The resulting `quotientOver` and `quotientMapOver` retain
the finite étale surjective projection.

If `S` is affine, the group is finite, and `U.left` is quasi-affine,
`quotientOver_quasiAffineOver` proves the all-affine-open condition for relative
quasi-affineness. An affine open in the affine base has an affine inclusion, so its
preimage has an affine inclusion into the quasi-affine quotient and is quasi-affine.
`quotientModel` packages the relative scheme, projection, these geometric
properties, and the fiber criterion below. It is applied to a supplied effective
quotient; `A.quasiAffineQuotient.val` provides one under the stated hypotheses.

Equality in the quotient on any scheme test is equivalent to differing by an action
element on the pieces of a Zariski open cover. This follows by pulling back the
coproduct cover of the effective action relation. The converse follows from
invariance of the projection and morphism equality on an open cover. The action
element is allowed to vary between open pieces.

The local orbit lemma itself only uses the effective kernel pair, and does not
require the group to be finite or the source to be quasi-affine once that quotient
has been supplied. Its cover has indexing universe `u`. The relative version follows
by forgetting to schemes and using extensionality of morphisms in `Over S`.

All provenance is derived from the imported effective quotient and Mathlib's
coproduct covers, pullbacks, and quasi-affine preservation by affine morphisms.
The result is an adapter for the later normalizer orbit construction; it does not
construct that orbit map.
