# Ambient transfer for largest split subtori

Author: Worker 1348.

This is an internal derived unit. It uses the published largest-split-subtorus
construction in `Rational.TorusSplitPart`; it assumes no parabolic or rational
Levi theorem. Its purpose is to isolate the elementary final step in the
split-part argument following Borel–Tits, *Groupes réductifs* (1965), proof of
4.18, printed p.92 (PDF p.39). It does not prove 4.18 or the geometric
hypotheses needed for the minimal-parabolic split-part theorem.

`torusCentralizer_le_of_factor` proves antitonicity of the whole-group
centralizer under an actual factorization. The proof substitutes the image of
each point into the defining commutation condition, retaining every test scheme
and refinement. `torusCentralizer_eq_of_iso` applies this in both directions
to an isomorphism between subgroup embeddings.

`IsMaximalSplitTorus.of_factor` says that a split subtorus containing an ambient
maximal split torus is maximal split. The containing factor is an isomorphism by
the given maximality; cancellation of this isomorphism proves maximality of the
larger embedding.

For a closed embedding `t : T → G`, a largest split subtorus `a : A → T`,
and an actual map `b : B → T` whose composite with `t` is ambient maximal
split, `IsLargestSplitSubtorus.ambient_transfer` proves that `a ≫ t` is
ambient maximal split and has the same all-test centralizer as `b ≫ t`.
Universality supplies `f : B → A`. Ambient maximality of `b ≫ t` makes
`f` an isomorphism; the preceding two lemmas give the conclusions.

`IsMaximalSplitTorus.ambient_transfer` uses the published theorem identifying
every maximal split subtorus of an affine commutative group locally of finite
type with its largest split subtorus.
`IsMaximalSplitTorus.ambient_transfer_of_isClosedSubgroup` obtains the required
affine and local finite-type properties from the ambient group and the closed
embedding, then transfers centralizer containment in any subgroup functor.
Neither result asserts that the required map `b` exists.

`TorusSplitPartTransferStatement.{u}` records the last result as a
proposition definition, with all fields, group schemes, embeddings and the
subgroup functor universally quantified. The theorem `torusSplitPartTransfer`
proves it by the preceding lemma. The entry declaration of this unit is this
derived proposition definition. Its statement publication does not supply a
separate proof receipt for the helper theorems or discharge the assigned
minimal-parabolic theorem.

The original source is registered as `borel-tits-1965-groupes-reductifs`,
SHA-256 `ec6674ba292deaadd77a449f4bad3750db79c0b87b117a892ef6b09bb16357ad`.
The implemented proofs are consequences of the existing categorical definitions
and universal properties, and do not assume the source's two-parabolic result.
