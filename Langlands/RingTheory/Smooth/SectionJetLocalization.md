# Section jets in a principal neighborhood

Let `ε : A →ₐ[R] R` be a split augmentation and let `a : A` have invertible
image under `ε`. The augmentation extends to `Localization.Away a`.
The map induced by localization from each actual jet of `ε` to the
corresponding jet of the extended augmentation is bijective.

In the implementation, the kernel of the extended augmentation is the
extension of the original kernel. The class of `a` in each jet quotient
is a unit because it is a unit modulo the augmentation ideal and the
image of that ideal in the jet is nilpotent. The localization property
then gives a map from the localized algebra to the original jet. This
map annihilates the corresponding power of the extended kernel, so it
descends to the inverse jet map. The inverse identities follow by quotient
and localization extensionality.

This is an internal locality result for the construction of the
smoothness locus along a section. It identifies the normal invariants
before and after restricting to a principal open containing the section,
as used when passing to a neighborhood of the section in SGA 3,
Exposé XV, Lemma 5.4.
