# Presentation and affine geometry of full group-scheme kernels

Worker 878.

This internal API works over an arbitrary base scheme and imposes no commutativity,
flatness or smoothness hypothesis on its group schemes. Every unit section is an
immersion: its composite with the structure map is the identity, and immersions
can be cancelled on the right. Pullback then makes the full kernel inclusion an
immersion, even when the target is not separated.

If the source is locally of finite presentation, the kernel is locally of finite
presentation whenever the base is locally noetherian or the target is locally of
finite type. In the noetherian case the immersion first gives local finite type,
then noetherianity upgrades it to local finite presentation. In the other case,
the published finite-presentation cancellation lemma applied to the homomorphism
makes it locally of finite presentation; the kernel structure map is its pullback
along the target unit.

A final lemma shows that a closed full kernel in an affine source is affine over
the base, by composing its closed inclusion with the source structure map. This
supplies quasi-compactness and quasi-separatedness when needed.

These are categorical and scheme-geometric consequences of existing Library and
Mathlib results, used as prerequisites for SGA 3 IX, Corollaries 6.6 and 6.7. They
do not assert either spreading corollary or that the source is of multiplicative
type. The target's locally finite type hypothesis in the presentation lemma is
slightly weaker than the locally finite presentation hypothesis of the assigned
spreading statement, in agreement with editorial note 43 on printed p.55 of SGA 3
IX. No source claim beyond the proved lemma is needed.
