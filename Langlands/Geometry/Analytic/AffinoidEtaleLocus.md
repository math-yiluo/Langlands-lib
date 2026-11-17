# The open pointwise étale locus of an actual affinoid map

This internal construction proves that the pointwise étale locus of any
finite-type bounded map between actual presented affinoid algebras is open.
In particular it applies to every finite Banach map. It uses the published
Noetherianity of the actual affinoid algebras and Mathlib's local smooth-fiber
criterion. It does not assume either finite base-change proposition and does
not assert unrestricted pointwise lifting in the analytic étale site.

`BanachSpectrum.primePoint` sends an ordinary bounded multiplicative seminorm
to its prime kernel. This map is continuous: the inverse image of an algebraic
zero locus is the intersection of the closed evaluation zero sets of its
elements.

`BoundedAlgHom.pointwiseEtaleLocus` is the set of ordinary points where the
original bounded map is both flat and unramified in the published pointwise
sense. `pointwiseEtaleLocus_eq_prime_preimage` identifies it with the inverse
image of the algebraic étale locus under the kernel-prime map. Noetherianity
of the original source algebra turns the assumed finite type into finite
presentation, which is essential in the argument.

For the forward implication, the pointwise flatness criterion supplies
flatness of the target prime localization over the original source.
Localize the source at the contracted prime and the original target by the
same source denominators. This intermediate algebra remains finitely
presented over the localized source. The target prime localization is flat
over that local source and formally unramified. Its residue-field fiber is
formally étale because it is essentially of finite type and formally
unramified over a field. Mathlib's flat local smooth-fiber criterion then
makes the target prime localization formally smooth over the local source.
Together with unramifiedness and the formally étale base localization,
composition gives formal étaleness over the original source.

For the reverse implication, the algebraic étale-locus theorem supplies a
principal neighborhood whose localized algebra is étale and thus flat over
the original source. Further localization at the chosen prime remains flat.
Formal unramifiedness is already a component of formal étaleness. The existing
pointwise criteria convert these properties back to pointwise étaleness of
the unchanged bounded map.

Finally, `isOpen_pointwiseEtaleLocus` pulls the open algebraic étale locus
back along the continuous kernel-prime map. The generic local-ring helpers
allow independent ring universes. For the affinoid declarations, both algebra
carriers lie in the coefficient field's universe, as specified by
`PresentedAffinoidAlgebra K`. There is no nontrivial-valuation or strict-radius
premise.
