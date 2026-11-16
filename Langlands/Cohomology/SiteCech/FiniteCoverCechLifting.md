# Degree-zero presentations and local lifting for free Čech complexes

This internal bridge starts with the actual finite basis covers of
`FiniteCoverLifting`, on an arbitrary site `(C, J)` and family `B : ι → C`.
`FiniteBasisCover.presheafArrow` is the arrow from the finite coproduct of
the cover-domain representables to the representable covered object. Its
representables have values in the coefficient universe even when the
finite index type has a smaller universe.

For the finite-cover constructions, the category is locally small in
universe `w`, the commutative coefficient ring `R` lies in `Type w`,
and module sheafification `HasSheafify J (ModuleCat.{w} R)` is assumed.
The singleton wide-pullback comparison itself does not need local
smallness of the site category.

The singleton wide pullback defining degree zero of a presheaf Čech nerve
is isomorphic to the arrow source: the projection is one direction and
the universal map with identity components is the inverse.
`presheafCechZeroIso` constructs this isomorphism explicitly. Applying the
free sheaf functor gives `freeCechZeroIso`; the wide-pullback relation shows
that its composite with the free image of the original arrow is the
actual Čech chain augmentation in degree zero.

The free sheaf adjunction supplies the left-adjoint instance and hence
preservation of finite coproducts. `FiniteBasisCover.freeCechZeroIso`
combines the degree-zero comparison with that preservation isomorphism
to identify the actual zero chain term with `FiniteBasisCover.freeSource`.
The following augmentation lemma verifies compatibility with
`FiniteBasisCover.freeAugmentation` by checking every coproduct summand.

Finally, under the explicit `HasFiniteBasisCoverRefinements J B`
hypothesis and `J.WEqualsLocallyBijective (ModuleCat R)`,
`exists_finiteBasisCover_cech_lift` transports the finite-cover lifting
result to the augmentation of the actual `freeCechChainComplex`. Its
equation has the form required for the `local_lift` field of a finite Čech
test system.

The provenance is internal: the proof uses the singleton wide-pullback
universal property, the free sheaf adjunction, coproduct preservation,
and the preceding section-lifting construction. Exactness of the full
augmented complex, finite basis presentations of the positive terms,
and the analytic finite-refinement instance are still separate
obligations. This module asserts no analytic comparison theorem.
