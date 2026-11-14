# Algebraic boundedness under restriction between split tori

Worker 312. This is internal derived content for the unramified root-filtration
boundedness task. It combines the published finite ordered-product bound with
the published exact product formula for restriction of a valued root family
between split tori; it makes no additional translation from external literature.

`TorusRestrictedZeroRootFiltrationBoundedStatement` is universe-polymorphic.
Over any valuative field it considers two split tori, a smooth affine group of
finite type, a monomorphism from the upper torus into that group, actual opposite
factor pairs and an actual root-datum valuation of the upper root family. For
any homomorphism of the two tori, boundedness of every upper zero-depth root
filtration implies boundedness of every actual lower zero-depth root filtration
of the canonical restricted root function family. All boundedness is in the
same ambient group and for the supplied valuative relation.

The first helper identifies the actual ordered root-filtration product with the
range of the ordered product of its filtration subgroups. The published
finite-product lemma gives boundedness. The second helper takes the finite
enumeration of selected indivisible upper roots with their positive integral
restriction multipliers. The published restriction product formula identifies
the restricted subgroup at depth `r` with this finite product, so bounds on the
upper filtrations at the multiplier-scaled depths bound the lower subgroup.
At depth zero every multiplier gives the same zero depth. The canonical scalar
family recovers that restricted subgroup, yielding the zero-depth helper and
the theorem `torusRestrictedZeroRootFiltrationBounded`.

The general-depth helper explicitly assumes the corresponding bounds on upper
filtrations. The zero-depth statement neither constructs the upper valued
family nor supplies its boundedness, and it does not perform field descent or
construct a bounded quasi-split apartment.
