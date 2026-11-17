# Local torus conjugacy with a supplied common root-datum map

This internal derived module constructs torus conjugators for two actual finite
homomorphisms over an arbitrary commutative local ring. The groups are affine
and reductive. Their coordinate tori are closed fibrewise maximal tori, and
finite reduced fibrewise root data P and Q are supplied.

`HasCommonRootDatumTorusMap` packages a natural number p, a root-datum isogeny
`r : RootDatumIsogeny p Q P`, and an actual homomorphism tau between the
coordinate tori. The character formula for tau is r.weightMap, and both
ambient homomorphisms have tau as their torus restriction. All three
compatibilities are equations of actual morphisms.

`RelativeIsogeny.exists_fppf_torusConjugates` takes these data explicitly.
For every parameter scheme V over Spec R it constructs a flat, surjective,
locally finitely presented morphism W to V and a W-point of the target torus.
This point satisfies `TorusConjugates`: conjugation identifies the two ambient
homomorphisms on every scheme refining W and at every point of the source
group. The parameter schemes need not be affine. Neither flatness nor
surjectivity of the ambient finite homomorphisms is an additional assumption.

The proof chooses a base b of P and a full Weyl-normalized source root family
using `exists_normalizedLocalRootFamily`. Flatness of the reductive target
provides actual target root parametrizations. The target roots indexed by
`r.indexEquiv.symm alpha`, for alpha in b, are linearly independent: applying
r.weightMap to an integral relation multiplies each source simple root by the
positive integer r.rootFactor; independence of the source simple roots then
annuls each coefficient.

`exists_fppf_selected_root_alignment` now constructs W and its torus point,
with the conjugation equation for each positive source simple root on all
refinements. `TorusConjugates.of_simpleRootRestrictions` uses the source
normalization and the positive and negative root parametrizations to extend
these equations to the whole group.

`fppfLocallyTorusConjugate_of_supplied_rootDatum` applies this construction to
the base scheme and packages its single surjection as an fppf cover.
`fppfLocallyTorusConjugate_of_commonRootDatumTorusMap` unpacks the existential
compatibility predicate and applies that wrapper.

The provenance is the combination of the existing root-datum base existence,
normalized local root families, finite-map root alignment, and whole-group
conjugation theorems. The proof keeps arbitrary local rings and all scheme
tests, including nilpotents. Existence of the compatible root-datum isogeny and
its character formula remains a separate obligation; this module does not
prove the unconditional reductive-isogeny rigidity statement.
