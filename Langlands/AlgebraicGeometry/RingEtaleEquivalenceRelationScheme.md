# The scheme relation attached to an affine ring relation

Author: Worker 122.

This internal adapter uses the global-sections and spectrum adjunction to
translate the published ring relation into the corresponding actual scheme
relation. The adjunction describes maps from any scheme to an affine scheme,
so it does not assume the testing scheme is affine.

`schemePointEquiv` is the adjunction equivalence, with ring arrows
unopposed. `schemePointEquiv_comp` records its compatibility with
postcomposition by a spectrum morphism.

`toScheme hE` has object scheme `Spec B`, relation scheme `Spec C`, source
`Spec (algebraMap B C)` and target `Spec t`. To verify its relation axioms
on a testing scheme `X`, apply the published ring relation axioms to
the ring of global sections of `X`. The adjunction transports the
resulting ring maps back to scheme morphisms. Its naturality identifies
the required composites. This uses the given ring axioms in their original
universe: the scheme and its global-sections ring have universe `u`.

The pair of projections is a monomorphism because the published
`RingEtaleEquivalenceRelation.hom_ext` identifies two ring maps agreeing
after composition with the source and target. This lemma uses the given
generation assumption `adjoin_range_eq_top`. The adjunction transfers this
uniqueness to maps from each testing scheme, which is the monomorphism
condition. Each projection is étale by Mathlib's spectrum criterion for
étale ring maps.

`toScheme_s_apply` and `toScheme_t_apply` identify the underlying point
maps with prime-spectrum comaps. All four constituent objects and morphisms
of `toScheme` are the original affine data, definitionally.

This is derived internal content using the existing Library relation,
its uniqueness lemma and Mathlib's adjunction and étaleness criterion.
It supplies no quotient scheme or coaction result and does not assume or
prove zero detection by invariants.
