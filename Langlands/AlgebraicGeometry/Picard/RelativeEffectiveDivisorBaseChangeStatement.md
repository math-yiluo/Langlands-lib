# Arbitrary base change of relative effective Cartier divisors

Author: Worker 1543.

`Langlands.AlgebraicGeometry.Picard.RelativeEffectiveDivisorBaseChangeStatement.{u}`
is a proposition, with no proof asserted here. It concerns actual ideals,
closed subschemes and module sheaves on arbitrary schemes in universe `u`.
Let `f : X ⟶ S` and let `I` be an actual ideal such that its actual kernel
module is invertible and its closed subscheme is flat over `S`. For every
`g : T ⟶ S`, set `X_T = T ×_S X` and let `p : X_T ⟶ X` and
`q : X_T ⟶ T` be its projections. The statement asserts both:

- The actual ideal `I.comap p` is a relative effective Cartier ideal for
  `q`.
- There is an isomorphism from the ordinary module pullback of the actual
  ideal kernel of `I` to the actual ideal kernel of `I.comap p`.
  Composing its forward map with the new actual ideal inclusion gives
  the pullback of the old actual ideal inclusion, followed by the
  canonical structure-module pullback isomorphism.

In particular, the isomorphism identifies the actual ideal inclusions;
it is stronger than an unspecified isomorphism between abstract line
bundles. No flatness of `g` is assumed. There is also no ambient flatness,
noetherian, properness, projectivity or finite-presentation premise. The
relative effective condition is the published conjunction of the
invertible actual ideal and flatness of its associated closed subscheme,
with no base-change stability built into its definition.

The source is S. L. Kleiman, *The Picard scheme*, arXiv math/0504020v1
(2005), p.23, Definition 3.6 and the paragraph immediately following it.
That paragraph establishes functoriality by observing that flatness of the
closed subscheme makes the pullback of its ideal equal to the ideal of the
base change. The invertible ideal then remains invertible. The registered
original is `kleiman-2005-picard-scheme-arxiv-math0504020v1`;
pp.22–23 were read, and no corresponding project erratum was found.

The source works under locally noetherian conventions. The statement here
extends its same ideal-pullback argument to arbitrary schemes: locally the
sequence from the ideal into the ambient structure sheaf with quotient
the divisor structure sheaf stays exact after base change because the
quotient is flat over the base. Local freeness of rank one is preserved
by ordinary pullback. These are an explanation of the derivation and
retained proof obligations, not a Lean proof of them.

The internal auxiliary construction
`RelativeEffectiveDivisorBaseChange.subschemeIso` is proved separately in
this module using Mathlib's actual `comapIso` and pasting isomorphism of
pullbacks. It identifies the actual subscheme of `I.comap p` with
`T ×_S I.subscheme`, and `subschemeIso_hom_fst` proves its equation over
`T`. Consequently `flat_toBase` proves the new structural flatness from
ordinary base-change stability of flat morphisms.
`isRelativeEffectiveCartierIdeal_of_kernelIso` then transports the old
rank-one local freeness along a supplied actual kernel pullback
isomorphism and combines it with this flatness. It does not construct
that isomorphism.

This is the base-change prerequisite for the relative divisor functor
and the natural association `D ↦ O(D)`. It supplies no divisor presheaf,
open Hilbert locus, linear-system representer, Abel-map representability
or Picard representability.
