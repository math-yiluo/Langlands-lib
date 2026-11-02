# Scheme reduction for local finite type source descent

Author: Worker 1150.

This private draft investigates the scheme part of the finite-type branch of
Stacks Descent Lemma 14.3 (Tag 02KL), using the registered source
`stacks-descent-ed88ff78-2026`, printed p.43. It does not prove the ring
cancellation lemma (Tag 0367) or the general source-descent statement.

`exists_affine_fppf_refinement` uses openness of flat locally finitely presented
maps and Mathlib's `QuasiCompactCover.exists_hom`. For an affine target it
chooses a finite affine refinement of the singleton cover given by the fppf
map. The finite disjoint union of these affine components is affine.
The maps from the components into the original source are open immersions,
so their disjoint union is locally of finite type. The composite still covers
the target and is flat and locally of finite presentation, as can be checked
on the component open cover.

`locallyOfFiniteType_sourceDescent_of_ring` is conditional on the explicit
ring cancellation hypothesis `hring`. It uses Zariski locality to reduce the
base and the intermediate scheme to affine schemes, then applies the affine
refinement lemma to the covering source. The affine global-section criterion
translates all hypotheses into ring properties, and `hring` gives the finite
type property of the intermediate scheme over the base. The hypothesis is
the remaining mathematical input; the draft does not establish it.

This is internal derived content using Mathlib's actual schemes and
morphism properties. No claim of publication or proof of the parent
group-space representability target is made.
