# Affine and locally noetherian reductions for fibrewise isogenies

This internal reduction relates the unchanged arbitrary-base reductive
fibrewise-isogeny criterion to its restriction to affine bases.
`AffineReductiveFibrewiseIsogenyStatement` quantifies over every commutative
ring in the given universe, without a noetherian hypothesis, and retains
the reductivity and residue-fibre isogeny hypotheses of the original target.
It is a proposition definition, not an unconditional proof of that criterion.

`isogeny_of_openCover` glues isogenies of a specified homomorphism over an
arbitrary open cover of the base. It pulls that cover back to the target
group scheme. Finiteness, flatness, and surjectivity are each Zariski local
on the target, so their intersection is too. The actual base-changed
homomorphism is identified with the relevant pullback map using
`baseChange_map_isPullback` and its canonical pullback isomorphism. The
morphism property respects isomorphisms, which gives the needed property
on each component of the pulled-back cover. This gluing result requires
no smoothness or reductivity.

`reductiveFibrewiseIsogeny_of_affine` uses the canonical affine open cover.
Reductivity and the fibrewise-isogeny condition are preserved by base
change, so the supplied affine criterion applies to every component.
`reductiveFibrewiseIsogeny_iff_affine` adds the converse, obtained by
evaluating the original target on spectra of commutative rings.

`isogeny_of_fibrewise_of_dvr_criterion_of_locallyNoetherian` proves the
criterion over every locally noetherian scheme, conditional on
`DvrFibrewiseIsogenyStatement`. The rings in its canonical affine open
cover are noetherian. The earlier noetherian affine DVR reduction proves
the isogeny on each component, and the same gluing lemma completes the
proof.

These are internal consequences of the named Library reductions and
Mathlib's target-local morphism properties. No external source statement
is asserted here. The module does not prove the DVR criterion, the affine
criterion, or the noetherian approximation needed to pass from noetherian
rings to arbitrary rings.
