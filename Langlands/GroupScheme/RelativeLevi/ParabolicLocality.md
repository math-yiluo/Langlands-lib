# Locality and separatedness of actual relative parabolic subgroups

This derived module supplies Zariski locality and fpqc separatedness for the
unchanged relative-parabolic predicate and actual parabolic subgroup functors.
It does not construct a parameter scheme or assert effective fpqc descent of
parabolic families.

## Statements and construction

In a reductive ambient group, `IsRelativeParabolicSubgroup.of_openCover`
detects relative parabolicity on any Zariski open cover of the base.
`isRelativeParabolicSubgroup_iff_openCover` combines this with preservation by
base change. These theorems concern an actual supplied inclusion.

`baseChangeEmbedding` sends an actual parabolic subgroup functor to its actual
base change, equipped with its parabolicity. The hypotheses on the base map are
flatness, quasi-compactness and surjectivity. The resulting map is injective.
`eq_of_baseChange_openCover` gives equality detection on an arbitrary Zariski
cover. `restrict_injective` states injectivity for the presheaf restriction
along any fpqc parameter morphism.

`isParabolic_of_isRepresentedBy_of_openCover` applies the locality theorem to a
supplied monic representative of a subgroup functor. If that functor has actual
relative-parabolic representatives on the cover, the supplied global
representative is relative parabolic. Existence of a global representative
remains a hypothesis.

## Implemented proofs

Smoothness and relative affineness descend from the base cover by their
Zariski locality. For monicity, the actual pulled-back inclusion is identified
with the pullback over the induced cover of the ambient group scheme; monicity
is local on that cover. For each base point, its residue-field map factors
through a cover member containing the point. The field-valued parabolicity
theorem on that member and the canonical iterated-pullback comparisons recover
parabolicity of the original residue fibre.

Injectivity uses the imported fpqc reflection theorem for equality of subgroup
functors represented by monomorphisms. Zariski equality detection uses the
corresponding imported cover theorem. For presheaf restriction, ambient
isomorphism transport is cancelled before applying fpqc reflection.
For a supplied global representative, uniqueness of monic representations
identifies its local pullbacks with the given local parabolics.

## Provenance

All constructions and proofs are derived from the imported relative-parabolic
base-change theorem, actual subgroup-functor reflection, represented-subgroup
uniqueness and Mathlib's locality of morphism properties. Conrad, *Reductive
group schemes* (2014), Definition 5.2.1, p.151, and Corollary 5.2.9 and its proof,
pp.156–157, are context for the imported predicate and the descent application.
This module supplies locality and equality detection only.
