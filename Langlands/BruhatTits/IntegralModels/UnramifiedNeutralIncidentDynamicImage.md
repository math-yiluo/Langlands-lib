# Dynamic positive subgroups in actual neutral comparison images

This internal adapter proves containment of the full dynamic positive subgroup
in the schematic image of a supplied comparison between actual neutral
components of full fixer models. It works at arbitrary universe `u`, over the
integers of the actual inertia fixed field of a nonarchimedean local field.
All containments hold on every scheme test over the residue field.

The building data `C` are supplied. The relative-component model data `M`,
`M'` supply the actual smooth neutral models. Their full models' integral
points are the character-valuation kernel intersected with the pointwise
fixers of the apartment images of `Ω`, `Ω'`, respectively. The comparison
`ψ` goes from the source neutral model to the target neutral model with
generic map the identity. The nonempty subsets lie in facets `Fa`, `Ca`,
with `Fa` a face of `Ca`. The model data and the comparison remain inputs;
this construction does not prove their existence.

The actual target integral torus is
`unramifiedNeutralSplitTorusData C M Ω hM`. The cocharacter in the target
neutral special fibre is the canonical specialization, through that torus,
of `C.incidentFacetCocharacter hCa hFaCa`, followed by the actual
special-fibre torus inclusion.

The theorem `unramifiedNeutralIncidentDynamicUnipotent_le_image` applies
`RelativeRoot.dynamicUnipotent_le_of_positive_rootSubgroups_le` to this
special fibre, which is smooth and affine by base change. The generic
relative root system and canonical character specialization provide
disjoint rays for indivisible positive roots in the special fibre.
Every positive residue root pulls back to a generic root, and the
specialization identity for the lattice pairing preserves its strict
positivity on the incident cocharacter. Actual root-model residue
representability identifies its root functor with the corresponding
root-model range. The actual-neutral incident-root image theorem puts
this range in the schematic image of `ψ`. The general theorem therefore
contains the entire dynamic positive subgroup, using the ordered
positive-root product construction internally.

`unramifiedNeutralIncidentDynamicUnipotentImagePoints` is the resulting
group homomorphism on each residue-scheme test. It is `Subgroup.inclusion`
for that containment. Its value theorem states that the underlying
ambient point is unchanged.

The provenance is internal composition of the general dynamic-root
containment theorem, specialization through an actual integral split
torus, the generic relative root system, and
`UnramifiedNeutralIncidentRootImage`. No global description of neutral
points by a separate zero-point subgroup is needed. This proves dynamic
positive containment only; containment of the full unipotent radical,
parabolicity and the full reduction-preimage formula remain separate
obligations.
