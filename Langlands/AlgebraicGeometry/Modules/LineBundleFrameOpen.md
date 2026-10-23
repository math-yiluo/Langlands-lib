# Openness of the frame locus of a line-bundle section

This proof uses the actual module restrictions and abelian-group stalks
from `SectionLocus`. It preserves the full universe parameter and places
no additional hypotheses on the scheme. The theorem
`Langlands.SchemeModule.lineBundleStalkFrameOpen` proves exactly the published
proposition `Langlands.SchemeModule.LineBundleStalkFrameOpen`.

First an endomorphism of the structure module acts on sections by
multiplication by its value at one; this follows from module linearity.
An invertible stalk map is surjective on the underlying abelian group, so
the germ of one has a preimage. The filtered-colimit description of stalks
represents that preimage by a section on some neighborhood. Naturality
and the equality-of-germs lemma shrink the neighborhood until the
endomorphism sends that section to one. Commutativity then makes its value
at one a unit on that neighborhood.

Restriction preserves this unit. On each open of the restricted scheme,
the endomorphism is therefore multiplication by a unit, hence bijective.
The componentwise isomorphism criterion makes the restricted module
morphism an isomorphism. Stalk restriction transfers this back to the
original scheme. Thus `isOpen_unitEnd_stalkIso` proves openness for an
endomorphism of the structure module.

For `isOpen_lineBundle_stalkFrame`, choose the local rank-one chart
provided by `LineBundle.property`. Conjugate the restricted section
morphism by that chart and the canonical restriction-of-unit isomorphism.
This is an endomorphism of the structure module on the chart. Functors
preserve the conjugating isomorphisms, and the published
`isIso_stalk_restrict_iff` identifies its stalk-isomorphism locus with the
original section's stalk-frame locus on the chart. Its open image supplies
a neighborhood of each stalk-frame point.

Finally `lineBundle_stalkFrame_set_eq` applies the already published
`trivializationOpenInterior`. The interior of the now-open stalk-frame
locus is itself, yielding equality with the whole trivialization open.
The exact-target theorem `lineBundleStalkFrameOpen` pairs this equality with
`isOpen_lineBundle_stalkFrame`, for every scheme, line bundle, and section.

The motivating source is Stacks Project Lemma 17.25.10 (tag 01CY), whose
proof likewise extends an inverse germ over a neighborhood. The implemented
proof works directly in a local scalar chart and does not construct the
inverse bundle section from the source. It proves no comparison with the
actual residue-field pullback; that is a separate prerequisite of the
parent residue-comparison task.
