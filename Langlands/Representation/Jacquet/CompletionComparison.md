# The stable-image completion and the Jacquet completion

Author: Worker 1775.

This derived unit implements the inverse-limit comparison in David Renard,
*Représentations des groupes réductifs p-adiques*, version dated 9 July 2026,
VI.9.7, printed pp.205–206 / PDF pp.211–212. Registered source:
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.

The inputs are a smooth complex representation of an arbitrary topological
group, three subgroups, an element `g` commuting with every member of `M`
(`∀ m ∈ M, m * g = g * m`), the inclusions
`M ≤ normalizer N` and `M ≤ normalizer Nbar`,
and closedness of the Levi subgroup `M`. Group and vector-space universes are
independent. The set `S` consists of compact open indices admitting both
Iwahori contractions for this element. Cofinality of `S` in the ambient group
and of its actual Levi intersections in the Levi group are explicit inputs.
Commutation is a separate input, not a field of `IsIwahoriContraction`.
No representation finiteness hypothesis is introduced.

`stableCompletionComponent` regards a component of the existing
`stableImageCompletion` as a vector in the existing stable image. The
completion equations imply that the component is fixed by its compact index,
and the stable-image completion condition supplies its stable membership.
`stableCompletion_mk_transition` applies the averaging compatibility proved
in `CompletionTransitions` to these actual components.

For a Levi index `J`, choose a good ambient index whose Levi intersection is
contained in `J`, then average its Jacquet class to `J`. A third good index
inside the intersection of two choices, together with the transition identity,
proves independence of the choice. This also proves the Levi completion
equations. The resulting `stableCompletionJacquetMap` is linear because it
uses the actual quotient and averaging linear maps. At every good Levi
intersection its component is exactly the Jacquet class of the original
ambient component.

Assume further that the actual `stableImageJacquetMap` is bijective at every
good ambient index. Injectivity of the completion map follows by applying
these pointwise injections and then cofinality of the ambient indices. For
surjectivity, apply the inverse pointwise maps to the corresponding components
of a Jacquet completion family. The transition identity and pointwise
injectivity prove that these lifts form a compatible ambient family on `S`.
The existing cofinal extension construction produces a full ambient family,
with the prescribed stable components. Averaging at every Levi index shows
that its image is the original Jacquet completion family.

`stableCompletionJacquetEquiv` is the linear equivalence obtained from this
proved bijectivity. The construction uses the actual unnormalized descended
Jacquet action, compact averages, stable images and completion objects.

This unit retains the two cofinality inputs and pointwise Jacquet bijectivity.
It does not prove the structural contraction basis or stabilization theorem,
identify stable completion with subgroup-fixed completion, transport to
normalized represented-parabolic functors, establish the final naturality or
arbitrary-contraction characterization clauses, or prove either exact parent
proposition.
