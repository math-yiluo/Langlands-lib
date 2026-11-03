# Normalized transitivity for actual nested dynamic parabolics

`dynamicNestedParabolicTransitivity` proves the exact published
`DynamicNestedParabolicTransitivityStatement.{u, uV}`. Both natural
isomorphisms use the actual normalized functors on the full smooth complex
representation categories, with the field/group universe and the
representation-carrier universe independent.

The published structural hypothesis supplies the actual product
`N = (L ∩ N) U`. The compatible pair supplies `P ≤ Q` and `M ≤ L`.
The published conversion supplies the semidirect decomposition of the
literal inner parabolic `P.subgroupOf L`, with Levi `M.subgroupOf L` and
radical `N.subgroupOf L`. No structural existence theorem is asserted here.

The topology remains the canonical rational-point topology. Smoothness and
affineness of the reductive group give finite-type coordinates; second
countability follows from the supplied local-field topology and a finite
polynomial presentation. The existing dynamic limit morphism gives a
continuous outer Levi projection. Published compact-open containment for
each actual dynamic radical implies compact-subgroup containment and then
unimodularity of both radicals. Closedness of `L` passes compact-subgroup
containment to the literal inner radical.

The imported generic application derives the positive Haar identity
`δ_N = δ_U δ_(N∩L)` from the actual radical product and continuous
semidirect Haar coordinates, transporting the inner factor to
`N.subgroupOf L`. Its positive square root supplies the exact
`NestedInduction.HalfCharacterProduct`. `NestedInduction.iso` then gives
the direct-to-iterated normalized induction natural isomorphism. Its
components arise from smooth induction in stages, the continuous split
quotient, and the character twist, with coefficient naturality already
proved.

For Jacquet restriction, the radical product identifies
`U ⊔ (L ∩ N)` with `N`. The same positive Haar identity supplies the
normalization comparison for the published coinvariant stages
isomorphism. `NestedParabolic.jacquetIso` transports the literal inner
subgroups and reverses that isomorphism to the target's direct-to-iterated
direction. It is a natural isomorphism of the actual quotient functors.

The convention is Haar scaling under `n ↦ m n m⁻¹`: induction twists by
the positive half character and Jacquet restriction by its inverse.
These are the conventions explained in the published statement's
Markdown for Renard VI.1.2 and VI.1.4 (French 9 July 2026 edition, printed
pp.136–137 / PDF pp.142–143). This implemented proof uses actual
semidirect Haar coordinates and explicit induction comparisons rather
than Renard's root/Cartan calculation and adjunction argument.

All original local compactness, nonarchimedean group, closedness,
compatible-pair and all-test structural premises are retained. There is
no additional transitivity, modulus, adjunction, finite-length or
representation-category premise. The published target and its imports
are unchanged.

Worker 194 assembled the dynamic and Jacquet comparisons. Worker 691
constructed the normalized induction stages comparison used here.
