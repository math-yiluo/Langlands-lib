# Field fibres of simultaneous reductive and parabolic models

`GoodFieldFibers p` packages the three field-valued conditions on an actual
homomorphism `p : P ⟶ G` over `Spec R`: connected reductivity of the ambient
pullback, parabolicity of the same pulled-back homomorphism, and connectedness
of the subgroup pullback. It quantifies over every field `k : Type u` and every
`Algebra R k`, and uses the actual morphism `Spec.algebraMap R k` throughout.
There is no finite-type, smoothness, domain, or arithmetic premise in this
packaging. It is an internal interface extracted from the published
`ReductiveParabolicSpreading.ModelData`, rather than a new literature assertion.

`GoodFieldFibers.atFieldPoint` proves that these tests include every actual morphism
`Spec k ⟶ Spec R`. The full faithfulness of the affine spectrum functor writes
that morphism as the spectrum of a ring homomorphism. Equipping `k` with that
ring homomorphism's algebra structure gives exactly the specified pullback.
This avoids identifying an arbitrary residue-field structure with a preferred
algebra structure by convention.

`GoodFieldFibers.isReductive` additionally assumes smoothness and affineness of
the ambient structural map. At each geometric point used by the current
`IsReductive` definition, `atFieldPoint` gives connected reductivity of the actual
geometric fibre. The published theorem
`IsConnectedReductive.isPseudoReductive` converts that field predicate to the
precise pseudo-reductivity predicate required by `IsReductive.geometricFiber`.
The construction retains the specified algebraic closure of the scheme residue
field and its actual composite geometric-point map.

`GoodFieldFibers.baseChange` proves stability under every morphism of affine
coefficient bases, without a field or injectivity hypothesis on that morphism.
For any subsequent field-valued point, apply `atFieldPoint` to its composite with the
coefficient morphism. The actual group-object pullback composition isomorphism
transfers connected reductivity and connectedness. For parabolicity, source and
ambient isomorphism transport preserve the supplied homomorphism; naturality of
the pullback composition isomorphism proves the required equality of arrows.
The private naturality lemma is the naturality equation of the existing
`Over.pullbackComp` isomorphism lifted to group objects.

`ModelData.goodFieldFibers` extracts these exact three clauses from the
published model record. This file constructs no integral models and proves no
spreading or openness assertion. In particular, it supplies none of the
existence, smoothness, or initial good-fibre premises of the full simultaneous
spreading theorem. Every declaration is uniform in universe `u`.
