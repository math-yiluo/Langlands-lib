# Existence of initial scheme models along filtered ring colimits

`Langlands.AlgebraicGeometry.SchemeLimitModel.schemeFilteredModelExistence`
proves the unchanged published proposition
`Langlands.AlgebraicGeometry.SchemeLimitModel.SchemeFilteredModelExistence`
in an arbitrary universe `u`. The proof was written by Worker 105 and is
reused here by Worker 148 from the task's shared draft.

The target is the initial existence assertion of Conrad, *Weil and
Grothendieck approaches to adelic points* (2011), Theorem 3.4(1), printed
p. 5, with small filtered categories in place of directed posets. Its
three finiteness conditions express the finite-presentation convention
immediately preceding that theorem. The original is registered as
`conrad-2011-weil-grothendieck-adelic-points`, SHA-256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`.
The proof below gives the categorical extension directly.

For a small filtered diagram `F`, an actual colimit cocone `c` with
witness `hc`, and an actual morphism `g : X → Spec c.pt`, assume
quasi-compactness, quasi-separatedness and local finite presentation.
The theorem constructs an actual index `j`, scheme `Xj`, structural
map `gj : Xj → Spec (F.obj j)` with those same three properties, and
`π : X → Xj` satisfying
`IsPullback π g gj (Spec.map (c.ι.app j))`.

The proof first invokes the published
`NoetherianApproximation.schemeSubalgebraDescent` over `ULift ℤ`, with
empty prescribed finite set. That theorem constructs a finitely generated
coefficient subalgebra `T` of `c.pt`, an actual model `f₀ : X₀ → Spec T`
with the three finiteness properties, and a pullback comparison with `g`.

Lifted integers are noetherian, so `T` is finitely presented over them.
Set `D = F.op ⋙ Scheme.Spec`. Applying preservation of limits by
`Scheme.Spec` to `hc.op` proves that the cone with apex `Spec c.pt` and
legs `Spec.map (c.ι.app j)` is limiting. Each stage spectrum is affine,
so the diagram has affine transitions and quasi-compact, quasi-separated
stages. The maps to `Spec (ULift ℤ)` are compatible by its terminality.
Mathlib's
`Scheme.exists_π_app_comp_eq_of_locallyOfFinitePresentation` then factors
the coefficient map `Spec c.pt → Spec T` through one actual stage
spectrum, giving `q : Spec (F.obj j) → Spec T` and the needed equality
with the actual cocone leg.

Take `Xj = pullback f₀ q` and `gj = pullback.snd f₀ q`. Base change
supplies local finite presentation, quasi-compactness and
quasi-separatedness of `gj`. Rewriting the original comparison with the
factorization equality produces the outer pullback square. Its right
square is the chosen pullback defining `Xj`, so `IsPullback.of_right'`
constructs `π` and the required square.

All rings, schemes and indexing-category sizes retain the arbitrary common
universe `u`. Ring transitions may be noninjective, the models may be
nonaffine and nonseparated, and no noetherian hypothesis is imposed on
any supplied stage ring or on `c.pt`. Noetherianity is used only for the
auxiliary lifted integers. The theorem addresses initial existence;
relative Hom comparison, prescribed-isomorphism descent, property
descent and arithmetic or topological realizations remain separate.

The reused subalgebra theorem is the published port of the Anthropic FLT
scheme-approximation theorem. Its original copyright, licence and
attribution remain in the imported Library modules and
`licenses/Anthropic-FLT/`; this contribution adds only the proof pair
and leaves that dependency closure unchanged.
