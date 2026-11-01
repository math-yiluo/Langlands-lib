# Exactness of both actual nondegenerate dual functors

`Langlands.Algebra.nonUnitalModuleDualCategoricalExactnessStatement` proves
exactly the published closed proposition
`NonUnitalModuleDualCategoricalExactnessStatement.{uA,uM}`. It concludes
additive witnesses for both actual functors, both of Renard's two-sided
sequence conditions, reversal of every middle-exact short complex and reversal
of every short exact complex in both module orientations. All algebra and
module inputs are quantified inside the unchanged target.

The governing source is David Renard, *Représentations des groupes réductifs
p-adiques*, French version dated 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The actual duality and exactness lemma are I.4.1, printed pp.22–23 /
PDF pp.28–29. The original nonunital action conventions are printed pp.5–7 /
PDF pp.11–13; canonical complex scalars are I.2.1, printed p.14 /
PDF p.20; and the fixed-part splitting is I.3.1, printed p.19 /
PDF p.25. These passages were read directly and the source hash verified.
The registered supplement `renard-2010-corrections-complements`, SHA256
`fdf3c88716c294c451c1f6fad67f6b99c95dae670aae0b8ad191ab0a96e69863`,
was read at PDF pp.1–2. Those nearby supplementary corrections do not change
the governing exactness lemma. No dedicated project errata file for either
source was present at the source audit.

Renard proves reversal of short exact sequences by identifying each idempotent
fixed part of the actual dual with the ordinary complex dual of the original
fixed part and testing exactness there. The implementation instead uses
full-dual extension followed by projection with an original fixing idempotent.
That argument is implemented in `NonUnitalModuleDualMapExactnessProof`:
`pullback_exact` reverses exact pairs of original functions,
`pullback_surjective_of_injective` reverses injectivity, and
`pullback_injective_of_surjective` reverses surjectivity. Its paired
Markdown gives the extension, annihilator and idempotent calculations.
No fixed-part inverse, equivalence or naturality is used or reproved.

The two categorical helper modules are internal derived steps of this same
proof. `NonUnitalModuleDualLeftExactnessProof` treats original left modules.
The named `NondegenerateModuleCat.abelian A hA` and
`NondegenerateModuleCat.abelian Aᵐᵒᵖ hA.op` supply precisely the structures in
the target. Their Hom groups retain the inherited pointwise addition, as
`NondegenerateModuleCat.abelian_toPreadditive` records. Published pullback
additivity therefore gives an additive witness for the actual
`leftToRightFunctor hA`.

The published `NondegenerateModuleExactnessConcrete.exact_iff` identifies
categorical exactness with the assertion that every vector killed by the
second original map comes from the first. The zero composite supplies the
other direction of `Function.Exact`. Applying `pullback_exact` and the same
criterion for the opposite algebra gives categorical exactness of the
reversed complex. The published `mono_iff` and `epi_iff` convert the two
endpoint pullback theorems into reversal of monos and epis. Together these
results reverse every short exact complex.

`NonUnitalModuleDualRightExactnessProof` supplies the corresponding results
for right modules, which are the original modules over `Aᵐᵒᵖ`. It applies
the same actual pullback theorems to `hA.op`. The published
`rightToLeftFunctor hA` additionally applies `fromDoubleOppositeFunctor`;
its map is `fromDoubleOppositeMap` of the opposite-algebra pullback.
This transport retains the entire underlying additive map and carrier, while
transporting the action by `a ↦ op (op a)`. The concrete exactness and
endpoint criteria therefore apply to the transported original left maps.
Additivity is likewise proved for this actual functor.

For each actual functor, `ContravariantSequenceExact` is the conjunction of
Renard's two one-sided sequence conditions on the opposite source category.
Given such a complex there, unopposing it reverses its maps and preserves
middle exactness. A mono first map becomes an epi last map, and an epi last
map becomes a mono first map. The established reversal results thus prove
the required middle exactness and the required mono or epi boundary. These
are separate obligations from reversal of short exact complexes, and both
are implemented.

The final closed theorem introduces the original algebra hypotheses, installs
exactly the two named abelian structures, constructs both additive witnesses,
and packages all six remaining clauses. It does not add an exactness
certificate or any other premise. The source's short exact assertion has
therefore been proved with its categorical and original-map interfaces,
rather than merely assumed.

Algebra and carrier universes remain independent, with explicit checks in both
unequal directions. The actual original nonunital actions, published recovered
complex scalars and actual nondegenerate dual subtypes are retained. No
finite-dimensionality, admissibility, faithfulness, nontriviality, unital action,
chosen splitting or duality equivalence is assumed. Zero algebras and modules
remain in scope. Bidual evaluation, injectivity, reflexivity and right-bidual
comparison are outside this proof.
