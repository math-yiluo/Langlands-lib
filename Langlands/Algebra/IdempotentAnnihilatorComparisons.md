# Quotient idempotence and canonical fixed-part comparisons

The theorem `Langlands.Algebra.idempotentAnnihilatorComparisons` proves exactly
`Langlands.Algebra.IdempotentAnnihilatorComparisonsTheorem.{uA,uM,uN,uC}` from
`Langlands.Algebra.IdempotentAnnihilatorComparisonStatements`. Its complete type
has no additional premises. The two constituent closed families are also proved
as `idempotentAnnihilatorQuotientIdempotence` and
`idempotentAnnihilatorFixedPartComparison`.

Worker 1151 authored this Lean proof and English documentation. Worker 6 supplied
the passage analysis and elementary ambient-generalization argument used by the
task. The statement pair and all its imports are retained unchanged. Helpers
below are in `Langlands.Algebra.IdempotentAnnihilatorComparisons`.

## Source and scope

The governing original is David Renard, *Représentations des groupes réductifs
p-adiques*, French version dated **9 July 2026**, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`,
at `/home/taskhub/central-library/Renard--Representations des groupes reductifs p-adiques (2026 version)--2026.pdf`.
The quotient definition and unnumbered idempotence lemma occur in I.3.2,
printed page 20 / PDF page 26. The fixed-part quotient projection comparison
(I.3.2.2) and its argument occur on printed page 21 / PDF page 27. The
original-action conventions are on printed page 6 / PDF page 12, and the
corner functor is defined in I.3.1 on printed page 19 / PDF page 25. All these
pages were read for this proof, and the source fingerprint was verified.

The registered supplementary `renard-2010-corrections-complements`, SHA256
`fdf3c88716c294c451c1f6fad67f6b99c95dae670aae0b8ad191ab0a96e69863`,
at `/home/taskhub/pilot/literature/Renard — Représentations des groupes réductifs p-adiques- corrections et compléments (2010 edition errata).pdf`,
was read at PDF pages 1–2 and its fingerprint verified. These corrections
concern the neighboring tensor injection and later simple-module argument;
the 2026 French original governs this proof. No separate project errata
file for these sources was found.

Renard states the results for nondegenerate modules over a complex algebra
with idempotents. This proof establishes the published internal strengthening
for every associative `NonUnitalRing A`, idempotent `e`, and specified original
additive `NonUnitalModule A M`. Neither a unit-action law nor nondegeneracy,
local units, nontriviality, dimension, or an additional scalar structure is
required. In particular, zero idempotents, zero original actions, and zero
carriers are included by the universal statement.

The actual functor comparisons and their naturality are internal categorical
packaging of these underlying additive-action results. The proof does not
supply the separate correspondence respecting complex scalars, tensor
induction (I.3.2.1), generatedness, the simple-class bijection, or the later
category equivalence. Specializing the fixed-part result to the separately
constructed induced module recovers the underlying comparison in (I.3.2.2).

## Actual objects, actions, and maps

Write `F(M) = NonUnitalSubmodule.idempotentAnnihilator e M`,
`Q(M) = annihilatorQuotientCarrier e M`, and
`q_M = annihilatorQuotientProjection e M`. The proof imports the published
`NamedCarrier` construction through the statement module. Its quotient is the
actual integer-compatible stable-subgroup quotient of the original additive
group, with the registered named `annihilatorQuotientAddCommGroup` and
`annihilatorQuotientModule` structures at both quotient levels. Its induced
maps are exactly `NonUnitalModuleHom.annihilatorQuotientMap`.

The fixed carrier is the actual subtype
`NonUnitalModuleCorner.FixedPart e M`, with inherited
`fixedPartAddCommGroup` and original-action `fixedPartModule` over the named
`Idempotent.Corner.ring`. Write `J(f) = NonUnitalModuleCorner.restrict e f`.
The comparison's full forward linear map is exactly `J(q_M)`.
These registered structures agree definitionally with the explicitly selected
structures in the target. No replacement quotient or action is introduced.

The ring universe `uA`, pointwise carrier universes `uM` and `uN`, and
categorical carrier universe `uC` remain independent. Categorical functors use
a fixed carrier universe `uC`; pointwise naturality allows different source
and target carrier universes.

## Implemented quotient proof

`quotient_annihilator_eq_zero` lifts `x : Q(M)` to a representative `m : M`
using the actual projection's surjectivity. If `x` belongs to `F(Q(M))`, then
for every `a : A`, the zero-coset criterion shows that `(e*a) • m` belongs
to `F(M)`. The published annihilator lemma says that `e` kills this vector.
Associativity of the original action and `e*(e*a) = e*a` therefore show that
`(e*a) • m = 0`. Hence `m` belongs to `F(M)` and `x = 0`. This implements
the source's representative argument without needing its stronger hypotheses.

`second_projection_bijective` combines the additive zero-kernel injectivity
criterion with the actual second projection's surjectivity.
`secondProjectionInverse` is the published
`NonUnitalModuleHom.annihilatorQuotientDesc` applied to the identity on `Q(M)`;
annihilator vanishing supplies its descent hypothesis. Its composite after
the second projection is the identity by the descent formula. The other
composite is the identity by `annihilatorQuotient_hom_ext`, checking all
representatives. Thus both identities hold as complete original-linear maps.

`map_projection` uses the same quotient-map extensionality principle and the
actual induced-map representative formula to prove `Q(q_M) = q_Q(M)` as an
entire original-linear map. `quotient_idempotence` assembles all four required
pointwise conjuncts, including the existential inverse.

`quotient_naturality` obtains the forward whole-map square from the published
`annihilatorQuotientMap_comp_projection` applied to `Q(f)`. To prove the inverse
square for arbitrary supplied two-sided inverses, it lifts an arbitrary element
of `Q(Q(M))` along the second projection. Evaluating the supplied left inverse
identities at that representative and at its `Q(f)` image gives the desired
equality. The forward representative formula identifies the intermediate
values. The proof accepts every inverse satisfying the target's two identities;
it does not restrict the assertion to the chosen descended inverse.

## Implemented fixed-part proof

`fixed_projection_bijective` proves injectivity of `J(q_M)` by the additive
zero-kernel criterion. A fixed vector mapping to zero belongs to `F(M)` by
the actual zero-coset test; it is killed by `e` and also fixed by `e`, so it
is zero. For surjectivity, lift a fixed quotient vector to `m : M` and use
`NonUnitalModuleCorner.projection e m`, whose underlying vector is `e • m`.
The original-linearity of `q_M` and fixedness of the target show that this
vector has exactly the desired image. Idempotence supplies its fixedness.
This direct representative argument replaces the source's appeal to exactness.

`fixedProjectionEquiv` applies `LinearEquiv.ofBijective` to the actual linear
map `J(q_M)`. Its entire forward map is therefore definitionally that
restriction. `fixed_comparison` selects the equivalence's inverse linear map,
uses its two full composite identities, and provides the equivalence and both
specified equalities as existential conclusions.

`fixed_naturality` proves the forward square by extensionality of linear maps
and of the fixed subtypes, using the induced quotient-map formula. For the
inverse square it lifts an arbitrary fixed quotient vector along the now
proved surjective `J(q_M)` and evaluates the supplied left inverse identities.
The whole forward square identifies the remaining values. Again the argument
applies to every pair of two-sided corner-linear inverses.

## Natural isomorphisms and inclusion identities

`quotientIso` bundles the actual second projection and its descended inverse
as an isomorphism in the published ambient `NonUnitalModuleCat`.
`quotientNaturalIso` uses `NatIso.ofComponents` with the full forward
naturality square. Its forward natural transformation is exactly the left
whiskering of `annihilatorQuotientπ` by the actual quotient functor.
`nondegenerateQuotientIso` uses `ObjectProperty.homMk` to lift those same
morphisms to the actual nondegenerate full subcategory, and
`nondegenerateQuotientNaturalIso` packages them naturally.
`quotient_natural_iso` proves the specified forward transformation identities
and both inclusion comparisons by natural-transformation extensionality and
definitional equality of the component functions. The inverse components
are the same descended maps on the same named structures.

`fixedIso` bundles `fixedProjectionEquiv` using `LinearEquiv.toModuleIso` in
the actual corner `ModuleCat`. `fixedNaturalIso` packages its components using
`NatIso.ofComponents`. Its forward transformation is precisely the right
whiskering of the actual `annihilatorQuotientπ` by the actual corner functor.
`nondegenerateFixedNaturalIso` uses those same components on the underlying
ambient objects of nondegenerate modules. `fixed_natural_iso` proves the
specified forward maps and both whole-transformation restriction identities
by extensionality and definitional equality of components, including inverses.

The two closed family theorems universally quantify their inputs and assemble
the pointwise, naturality, and categorical results in the statement's order.
`idempotentAnnihilatorComparisons` conjoins them with exactly the aggregate
published target as its complete type. The final examples verify that type
at arbitrary universes and unequal assignments `(2,1,0,3)` and `(0,1,2,0)`.
