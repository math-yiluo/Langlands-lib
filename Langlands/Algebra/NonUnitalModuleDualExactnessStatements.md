# Exactness of the actual nondegenerate duality

This statement unit records Renard, *Représentations des groupes réductifs
p-adiques*, French version dated 9 July 2026, I.4.1, lemma, printed page 23 /
PDF page 29: the nondegenerate duality functor is exact. Its construction is
on printed page 22 / PDF page 28. Registered governing source:
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The original nonunital conventions are printed pages 5–7 / PDF pages 11–13,
and canonical complex scalars are I.2.1, printed page 14 / PDF page 20.
These passages were read directly. The registered supplementary
`renard-2010-corrections-complements`, SHA256
`fdf3c88716c294c451c1f6fad67f6b99c95dae670aae0b8ad191ab0a96e69863`,
PDF pages 1–2, was also read; its nearby duality and admissibility
corrections do not change this exactness claim in the governing 2026 edition.
No project errata file for either source was present at the source audit.

Import `Langlands.Algebra.NonUnitalModuleDualExactnessStatements`.
The four declarations are closed `Prop` definitions in `Langlands.Algebra`.
All their mathematical inputs are quantified inside the proposition. The
algebra is an arbitrary possibly noncommutative complex idempotented algebra
with specified `NonUnitalRing A`, `Module ℂ A`,
`IsScalarTower ℂ A A`, `SMulCommClass ℂ A A` and
`hA : IsIdempotented A`. No original carrier is supplied with a complex
module. Its scalars are precisely the canonically recovered
`NondegenerateScalars.complexModule hA hM` from its specified original
additive action and nondegeneracy.

`NonUnitalModuleDualCategoricalExactnessStatement.{uA,uM}` asserts
additivity and exactness of both published actual functors
`NonUnitalModuleDual.leftToRightFunctor hA` and
`NonUnitalModuleDual.rightToLeftFunctor hA`. Their categories are exactly
`NondegenerateModuleCat.{uA,uM} A` and
`RightNondegenerateModuleCat.{uA,uM} A`. The latter is the original
nondegenerate module category over the multiplicative opposite. The target
installs the named structures
`NondegenerateModuleCat.abelian A hA` and
`NondegenerateModuleCat.abelian Aᵐᵒᵖ hA.op`.
Their preadditive structures are the original inherited pointwise Hom
groups, as proved by `NondegenerateModuleCat.abelian_toPreadditive`.
It introduces no replacement Hom groups or categories.

Both `Functor.Additive` witnesses are existential conclusions. They are
installed only after being concluded. The conclusion then requires
`Langlands.Renard.ContravariantSequenceExact` for each functor, together
with reversal of every exact short complex and every short exact complex
in each original source category. A short complex has three objects;
calling it exact imposes exactness at the middle, and does not by itself
impose injectivity or surjectivity at the ends.
For `S : ShortComplex C`, `S.op` reverses the arrows: the displayed image
is `D(M₃) → D(M₂) → D(M₁)`.
The Renard predicate is the conjunction of its two one-sided sequence
conditions, including the boundary monomorphism and epimorphism conclusions
on the actual functor from the opposite category.

`NonUnitalModuleDualMapExactnessStatement.{uA,uM,uN,uP}` quantifies
three arbitrary original additive modules, their specified
`NonUnitalModule A` actions and nondegeneracy witnesses, and original
intertwiners `f : NonUnitalModuleHom A M N` and
`g : NonUnitalModuleHom A N P`. It installs exactly each published
`NonUnitalModuleDual.fullAction` on the actual full dual, as required to
form its actual nondegenerate subtype. Write `D(f)` for the published
`pullback hA hM hN f` and `D(g)` for `pullback hA hN hP g`.
The target asserts all four clauses:

- `Function.Exact f g` implies `Function.Exact D(g) D(f)`.
- Injective `f` gives surjective `D(f)`.
- Surjective `f` gives injective `D(f)`.
- Injective `f`, exact `f,g` and surjective `g` together give injective
  `D(g)`, exact `D(g),D(f)` and surjective `D(f)`.

`NonUnitalModuleDualInjectiveSurjectiveStatement.{uA,uM,uN}` and
`NonUnitalModuleDualSurjectiveInjectiveStatement.{uA,uM,uN}` expose the
two endpoint clauses separately, without a third unused module.
The maps are actual restrictions of full-dual precomposition by the
automatically complex-linear original intertwiner. They do not ask for
externally supplied linear maps or caller-chosen dual objects.
The dual carrier is precisely the published nondegenerate part of the
canonical full complex dual.

The same original-map assertions specialized to `Aᵐᵒᵖ` state the
right-module versions. Their values initially carry a multiplicative
double-opposite action. The published `rightToLeftFunctor hA` composes
`leftToRightFunctor hA.op` with `fromDoubleOppositeFunctor`; its actual
map is `fromDoubleOppositeMap` of this pullback. That explicit transport
keeps the additive carrier and the whole function unchanged and transports
the action by `a ↦ op (op a)`. Consequently the function-exactness,
injectivity and surjectivity interfaces have the same meaning for the
actual transported left maps.

The source explicitly proves reversal of short exact sequences. Additivity,
the two one-sided Renard conditions, arbitrary middle-exact complexes and
standalone endpoint reversals are the standard categorical and elementwise
interfaces of that exactness assertion. Arbitrary middle-exact complexes
can be factored through their image/kernel, and endpoint reversals follow
by completing a mono or epi to a short exact sequence. These formulations
are consequences of the source claim, not additional hypotheses. The
right-module version applies the same source assertion to the opposite
algebra and then the explicit transport.

The source proof restricts to each idempotent fixed part. The decomposition
`M = eM ⊕ {m − e • m}` identifies the full complex dual of `eM`
with functionals on `M` annihilating the complementary summand, exactly
the functionals fixed by right action of `e`. It therefore identifies the
`e`-fixed part of the actual nondegenerate dual with `(eM)*`.
Nondegeneracy lets one test the desired sequence on all fixed parts.
Exactness of the fixed-part functor and of ordinary vector-space duality
then proves the reversed short exact sequence.
This paragraph describes Renard's argument; no exactness proof is
implemented by this statement file. Actual fixed-part restriction and
extension, their inverse/isomorphism and naturality proofs are proof
dependencies, with no such data assumed in these targets.

Algebra and carrier universes are independent throughout. There is no
finite-dimensionality, nontriviality, admissibility, faithfulness,
anti-involution, unital-action, splitting, additive-instance, duality
equivalence or exactness-certificate premise. Zero algebras and zero
modules remain in scope. Exactness proofs, canonical bidual evaluation
and injection, admissible reflexivity and I.4.2 comparisons are separate
successors.
