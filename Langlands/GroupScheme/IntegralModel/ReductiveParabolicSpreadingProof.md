# Simultaneous good reductive and parabolic spreading: proof

Worker 4668, for task `8b53f86e-c91d-47ab-b631-e30de865fbbe`.

`Langlands.GroupScheme.IntegralModel.ReductiveParabolicSpreading.existence`
proves the Library proposition
`Langlands.GroupScheme.IntegralModel.ReductiveParabolicSpreading.ExistenceStatement.{u}`
of `Langlands.GroupScheme.IntegralModel.ReductiveParabolicSpreadingStatement`.
The theorem's type is exactly that proposition. The universe `u` is arbitrary,
and the theorem has no premises. The statement module and its companion are
unchanged.

For every number field `F : Type u`, every actual group scheme `G` over
`Spec F` with `IsConnectedReductive G`, and every actual homomorphism
`p : P ⟶ G` with `IsParabolicSubgroup p`, the theorem gives a finite set `S`
of finite places of `F` and a term of the published
`ModelData ((S : Set (FinitePlace F)).integer F) F p`. The ring is Mathlib's
actual S-integer subalgebra, with its inferred inclusion into `F` and its
fraction-ring structure. Non-split and anisotropic groups are included, and
so is the improper parabolic `P = G`. No cocharacter, Levi decomposition,
representation, model or exceptional set is supplied as input.

## The implemented term

The proof is a single composition of published Library theorems:

```lean
theorem existence : ExistenceStatement.{u} :=
  existenceStatement_of_spreadingStatements genericReductivitySpreading parabolicDynamic
```

- `existenceStatement_of_spreadingStatements` (module
  `IntegralModel.ConditionalReductiveParabolicSpreading`) proves
  `GenericReductivitySpreadingStatement.{u} → ParabolicDynamicStatement.{u} →
  ExistenceStatement.{u}`.
- `Langlands.GroupScheme.genericReductivitySpreading` (module
  `Reductive.GenericSpreadingProof`) proves
  `GenericReductivitySpreadingStatement.{u}` unconditionally.
- `Langlands.GroupScheme.parabolicDynamic` (module
  `Absolute.ParabolicDynamicProof`) proves `ParabolicDynamicStatement.{u}`
  unconditionally.

`lean_check` in environment `bb168ec3-1031-46d9-816b-5c2ed7bbe1a6` compiled
the module with no errors or warnings. It reported only the axioms
`propext`, `Classical.choice` and `Quot.sound` for `existence`.

## How the models and fibres are constructed

The steps below are carried out by the imported declarations. They show how
each `ModelData` field is obtained for the actual supplied `G` and `p`. Names
are in `Langlands.GroupScheme`, `Langlands.GroupScheme.IntegralModel` or
`Langlands.Global`, as in the cited modules.

1. **Generic cocharacter.** `IsParabolicSubgroup p` gives `IsClosedSubgroup p`.
   The forward implication of `parabolicDynamic` then gives a cocharacter
   `χ : Gm(F) ⟶ G` with `SubgroupFunctor.range p = Dynamic.parabolic χ`.
   This is equality of subgroup functors on every scheme over `Spec F`. The
   cocharacter is built inside `parabolicDynamic`: a maximal torus inside `P`,
   a finite Galois splitting field, the split classification there, and
   Galois descent of the resulting cocharacter.

2. **Smooth ambient model.** `ArithmeticSpreading.reductiveModelData`, applied
   to `genericReductivitySpreading`, starts from `smoothIntegralModelData F G`.
   That construction gives a finite set `S₀` and an actual smooth affine
   `IntegralModel R₀ F G` over `R₀ = (S₀ : Set (FinitePlace F)).integer F`.
   It uses finitely presented subalgebra descent of the scheme, smoothness
   descent and group-law descent. The `smooth` and `isAffineHom` fields of
   `IsConnectedReductive G` supply its inputs.

3. **Good reductive fibres.** `adelicSIntegersNoetherian` makes `R₀`
   Noetherian. Transport along the model's `genericIso` gives connected
   reductivity of the actual pullback along `Spec.algebraMap R₀ F`.
   `genericReductivitySpreading` then gives a nonzero `r ∈ R₀`. Every field
   point of `R₀` on which `r` does not vanish has a connected reductive actual
   fibre. `numberFieldSIntegersUnitStage` chooses a larger finite set `S₁`
   in which `r` becomes a unit. The model is replaced by
   `ArithmeticSpreading.enlargeModel` along the literal inclusion of S-integer
   rings. `fieldReductive_baseChange_of_isUnit` uses the pullback-composition
   isomorphism `baseChangeCompIso`. It gives `IsConnectedReductive` for the
   pullback along `Spec.algebraMap R₁ k`, for every field `k : Type u` and
   every `Algebra R₁ k`.

4. **Extending the cocharacter.** `ArithmeticSpreading.enlargedCocharacterData`
   enlarges `S₁` to the final finite set `S`. Write `R` for its S-integer ring
   and `N` for the canonical enlargement of the model. The construction gives
   an actual cocharacter `Gm(Spec R) ⟶ N.group`. Its generic base change,
   composed with `N.genericIso.hom`, is exactly `χ`. `smooth_enlargeModel`
   and `fieldReductive_enlargeModel` keep smoothness and the all-field
   connected reductivity after this enlargement. `isReductive_of_fieldReductive`
   then proves the exact integral `IsReductive N.group`. It applies the
   all-field statement to the geometric points used in `IsReductive`.

5. **Parabolic model and closed inclusion.** The range equality of step 1 is
   transported through `N.genericIso` by `Dynamic.parabolic_eq_comap_of_iso`
   and the cocharacter equation of step 4. It identifies
   `range (p ≫ N.genericIso.inv)` with the generic dynamic subgroup of the
   integral cocharacter. `IntegralModel.DynamicParabolic.modelData` then
   builds the final data:
   - `ambient` is `N`, and `parabolic` has group
     `Dynamic.Affine.parabolicScheme` of the integral cocharacter. Its
     structural map is affine because the dynamic inclusion is a closed
     immersion into an affine model. It is flat and locally of finite type
     because it is smooth. Its `genericIso` to the supplied `P` comes from the
     uniqueness of representing subgroups.
   - `inclusion` is the dynamic inclusion `Dynamic.Affine.parabolicHom`. Its
     `generic_comm` is the exact square with the original `p`.
     `closedImmersion` is `Dynamic.Affine.isClosedSubgroup_parabolicHom`.
   - `reductive` is step 4, and `parabolicSmooth` is
     `Dynamic.Affine.smooth_parabolicScheme` over the Noetherian ring `R`.
   - `fieldReductive` is the all-field statement of step 4.
   - `fieldParabolic k`: for the actual base change along
     `Spec.algebraMap R k`, the changed inclusion is closed. It represents the
     dynamic subgroup of the changed cocharacter. The reverse implication of
     `parabolicDynamic`, applied over `k` to the connected reductive fibre,
     gives `IsParabolicSubgroup` of that same base-changed homomorphism.
   - `fieldConnected k` comes from
     `DynamicConnected.connectedSpace_of_isRepresentedBy_parabolic`. It uses
     the smooth, affine and connected ambient fibre over `k` and the same
     represented dynamic subgroup.

The finite set and both models are chosen before the quantifier over `k`.
All three field clauses use the predicates `IsConnectedReductive`,
`IsParabolicSubgroup` and `ConnectedSpace` without modification, along the
actual morphism `Spec.algebraMap R k`.

## Comparison with the source

The statement companion cites Getz and Hahn, *An Introduction to Automorphic
Representations* (2024), source `getz-hahn-2024-automorphic-representations`:
Proposition 2.4.8 with its proof (printed pp.61–62 / PDF pp.78–79) and section B.3 with
Proposition B.3.1 and Theorems B.3.2–B.3.3 (printed pp.544–547 / PDF
pp.549–552). The implemented route follows the outline of their proof of
Proposition B.3.1. There, `P = P(λ)` for a cocharacter `λ` over the field
(Theorem B.3.3, which cites Milne Theorem 25.1). After enlarging the set of
places, a reductive model of `G` is taken and `λ` extends to an integral
cocharacter `Λ`. The integral parabolic is `P(Λ)`, which is smooth and
parabolic by Theorem B.3.2.

The Lean route differs in three ways:

- The ambient model comes from finitely presented subalgebra descent, not from
  a schematic closure in a faithful representation.
- Good reductive fibres come from the published principal-open spreading
  theorem, not from Conrad's results cited in Proposition 2.4.8.
- The cocharacter is extended directly into the ambient model, without a
  maximal-torus model.

The parabolic model is the actual dynamic subgroup scheme, not a schematic
closure. The Levi and unipotent-radical parts of Proposition B.3.1 are not
part of the target and are not constructed. The provenance of this module is
internal: it composes published Library theorems and asserts nothing new from
the literature.
