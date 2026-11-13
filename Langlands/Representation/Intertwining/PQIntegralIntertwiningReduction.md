# Renard VII.3.4, integral form: reduction to the integral identification

Author: Worker 48. Module
`Langlands.Representation.Intertwining.PQIntegralIntertwiningReduction`, namespace
`Langlands.Aubert.General.RepresentedParabolic`. Universe parameters `u, v`.

The module contains one `Prop`-valued definition, one theorem and one definition whose type is
that theorem's implication:

- `PQIntegralIdentificationStatement`: the first clause of the published
  `PQIntegralIntertwiningOperatorStatement`, stated on its own;
- `pqIntegralIntertwiningOperator_of_identification`:
  `PQIntegralIdentificationStatement.{u, v} → PQIntegralIntertwiningOperatorStatement.{u, v}`;
- `pqIntegralIntertwiningOperatorOfIdentification`: a `def` of the same type,
  `PQIntegralIdentificationStatement.{u, v} → PQIntegralIntertwiningOperatorStatement.{u, v}`,
  whose value is the theorem above. It is the declaration recorded for this unit. The
  `linter.defProp` warning (a `def` whose type is a proposition) is switched off for it alone.

This is a conditional reduction. It does not prove the published statement, because it does not
prove `PQIntegralIdentificationStatement`.

## Source

David Renard, *Représentations des groupes réductifs p-adiques*, French version dated
9 July 2026. Literature ID `renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`. VII.3.4, printed
pp.235–236 / PDF pp.241–242. Renard writes "Il est utile de donner une forme plus explicite de
l'opérateur `K_{Q|P}`": the natural isomorphism `F^{<1̄}_{PQ}/F^{≤1̄}_{PQ}(E) ≃ E` comes from
the map `F̃^{<1̄}_{PQ} → E`, `f ↦ ∫_{U∩N̄} f(u) du`, by passing to the quotient. The Proposition
that follows says that `J_{Q|P}(σ)` is the unique intertwining operator with
`J_{Q|P}(σ)(f)(1_G) = ∫_{N̄∩U} f(u) du` on `F̃^{<1̄}_{PQ}(E)`.

## The definition `PQIntegralIdentificationStatement`

The quantifier prefix, hypotheses and body are copied word for word from the first conjunct of
`PQIntegralIntertwiningOperatorStatement` (module
`Langlands.Representation.Intertwining.PQIntegralIntertwiningStatements`). The setting is a
nonarchimedean local field `k`, a connected reductive `G` with the canonical topology on `G(F)`,
represented parabolics `P = MN` and `Q = MU` with the same embedded Levi subgroup
(`l ≫ p = lQ ≫ q`), and a represented parabolic `P̄ = MN̄` opposite to `P` (`lb ≫ pb = l ≫ p`,
`P(F) ∩ P̄(F) = M(F)`). With `V = N̄(F) ∩ U(F)` and any Haar measure `haar` on `V`, the
statement says: for every smooth representation `σ` of `M(F)` there is an
`M(F)`-equivariant linear equivalence
`e : F^{<1̄}_{PQ}/F^{≤1̄}_{PQ}(σ) ≃ σ` such that for every `f ∈ F̃^{<1̄}_{PQ}(σ)`, every
representative `y = f̄` of its class in `r_Q^G i_P^G(σ)`, and every linear form `ℓ` on `σ`, the
function `v ↦ ℓ(f(v))` is `haar`-integrable on `V`, and `ℓ(e([y])) = ∫_V ℓ(f(v)) dhaar(v)`.

The integral is read against linear forms, as in the published statement and in
`IsIntegralIntertwiner`. The meanings of the published objects
(`closureSupportImage`, `boundarySupportImage`, `boundaryVanishingSubfunctor`,
`identityParabolicDoubleCoset`, `Jacquet.Localization.mk`, `Induction.eval`) are those in
[PQIntegralIntertwiningStatements](PQIntegralIntertwiningStatements.md) and
[PQIntertwiningOperatorStatement](PQIntertwiningOperatorStatement.md).

## The theorem `pqIntegralIntertwiningOperator_of_identification`

It has hypothesis `PQIntegralIdentificationStatement.{u, v}` and conclusion exactly the
published `PQIntegralIntertwiningOperatorStatement.{u, v}`, with no other hypothesis.

### Proof

After the common binders are introduced, the hypothesis applied to the same data gives the
first conjunct of the target as it stands.

For the second conjunct, fix a split component `a`, a `PQ`-regular `σ`, and the identification
`e` that the hypothesis supplies for `σ`. The proved theorem
`pqIntertwiningOperator : PQIntertwiningOperatorStatement` (module
`Langlands.Representation.Intertwining.PQIntertwiningOperatorProof`) applied to this `e` gives
an intertwining operator `J` that is unique for the property
`J(f)(1) = e([f̄])` for all `f ∈ F̃^{<1̄}_{PQ}(σ)`.

- **Existence.** For `f ∈ F̃^{<1̄}_{PQ}(σ)`, its image `f̄ = Jacquet.Localization.mk … 1 f` lies
  in `boundarySupportImage … σ` by the definition of that image (witness `f`). So
  `J(f)(1) = e([f̄])`, and the hypothesis gives integrability and
  `ℓ(e([f̄])) = ∫_V ℓ(f(v)) dhaar(v)` for every `ℓ`. Together these give
  `IsIntegralIntertwiner … V haar σ J`.
- **Uniqueness.** Let `J'` satisfy `IsIntegralIntertwiner`. For each `f`, its representative `y`
  and each `ℓ`, `ℓ(J'(f)(1)) = ∫_V ℓ(f(v)) dhaar(v) = ℓ(e([y]))`. Linear forms on a complex
  vector space separate points (Mathlib `Module.forall_dual_apply_eq_zero_iff`, applied to the
  difference). So `J'(f)(1) = e([y])`, and the uniqueness part of `pqIntertwiningOperator` gives
  `J' = J`.

The lemma `Module.forall_dual_apply_eq_zero_iff` uses a projective module, and every vector space
over `ℂ` is free, hence projective.

## The definition `pqIntegralIntertwiningOperatorOfIdentification`

`def pqIntegralIntertwiningOperatorOfIdentification :
PQIntegralIdentificationStatement.{u, v} → PQIntegralIntertwiningOperatorStatement.{u, v} :=
pqIntegralIntertwiningOperator_of_identification.{u, v}`. It adds no content to the theorem. It
records the reduction as a declaration whose type is the implication, as the Library does for
other conditional reductions (for example
`Langlands.Aubert.General.RationalPointFamily.rationalSupportCategoryDecompositionOfWholeStatement`).

## Provenance

Derived. The definition is the first clause of a published statement (Renard VII.3.4, explicit
form), split off so that the second clause is proved from it. The theorem is the routine
argument of Task 5516's context: clause (b) follows from clause (a), the proved characterization
`pqIntertwiningOperator`, and the separation of points by linear forms.

## Dependencies

Imports `Langlands.Representation.Intertwining.PQIntegralIntertwiningStatements` (unchanged) and
`Langlands.Representation.Intertwining.PQIntertwiningOperatorProof`. It uses no `sorry` and no
new axiom.
