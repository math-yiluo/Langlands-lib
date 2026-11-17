# Semisimple groups and commutative normal subgroups: proof

This module proves the published statement
`Langlands.GroupScheme.SemisimpleCommutativeNormalSubgroupStatement.{u}`
(module `Langlands.GroupScheme.Reductive.SemisimpleCommutativeNormalStatement`;
Milne, *Algebraic Groups* (2017), Proposition 19.3) as the theorem

```text
Langlands.GroupScheme.semisimpleCommutativeNormalSubgroup :
  SemisimpleCommutativeNormalSubgroupStatement.{u}
```

The statement is unchanged and no hypotheses are added. The axioms used are
`propext`, `Classical.choice` and `Quot.sound`.

Throughout, `k` is a field, `G` is a smooth connected affine group scheme over
`Spec k`, and "no commutative normal subgroup" is the statement's local
proposition: every closed subgroup `j : H ⟶ G` with `H` smooth, connected and
commutative and with normal image has `SubgroupFunctor.range j = ⊥`.

## Route

The proof does not follow Milne's derived-series argument for the converse,
because the Library has no theorem that the derived series of a group scheme
terminates. It uses only theorems already published in the Library; in
particular it does not use the separately stated Milne 19.2(a)
(`PerfectFieldSemisimpleRadicalStatement`) or the radical characterization of
semisimplicity (`SemisimpleRadicalCharacterizationStatement`).

- **Semisimple ⇒ no commutative normal subgroup.** A commutative subgroup is
  solvable, so it is central (Library theorem on normal solvable subgroups of
  reductive groups). Hence it factors through the finite centre, so it is a
  finite smooth connected group, which is trivial.
- **Converse over a perfect field.** First, the ground-field unipotent radical
  is trivial: a nontrivial smooth connected unipotent normal subgroup would
  contain a nontrivial smooth connected central subgroup stable under
  conjugation by `G`, which is commutative and normal in `G`. Over a perfect
  field this makes `G` connected reductive. Second, the geometric solvable
  radical of `G` is a central torus defined over `k`, hence a commutative normal
  subgroup, hence trivial; so over `k̄` there is no nontrivial smooth connected
  solvable normal subgroup, the centre over `k̄` is finite, `G_{k̄}` is
  semisimple, and semisimplicity descends to `G`.

## Declarations

All auxiliary declarations live in the namespace
`Langlands.GroupScheme.SemisimpleCommutativeNormal`.

### `id_eq_one_of_isFinite`

For a group scheme `H` over `Spec k` with `H.X.hom` smooth and finite and
`H.X.left` connected, the identity of `H.X` equals the unit morphism `1`.

Proof as implemented. The unit section `s = η[H.X].left` satisfies
`s ≫ H.X.hom = 𝟙`, so it is a closed immersion
(`isClosedImmersion_of_comp_eq_id`). `H.X.left` is reduced because it is smooth
over a field (`SmoothReducedProof.isReduced_of_smooth_over_field`). The fibre
of the finite morphism `H.X.hom` over the single point of `Spec k` is
discrete (`Scheme.Hom.isDiscrete_preimage_singleton`), and this fibre is all of
`H.X.left`; a discrete connected space is a subsingleton. So `s` is surjective,
hence an isomorphism (`isIso_of_isClosedImmersion_of_surjective`, which uses
reducedness of the target). Then `H.X.hom = inv s` is an isomorphism, in
particular a monomorphism, and `𝟙 H.X` and `1` agree after composing with it.

### `range_eq_bot_of_isSemisimple` (first direction)

If `IsSemisimple G`, then every smooth connected commutative closed subgroup
`j : H ⟶ G` with normal image has `SubgroupFunctor.range j = ⊥`.

Proof as implemented. `H` is affine over `Spec k` because `j` is a closed
immersion into the affine `G`. `IsCommMonObj H.X` gives
`IsSolvableGroupScheme H` (`isSolvableGroupScheme_of_isCommMonObj`), so
`IsSolvableGroupScheme.isCentral_of_normal_of_isConnectedReductive_field`
(module `Rational/NormalSolvableCentrality`) shows `IsCentral j`. Let
`z : Z ⟶ G` be the closed subgroup with finite `Z.X.hom` and image the centre,
given by `IsSemisimple.hasFiniteCenter`. Centrality puts the point
`𝟙 H.X ≫ j.hom.hom` in the image of `z`, so `j.hom.hom.left` factors as
`y.left ≫ z.hom.hom.left`. This composite is a closed immersion, hence finite,
and `z.hom.hom.left` is a closed immersion, hence separated, so `y.left` is
finite (`IsFinite.of_comp`), and `H.X.hom = y.left ≫ Z.X.hom` is finite. By
`id_eq_one_of_isFinite`, `𝟙 H.X = 1`, and
`CenterQuotient.range_eq_bot_of_id_eq_one` gives `range j = ⊥`.

### `hasTrivialUnipotentRadical_of_noCommutativeNormal`

For affine `G` (any field) with no commutative normal subgroup,
`HasTrivialUnipotentRadical G` holds: every smooth connected unipotent closed
subgroup `u : U ⟶ G` with normal image has `range u = ⊥`.

Proof as implemented. Suppose `range u ≠ ⊥`; then `range (𝟙 U) ≠ ⊥` (via
`CenterQuotient.id_eq_one_of_range_id_eq_bot` and
`range_eq_bot_of_id_eq_one`). Normality of `range u` makes it stable under the
conjugation action `AutomorphicAction.conjugation (𝟙 G)`, so this action
restricts to an action `aU` of `G` on `U`
(`AutomorphicAction.onRepresentedSubgroup`). The Library theorem
`hasNontrivialSmoothStableCentralSubgroup_of_isUnipotent` (module
`Rational/UnipotentSmoothCenter`) applied to `aU` gives a smooth connected
closed subgroup `w : W ⟶ U`, central in `U`, stable under `aU`, with
`range w ≠ ⊥`. Centrality gives `IsCommMonObj W.X`. Stability under `aU`,
rewritten with `onRepresentedSubgroup_act_comp`, says that `range (w ≫ u)` is
normal in `G`, and `w ≫ u` is a closed subgroup. The hypothesis gives
`range (w ≫ u) = ⊥`, hence `𝟙 W.X = 1` (cancel the monomorphism
`(w ≫ u).hom.hom`), hence `range w = ⊥`, a contradiction.

### `isSemisimple_of_noCommutativeNormal`

For connected reductive `G` (any field) with no commutative normal subgroup,
`IsSemisimple G`.

Proof as implemented. `reductiveGeometricSolvableRadicalExists` gives
`r : R ⟶ G` with `IsGeometricSolvableRadical r`, and
`IsGeometricSolvableRadical.isTorus_and_isCentral_of_structural` together with
`algClosedReductiveNormalSolvableTorus` shows that `R` is a torus and `r` is
central. So `R` is commutative (`IsTorus.isCommMonObj`), `range r` is normal
(`IsCentral.range_isNormal`), and the hypothesis gives `range r = ⊥`. Over
`k̄ = AlgebraicClosure k`, the base change of `r` is the solvable radical of
`G_{k̄}`, so every smooth connected solvable normal closed subgroup of
`G_{k̄}` has image inside `(range r)_{k̄} = ⊥_{k̄} = ⊥`
(`SubgroupFunctor.range_baseChangeHom`, `SubgroupFunctor.bot_baseChange`),
i.e. `HasTrivialSolvableRadical G_{k̄}`. Then
`HasTrivialSolvableRadical.hasFiniteCenter` gives a finite centre for `G_{k̄}`,
which is connected reductive (`IsConnectedReductive.baseChange_toAlgebraicClosure`),
so `G_{k̄}` is semisimple, and `IsSemisimple.of_fieldExtension` descends this to
`G`.

### `Langlands.GroupScheme.semisimpleCommutativeNormalSubgroup`

The first conjunct is `range_eq_bot_of_isSemisimple`. For the second, assume
`PerfectField k` and no commutative normal subgroup.
`hasTrivialUnipotentRadical_of_noCommutativeNormal` together with the
hypotheses `Smooth G.X.hom`, `IsAffineHom G.X.hom` and `ConnectedSpace G.X.left`
gives `IsPseudoReductive G`; `perfectFieldPseudoReductive` turns this into
`IsConnectedReductive G`; and `isSemisimple_of_noCommutativeNormal` concludes.

## Relation to the source

Milne's first direction passes to `k^a` and uses that the radical of `G_{k^a}`
is trivial. Here semisimplicity is the Library's `IsSemisimple` (connected
reductive with finite centre), so the argument instead uses centrality of
smooth connected solvable normal subgroups of reductive groups and finiteness
of the centre. Milne's converse uses Proposition 19.2(a) and the derived series
of `R(G)`; here the unipotent case is handled by a stable central subgroup of
the unipotent subgroup, and the remaining case by the fact that the geometric
solvable radical of a reductive group is a central torus defined over `k`.
Perfectness of `k` is used only through `perfectFieldPseudoReductive`.
