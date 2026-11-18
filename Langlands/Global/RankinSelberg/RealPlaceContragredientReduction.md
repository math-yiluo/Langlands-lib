# Reduction of the real-place contragredient pair-factor statement

Module: `Langlands.Global.RankinSelberg.RealPlaceContragredientReduction`. Helper declarations
are in the namespace `Langlands.Global.RankinSelbergGlobal.RealPlaceContragredient`.

Main theorem:
`Langlands.Global.RankinSelbergGlobal.realPlaceContragredientPairLReduction :
RealPlaceContragredientPairLReductionStatement.{u}`.

## What is proved

`RealPlaceContragredientPairLReductionStatement` is stated in
`Langlands.Global.RankinSelberg.RealPlaceContragredientPremises`; see its Markdown. It says that
the published global irreducibility statement
`Automorphic.CuspidalArchimedeanStandardIrreducibleStatement` and the local pairing premise
`RealStandardPairingPairLStatement` (L_R) together imply `RealPlaceContragredientPairLStatement`.
Neither premise is proved here.

The unconditional content is `exists_realStandardInvariantPairing`. Let `F` be a number field
with compact adele quotient, and let `T`, `Td` be actual cuspidal realizations of `GL_(r+1)` with
`Td` contragredient to `T`. Let `v` be a real place, `ds` a parameter of `T` at `v` and `dds` a
parameter of `Td` at `v`. Then there is a nonzero bilinear form
`P : realStandardKFinite (r+1) ds → realStandardKFinite (r+1) dds → ℂ` with
`IsRealStandardInvariantPairing (r+1) ds dds P`.

The main theorem `realPlaceContragredientPairLReduction` takes the premises `hG` and `hL` and the
data of the target. It obtains invariant nonzero pairings `P` for `(ds, dds)` from `(T, Td)` and
`P'` for `(es, ees)` from `(T', Td')`. The irreducibility hypotheses of L_R come from the real
half `(hG F r T).1` of the global statement, applied to `T` with `ds`, `Td` with `dds`, `T'` with
`es` and `Td'` with `ees`. The rank hypotheses are the first components of the parameter
hypotheses. Then

- the first conclusion of L_R for `(ds, dds, P)` with partner `ees` gives
  `den L(dds × ees) = den L(ds.map dualBlock × ees)`;
- the second conclusion of L_R for `(es, ees, P')` with partner `ds.map dualBlock` gives
  `den L(ds.map dualBlock × ees) = den L(ds.map dualBlock × es.map dualBlock)`.

The two equalities compose to the target.

The proof uses only the axioms `propext`, `Classical.choice` and `Quot.sound`.

## Idea

Let `B : T × Td → ℂ` be the contragredient pairing. `IsContragredientOf` provides that `B` is
invariant under the finite, compact and real Lie actions and that `B.flip` is injective. Let
`A`, `Ad` be the injective equivariant maps of the parameters `ds`, `dds`.

Consider the vectors `y` of `T` orthogonal under `B` to the image of every `v`-equivariant map
`Φ` from the standard module of `dds` into `Td`. They form a subspace stable under the whole
operator algebra of `T`, so by irreducibility of `T` it is `0` or everything.

- It is not everything. Otherwise `B(·, Ad f') = 0` for every `f'`, and injectivity of `B.flip`
  and of `Ad` would make the nonzero standard module of `dds` zero.
- So it is `0`. Take `f ≠ 0`. Then `A f ≠ 0` lies outside it, so some equivariant `Φ` and some
  `f'` have `B(A f, Φ f') ≠ 0`. The form `P(f, f') = B(A f, Φ f')` is invariant because `B` is
  invariant and `A`, `Φ` are equivariant.

Quantifying over every equivariant `Φ`, not only `Ad`, makes the subspace stable: composing `Φ`
with an operator of `Td` that commutes with the actions at `v` gives an equivariant map.

This is the argument of the published complex-place module `ComplexPlaceContragredientReduction`,
transferred to a real place. The real-place changes are listed below.

## Declarations

### Equivariant maps

- `IsPlaceEquivariant S v ds Φ`: the linear map `Φ` from `realStandardKFinite n ds` to the
  space of the operator realization `S` carries `realStandardRep n ds l` to the compact action
  `S.realPlaceCompactRepresentation v l` for every `l ∈ O(n)`, and `realStandardLie n ds (1 ⊗ X)`
  to `S.realPlaceLieAction v (1 ⊗ X)` for every real matrix `X`.
- `exists_isPlaceEquivariant_of_parameter`: a real-place parameter gives an injective
  place-equivariant map. It unpacks `HasRealPlaceParameter` and converts its compact and Lie
  clauses, stated with raw right translations and right derivatives, by the Library lemmas
  `OperatorRealization.realPlaceParameter_compact` and `OperatorRealization.realPlaceParameter_lie`
  (module `Langlands.Automorphic.CuspidalArchimedeanComponentUnitaryProof`). The declaration is
  elaborated with `backward.isDefEq.respectTransparency false`, which the manifold structure on
  `GL_n(ℝ)` needs.
- `IsPlaceEquivariant.comp`: composing an equivariant `Φ` with a linear operator `c` of `S`
  gives an equivariant map, if `c` commutes with the compact and Lie actions at `v`.

### The annihilator

- `annihilator S S' B v ds`: the subspace of `y ∈ S` with `B y (Φ f) = 0` for every
  place-equivariant `Φ : realStandardKFinite n ds → S'` and every `f`. `mem_annihilator`
  unfolds membership.
- `annihilator_map`: let `c` be a map of `S` with a `B`-adjoint `c'`, meaning
  `B (c y) x = B y (c' x)`, and let `c'` commute with the actions of `S'` at `v`. Then `c`
  preserves the annihilator, because `c' ∘ Φ` is again equivariant.
- `compact_comm_of_trivial`: if `q` in the product of compact factors has real component `1` at
  `v`, its compact action commutes with the compact action at `v`, because the factors commute
  coordinatewise (`q · realPlaceFactor v l = realPlaceFactor v l · q`). It also commutes with
  the Lie action at `v`, by the Library lemma `compactRepresentation_realPlaceLieAction` and
  `unitaryMatrixComplexLieConjugation_one'`, since conjugation by `q_v = 1` is trivial.
- `annihilator_finite`: finite adelic elements `g` preserve the annihilator. Apply
  `annihilator_map` with adjoint `g⁻¹` on `S'`. The commutation is
  `finiteRepresentation_realPlaceCompactRepresentation` and
  `finiteRepresentation_realPlaceLieAction`.
- `annihilator_compact_trivial`: compact elements with component `1` at `v` preserve the
  annihilator; the adjoint is the inverse.
- `annihilator_placeCompact`: an orthogonal `l` at `v` preserves the annihilator. By invariance
  of `B` at `realPlaceCompactInclusion F n v l`, `B (l y) (Φ f) = B y (l⁻¹ Φ f)`, and
  `l⁻¹ Φ f = Φ (realStandardRep n ds l⁻¹ f)` is annihilated.
- `annihilator_compact`: every standard infinite compact element `k` preserves the annihilator.
  Write `k` as the image of `p` in the compact factors (`toStandardCompact_surjective`). Then
  `p = realPlaceFactor v (p.1 v) · p'` with `p'.1 = update p.1 v 1`. Combine the two previous
  lemmas. The decomposition is the one of the Library's `realFreeSet_compact`.
- `annihilator_lieAction`: every real Lie algebra element `X` preserves the annihilator. By Lie
  invariance, `B (X y) (Φ f) = -B y (X (Φ f))`. The Library's `complexify_action_eq_sum_place`
  splits `X (Φ f)` into its components at the real places and at the complex places.
  - The component at a real place `w ≠ v` commutes with the actions at `v`
    (`realPlaceCompactRepresentation_realPlaceLieAction_of_ne`, `realPlaceLieAction_comm_of_ne`).
  - The component at a complex place commutes with the actions at `v`
    (`realPlaceCompactRepresentation_complexPlaceLieAction`,
    `realPlaceLieAction_comm_complexPlace`).
  - The component at `v` is `Φ` of `realStandardLie n ds (1 ⊗ X_v) f`.

  So each term is annihilated by `y`, and the sum lies in `ker (B y)`.
- `annihilator_complexLieAction`: extension to the complexified Lie algebra, by
  `TensorProduct.inductionOn` and `z ⊗ X = z • complexify X`.
- `annihilator_enveloping`: extension to the enveloping algebra, generated by the complexified
  Lie algebra (`Langlands.Algebra.LieCasimir.enveloping_adjoin_range`).
- `annihilator_operator`: the whole concrete operator algebra preserves the annihilator, by
  `Algebra.adjoin_induction` over its finite, compact and enveloping generators.
- `annihilatorSubrepresentation S S' B hB v ds`: the annihilator as a `Subrepresentation` of
  `S.representation`.

### The induced pairing

- `inducedPairing B A Φ`: the bilinear form `(f, f') ↦ B (A f) (Φ f')`. `inducedPairing_apply`
  evaluates it (by `rfl`).
- `realPlaceLieAction_one_tmul`: the Lie action at `v` of `1 ⊗ X` is the real Lie action of
  `realPlaceLieInclusion F n v X` (`realPlaceComplexLieInclusion_tmul`, `complexify_apply`).
- `isRealStandardInvariantPairing_induced`: if `B` is invariant and `A`, `Φ` are
  place-equivariant, `inducedPairing B A Φ` satisfies `IsRealStandardInvariantPairing`. Compact
  invariance uses invariance of `B` at `realPlaceCompactInclusion F n v l`; Lie invariance uses
  `realPlaceLieAction_one_tmul` and invariance of `B` at `realPlaceLieInclusion F n v X`.

### Conclusion

- `mem_annihilator_of_eq_top`, `eq_zero_of_mem_annihilator`: if the annihilator
  subrepresentation is `⊤`, every vector lies in the annihilator; if it is `⊥`, its only vector
  is `0`.
- `annihilatorSubrepresentation_ne_top`: if `B.flip` is injective, the standard module of `ds`
  is nontrivial and `Ad` is an injective place-equivariant map into `S'`, the annihilator is not
  `⊤`.
- `exists_inducedPairing_ne_zero`: if the annihilator of `dd` is `⊥`, the standard module of `d`
  is nontrivial and `A` is injective and place-equivariant, some `inducedPairing B A Φ` is a
  nonzero invariant pairing.
- `exists_realStandardInvariantPairing`: the theorem stated above. Nontriviality of the standard
  modules is the Library's `realStandardNontrivial`, from the rank hypotheses. Then it applies
  `T.irreducible` to `annihilatorSubrepresentation T.realization Td.realization B hB v dds`.
- `realPlaceContragredientPairLReduction`: the main theorem, as described above.

## Implementation notes

- The module declares local `AddCommGroup` instances on the Library's submodule types and
  `attribute [local instance 100] LieRing.ofAssociativeRing`, as in the complex-place module.
- Equations inside `B (·) (·)` are transported with `congrArg` instead of `rw`.

## Provenance

All declarations are internal. The argument that an invariant pairing of global realizations
restricts to a nonzero invariant pairing of local components is standard. It is implemented
directly from the Library's definitions of operator realizations, contragredient pairings and
real-place parameters, following the published complex-place module
`ComplexPlaceContragredientReduction`.
