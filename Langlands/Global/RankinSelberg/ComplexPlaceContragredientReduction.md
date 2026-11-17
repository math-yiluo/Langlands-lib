# Reduction of the contragredient-parameter premise

Module: `Langlands.Global.RankinSelberg.ComplexPlaceContragredientReduction`. Helper
declarations are in the namespace
`Langlands.Global.RankinSelbergGlobal.ComplexPlaceContragredient`.

Main theorem:
`Langlands.Global.RankinSelbergGlobal.complexPlaceContragredientParameterReduction :
ComplexPlaceContragredientParameterReductionStatement.{u}`.

## What is proved

`ComplexPlaceContragredientParameterReductionStatement` is stated in
`Langlands.Global.RankinSelberg.ComplexPlaceContragredientPremises`; see its Markdown for the
statements. It says that the global irreducibility premise
`ComplexPlaceParameterIrreducibleStatement` (G) and the local pairing premise
`ComplexStandardPairingParameterStatement` (L) together imply
`ComplexPlaceContragredientParameterStatement`. Neither G nor L is proved here.

The unconditional content is `exists_complexStandardInvariantPairing`. Let `F` be a number field
with compact adele quotient, and let `T`, `Td` be actual cuspidal realizations of `GL_(r+1)` with
`Td` contragredient to `T`. Let `w` be a complex place, `d` a parameter of `T` at `w` and `dd` a
parameter of `Td` at `w`. Then there is a nonzero bilinear form
`P : complexStandardKFinite (r+1) d → complexStandardKFinite (r+1) dd → ℂ` with
`IsComplexStandardInvariantPairing (r+1) d dd P`.

The main theorem then applies L to `P`. The two irreducibility hypotheses of L come from G
applied to `T` with `d` and to `Td` with `dd`. Their length hypotheses are the first components
of the two parameter hypotheses.

The proof uses only the axioms `propext`, `Classical.choice` and `Quot.sound`.

## Idea

Let `B : T × Td → ℂ` be the contragredient pairing. `IsContragredientOf` provides that `B` is
invariant under the finite, compact and real Lie actions and that `B.flip` is injective. Let
`A`, `Ad` be the injective equivariant maps of the parameters `d`, `dd`.

Consider the vectors `y` of `T` orthogonal under `B` to the image of every `w`-equivariant map
`Φ` from the standard module of `dd` into `Td`. They form a subspace that is stable under the
whole operator algebra of `T`, so by irreducibility of `T` it is `0` or everything.

- It is not everything. Then `B(·, Ad f') = 0` for every `f'`, and injectivity of `B.flip` and
  of `Ad` would make the nonzero standard module of `dd` zero.
- So it is `0`. Take `f ≠ 0`. Then `A f ≠ 0` lies outside it, so some equivariant `Φ` and some
  `f'` have `B(A f, Φ f') ≠ 0`. The form `P(f, f') = B(A f, Φ f')` is invariant because `B` is
  invariant and `A`, `Φ` are equivariant.

Using every equivariant `Φ`, and not only `Ad`, makes the subspace stable. Compose `Φ` with any
operator of `Td` that commutes with the actions at `w`, and the result is still equivariant.

## Declarations

### Equivariant maps

- `ofUnitary l`: a unitary matrix `l` as an element of `unitaryCompact ℂ n ⊆ GL_n(ℂ)`.
  `ofUnitary_unitaryGroup` says its underlying unitary matrix is `l` (by `rfl`).
- `IsPlaceEquivariant S w ds Φ`: the linear map `Φ` from `complexStandardKFinite n ds` to the
  space of the operator realization `S` intertwines two pairs of actions.
  - `complexStandardTranslate n ds k` with the compact action at `w` of the unitary matrix
    underlying `k`.
  - `complexStandardDerivative n ds X` with the Lie action at `w` of `1 ⊗ X`.

  This is the equivariance in the Library's `HasComplexPlaceParameter`, without the existence
  quantifiers over membership proofs.
- `isPlaceEquivariant_of_parameter`: the map of a parameter is place-equivariant. The terms
  `⟨_, hf⟩` of the parameter and `complexStandardTranslate`/`complexStandardDerivative` agree by
  proof irrelevance. This declaration is elaborated with
  `backward.isDefEq.respectTransparency false`, which the manifold structure on `GL_n(ℂ)` needs.
- `IsPlaceEquivariant.comp`: composing an equivariant `Φ` with a linear operator `c` of `S`
  gives an equivariant map, if `c` commutes with the compact and Lie actions at `w`.

### The annihilator

- `annihilator S S' B w ds`: the subspace of `y ∈ S` with `B y (Φ f) = 0` for every
  place-equivariant `Φ : complexStandardKFinite n ds → S'` and every `f`. `mem_annihilator`
  unfolds membership.
- `annihilator_map`: the general stability criterion. Let `c` be a map of `S` with a `B`-adjoint
  `c'`, meaning `B (c y) x = B y (c' x)`, and let `c'` commute with the actions of `S'` at `w`.
  Then `c` preserves the annihilator, because `c' ∘ Φ` is again equivariant.
- `compact_comm_of_trivial`: if `q` in the product of compact factors is `1` at `w`, its
  compact action commutes with the compact action at `w`, because the factors commute
  coordinatewise. It also commutes with the Lie action at `w`, by the Library lemma
  `compactRepresentation_complexPlaceLieAction`, since conjugation by `q_w = 1` is trivial.
- `annihilator_finite`: finite adelic elements `g` preserve the annihilator. Apply
  `annihilator_map` with adjoint `g⁻¹` on `S'`. The adjoint relation follows from finite
  invariance of `B` and `ρ(g) ρ(g⁻¹) = 1`. The commutation is the Library's
  `finiteRepresentation_complexPlaceCompactRepresentation` and
  `finiteRepresentation_complexPlaceLieAction`.
- `annihilator_compact_trivial`: compact elements equal to `1` at `w` preserve the annihilator.
  Apply `annihilator_map` with adjoint the inverse, which is also `1` at `w`, and use
  `compact_comm_of_trivial`.
- `annihilator_placeCompact`: a unitary `l` at `w` preserves the annihilator. By invariance,
  `B (l y) (Φ f) = B y (l⁻¹ Φ f)`. By equivariance, `l⁻¹ Φ f = Φ (translate by l⁻¹ of f)`. That
  vector is annihilated.
- `annihilator_compact`: every standard infinite compact element `k` preserves the annihilator.
  Write `k` as the image of `p` in the compact factors (`toStandardCompact_surjective`). Then
  `p = (p_w at w) · p'` with `p'` equal to `1` at `w`. Combine the two previous lemmas.
- `annihilator_lieAction`: every real Lie algebra element `X` preserves the annihilator. By Lie
  invariance, `B (X y) (Φ f) = -B y (X (Φ f))`. The Library's `complexify_action_eq_sum_place`
  splits `X (Φ f)` into its components at the real places and at the complex places.
  - Components at real places and at complex places `v ≠ w` commute with the actions at `w`.
    These are the Library's commutation lemmas
    `complexPlaceCompactRepresentation_realPlaceLieAction`,
    `realPlaceLieAction_comm_complexPlace`,
    `complexPlaceCompactRepresentation_complexPlaceLieAction_of_ne` and
    `complexPlaceLieAction_comm_of_ne`. So each such component is `(component) ∘ Φ`, an
    equivariant map, applied to `f`.
  - The component at `w` is `Φ` of a right derivative of `f`.

  So every term is annihilated by `y`, and the sum lies in `ker (B y)`.
- `annihilator_complexLieAction`: extension to the complexified Lie algebra. A pure tensor is
  `z ⊗ X = z • complexify X`. Use `TensorProduct.inductionOn`.
- `annihilator_enveloping`: extension to the enveloping algebra. It is generated by the
  complexified Lie algebra (`Langlands.Algebra.LieCasimir.enveloping_adjoin_range`). Use
  `Algebra.adjoin_induction`.
- `annihilator_operator`: the whole concrete operator algebra preserves the annihilator. Use
  `Algebra.adjoin_induction` over its three generator families: finite, compact and enveloping.
- `annihilatorSubrepresentation S S' B hB w ds`: the annihilator as a `Subrepresentation` of
  `S.representation`.

### The induced pairing

- `inducedPairing B A Φ`: the bilinear form `(f, f') ↦ B (A f) (Φ f')` on the standard modules.
  `inducedPairing_apply` evaluates it (by `rfl`).
- `complexPlaceLieAction_one_tmul`: the Lie action at `w` of `1 ⊗ X` is the real Lie action of
  `complexPlaceLieInclusion F n w X`. Use the Library's `complexPlaceComplexLieInclusion_tmul`
  and `complexify_apply`.
- `isComplexStandardInvariantPairing_induced`: if `B` is invariant and `A`, `Φ` are
  place-equivariant, `inducedPairing B A Φ` satisfies `IsComplexStandardInvariantPairing`.
  - `K`-invariance: compact invariance of `B` at `complexPlaceCompactInclusion F n w k`.
  - Lie invariance: `complexPlaceLieAction_one_tmul` and Lie invariance of `B` at
    `complexPlaceLieInclusion F n w X`.

### Conclusion

- `mem_annihilator_of_eq_top`, `eq_zero_of_mem_annihilator`: if the annihilator
  subrepresentation is `⊤`, every vector lies in the annihilator. If it is `⊥`, its only
  vector is `0`.
- `annihilatorSubrepresentation_ne_top`: suppose `B.flip` is injective, the standard module of
  `ds` is nontrivial, and `Ad` is an injective place-equivariant map into `S'`. Then the
  annihilator is not `⊤`. Otherwise `B.flip (Ad f') = 0` for a nonzero `f'`, so `Ad f' = 0` and
  `f' = 0`.
- `exists_inducedPairing_ne_zero`: suppose the annihilator of `dd` is `⊥`, the standard module of
  `d` is nontrivial, and `A` is injective and place-equivariant. Then some
  `inducedPairing B A Φ` is a nonzero invariant pairing. For `f ≠ 0`, `A f ≠ 0` is not in the
  annihilator, which gives `Φ` and `f'` with `B (A f) (Φ f') ≠ 0`.
- `exists_complexStandardInvariantPairing`: the theorem stated above. It unpacks the
  contragredient pairing and the two parameters. Nontriviality of the standard modules is the
  Library's `complexStandardNontrivial`, which uses the length hypotheses. Then it applies
  `T.irreducible` to `annihilatorSubrepresentation T.realization Td.realization B hB w dd`.
- `complexPlaceContragredientParameterReduction`: the main theorem, as described above.

## Implementation notes

- The module declares local `AddCommGroup` instances on the Library's submodule types. It also
  declares `attribute [local instance 100] LieRing.ofAssociativeRing`, needed when working with
  the enveloping algebra.
- Equations inside `B (·) (·)` are transported with `congrArg` instead of `rw`, to keep
  elaboration within the default heartbeat limit.

## Provenance

All declarations are internal. The argument that an invariant pairing of global realizations
restricts to a nonzero invariant pairing of local components is standard. It is implemented
directly from the Library's definitions of operator realizations, contragredient pairings and
standard-module parameters.
