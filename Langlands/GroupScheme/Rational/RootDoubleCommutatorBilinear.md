# Bilinearity of the commutator pairing of a multipliable relative root

This module combines two modules: `GroupScheme/Rational/RootDoubleCommutatorPairing`, which
gives the commutator pairing `V × V ⟶ U₂` of a relative root subgroup `U = U_a` modulo its
doubled root subgroup `U₂ = U_{2a}`, with `V = U / U₂`, and
`GroupScheme/Rational/VectorPairingWeightLinearity`, which shows that equivariant pairings
of weight vector groups are bilinear. The result is that the commutator pairing is bilinear
over every test scheme's ring of global functions, in weight vector coordinates. The
argument is internal; the module adds no literature input.

## Setting

All declarations live in namespace `Langlands.GroupScheme.RelativeRoot`. The setting is a
field `k`, a group scheme `G` over `Spec k`, a commutative group scheme `S` with a
homomorphism `i : S ⟶ G`, and a character `a` of `S`. Represented root subgroups are given:
`j : U ⟶ G` represents `subgroup i a` (`hj`), and `j₂ : U₂ ⟶ G` represents
`subgroup i (2 • a)` (`hj₂`). `C : DoubleRootCommutatorPairing i a hj hj₂` provides the
quotient `C.V`, the torus action `C.action` on it and the pairing `C.pairing`.

## Statements

- `DoubleRootCommutatorPairing.isBilinearVectorPairing C hS ha he he'`. Assume
  `IsSplitTorus S.toGrp`, `a ≠ 0`, weight vector coordinates `e` on `C.V` of weight `a` for
  `C.action` (`IsWeightVectorCoordinates C.action a e`), and weight vector coordinates `e'`
  on `U₂` of weight `2 • a` for the conjugation action `subgroupAction i (2 • a) j₂ hj₂`.
  Then `IsBilinearVectorPairing e e' C.pairing`. On every test scheme `T`, the pairing is
  additive in each argument and linear over `Γ(T, 𝒪_T)` in each argument, in these
  coordinates.
- `hasNoHigherRoots_two_nsmul hhigh`, assuming `[IsAffineHom G.X.hom]`. If no `n • a` with
  `n ≥ 3` is a relative root of `i`, then `HasNoHigherRoots i (2 • a)`: no `n • (2 • a)` with
  `n ≥ 2` is a relative root.
- `DoubleRootCommutatorPairing.exists_bilinear_coordinates C hS ha hhigh`, assuming
  `[IsAffineHom G.X.hom] [Smooth G.X.hom]`. Assume `IsSplitTorus S.toGrp`, `a ≠ 0`, and no
  relative root `n • a` with `n ≥ 3`. Then there are weight vector coordinates `e` on `C.V`
  of weight `a` and `e'` on `U₂` of weight `2 • a` with `IsBilinearVectorPairing e e' C.pairing`.

## Proofs

- Bilinearity is `isBilinearVectorPairing_of_equivariant` applied to the fields of `C`:
  `lift_mul_pairing` and `lift_pairing_mul` give multiplicativity in each argument, and
  `lift_pairing_act` gives equivariance from weight `a` to weight `2 • a`.
- No higher roots: `n • (2 • a) = (n * 2) • a`, and `n * 2 ≥ 4 ≥ 3` when `n ≥ 2`.
- Existence: the coordinates `e` come from the field `C.weightVectorStructure`. The
  coordinates `e'` come from the published `weightVectorCoordinatesOfNoHigherRoots`
  (module `GroupScheme/Rational/RootSubgroupWeightCoordinates`), applied to `2 • a`. It
  needs `2 • a ≠ 0` (`IsSplitTorus.nsmul_ne_zero`) and the preceding no-higher-roots
  statement.

## Scope

This module proves bilinearity in coordinates only. It does not identify the pairing with a
hermitian or trace form, does not produce a quadratic field extension, and does not
construct `RootUnitaryCoordinates`.
