# The Heisenberg normal form of a multipliable relative root group

This module puts a multipliable relative root group into normal form. Let `a` be a relative
root with no relative root `n • a` for `n ≥ 3`, let `U = U_a` and `U₂ = U_{2a}` be the root
groups, and let `V = U / U₂`. There is a torus-equivariant section `sec : V ⟶ U` as a
morphism of schemes, with `sec(1) = 1`. The group law of `U` in this section reads

`sec(x) sec(y) = β(x, y) · sec(x y)`

for a morphism `β : V × V ⟶ U₂`, the cocycle. Every point of `U` is `w · sec(x)` with `w` a
point of `U₂` and `x` its image in `V`. The cocycle is trivial when either argument is the
identity, intertwines the torus actions of weights `a` and `2 • a`, and is bilinear in weight
vector coordinates. The commutator pairing of
`GroupScheme/Rational/RootDoubleCommutatorPairing` is `β(x, y) β(y, x)⁻¹`. The law has the
same shape as the quadratic unitary law `(u, v)(u', v') = (u + u', v + v' + u ū')` of
Kaletha–Prasad (2.7.2).

Provenance: the module is internal; the literature reference is context only. It combines the
published or staged modules `RootDoubleCommutatorPairing`, `VectorPairingWeightLinearity`,
`SplitTorusEquivariantSection` and `RootDoubleCommutatorBilinear`, the published
`IsVectorGroupOfDimension.exists_quotientSection` (affine split-unipotent torsor
triviality), and `weightVectorCoordinatesOfNoHigherRoots`.

All declarations live in namespace `Langlands.GroupScheme.RelativeRoot`.

## Additivity from scalar linearity

These statements concern a pairing `P : V.X ⊗ V.X ⟶ W.X` of vector groups over a field `k`
with natural coordinates `e` and `e'`. `coordinatePairing e e' P` is the pairing in
coordinates over coefficient algebras, from `VectorPairingWeightLinearity`.

- `trunc_T_one_mul_invert_toLaurent q`: `trunc (t q(t⁻¹)) = q₀ X + q₁` in Laurent polynomials
  over any commutative ring. `eq_of_toLaurent_eq_T_one_mul_invert`: if `p(t) = t q(t⁻¹)`,
  then `p = q₀ X + q₁`.
- `aevalTower_id_zero p`: substituting `X ↦ 0` gives the constant coefficient.
- `coordinatePairing_add_left he he' hsmul x x' y`. Assume natural coordinates and scalar
  linearity in the first argument over every coefficient algebra (`hsmul`). Then
  `coordinatePairing (x + x') y = coordinatePairing x y + coordinatePairing x' y`.
  `coordinatePairing_add_right` is the analogue in the second argument.
- `isBilinearVectorPairing_of_smul he he' hsmul_left hsmul_right`: scalar linearity in each
  argument over every coefficient algebra gives `IsBilinearVectorPairing e e' P`, that is,
  additivity and `Γ(T, 𝒪_T)`-linearity in each argument on every test scheme.

**Proof of additivity.** Over `A[X]` put `G = P(X x + x', y)` and `K = P(x + X x', y)`.
Substitute `X ↦ t` in `G` and `X ↦ t⁻¹` in `K` (into `A[t, t⁻¹]`). Scalar linearity at the
scalar `t` gives `G(t) = t K(t⁻¹)` coordinatewise, because `t(x + t⁻¹ x') = t x + x'`. The
Laurent lemma then gives `G = K₀ X + K₁`. Substituting `X ↦ 0` identifies `K₀` with
`P(x, y)` and `K₁` with `P(x', y)`. Substituting `X ↦ 1` gives `P(x + x', y) = P(x, y) +
P(x', y)`. Bilinearity on scheme tests follows from `coordinatePairing_global`.

## The normal form

The setting is a field `k`, a group scheme `G` over `Spec k`, a commutative group scheme `S`
with `i : S ⟶ G`, a character `a`, representatives `j : U ⟶ G` of `subgroup i a` (`hj`) and
`j₂ : U₂ ⟶ G` of `subgroup i (2 • a)` (`hj₂`), and `C : DoubleRootCommutatorPairing i a hj
hj₂`. `C` provides `V = C.V`, the quotient map `C.q`, the torus action `C.action` and the
commutator pairing `C.pairing`.

`HeisenbergNormalForm C` (structure) has the fields:

- `inclusion : U₂ ⟶ U` with `inclusion_comp : inclusion ≫ j = j₂`, and
  `range_inclusion`: the range of `inclusion` is the range of the actual kernel of `C.q`;
- `sec : C.V.X ⟶ U.X`, a morphism of schemes, with `sec_comp : sec ≫ C.q = 𝟙`,
  `one_sec : 1 ≫ sec = 1` on every test scheme, and `act_sec`: for every torus point `s`,
  `(subgroupAction i a j hj).act s (x ≫ sec) = C.action.act s x ≫ sec`;
- `cocycle : C.V.X ⊗ C.V.X ⟶ U₂.X` with `sec_mul`:
  `(x ≫ sec) * (y ≫ sec) = ((lift x y ≫ cocycle) ≫ inclusion) * ((x * y) ≫ sec)` for all
  test points `x, y` of `V`.

Statements in namespace `HeisenbergNormalForm`, for `N : HeisenbergNormalForm C`:

- `inclusion_comp_hom`, `mono_inclusion` (the inclusion is a monomorphism of schemes, since
  `j₂` is), and `act_inclusion` (the inclusion intertwines the conjugation actions
  `subgroupAction i (2 • a) j₂ hj₂` and `subgroupAction i a j hj`).
- `cocycle_comp`: `cocycle(x, y) = sec(x) sec(y) sec(x y)⁻¹`, read through the inclusion.
- `cocycle_one_left`, `cocycle_one_right`: `cocycle(1, y) = 1` and `cocycle(x, 1) = 1`.
- `cocycle_act`: `cocycle(s · x, s · y) = s · cocycle(x, y)`, with `S` acting on `U₂` by
  conjugation.
- `pairing_eq`: `lift x y ≫ C.pairing = cocycle(x, y) * cocycle(y, x)⁻¹`.
- `exists_eq_mul_sec`: every `T`-point `g` of `U` is `(w ≫ inclusion) * ((g ≫ C.q) ≫ sec)`
  for some `T`-point `w` of `U₂`.
- `isBilinearVectorPairing_cocycle hS ha he he'`. Assume `IsSplitTorus S.toGrp`, `a ≠ 0`,
  weight vector coordinates `e` on `C.V` of weight `a` for `C.action`, and weight vector
  coordinates `e'` on `U₂` of weight `2 • a` for the conjugation action. Then
  `IsBilinearVectorPairing e e' N.cocycle`.

Existence:

- `nonempty_heisenbergNormalForm C hS ha hhigh`, under `[IsAffineHom G.X.hom]`,
  `[Smooth G.X.hom]` and `[IsAffineHom U.X.hom]`, with `hS : IsSplitTorus S.toGrp`,
  `ha : a ≠ 0` and `hhigh : ∀ n ≥ 3, n • a ∉ relativeRoots i`. It proves
  `Nonempty (HeisenbergNormalForm C)`; `heisenbergNormalForm` is a chosen instance.

## Proofs

**Bilinearity of the cocycle.** `coordinatePairing_smul` of `VectorPairingWeightLinearity`
gives scalar linearity in each argument from `cocycle_act` and the normalization lemmas.
`isBilinearVectorPairing_of_smul` then applies.

**Commutator.** Put `g = sec(x)` and `h = sec(y)`; their images in `V` are `x` and `y`. Points
of `V` commute, because `V` has vector coordinates. So `g h = β(x, y) sec(x y)` and
`h g = β(y, x) sec(x y)`, and `g h g⁻¹ h⁻¹ = (g h)(h g)⁻¹ = β(x, y) β(y, x)⁻¹`. The field
`C.lift_pairing` identifies the commutator pairing with this commutator in `G`.

**Existence.**

1. The doubled root subgroup lies in the root subgroup (published
   `double_subgroup_le_of_cyclicComparison`). Factoring `j₂` through `j`
   (`IsRepresentedBy.factor`) gives the inclusion. Its range is the preimage of the doubled
   root subgroup, which is the kernel of `C.q` by `C.isFppfQuotient`.
2. Weight vector coordinates of weight `a` on `V` come from `C.weightVectorStructure`. Those
   of weight `2 • a` on `U₂` come from `weightVectorCoordinatesOfNoHigherRoots`, since
   `2 • a ≠ 0` and `2 • a` has no higher roots (`hasNoHigherRoots_two_nsmul`). Hence `V` and
   `U₂` are affine vector groups.
3. `IsVectorGroupOfDimension.exists_quotientSection` gives a section `s₀` of `C.q` as a
   morphism of schemes, using that `C.q` is flat and surjective and that `U` and `V` are
   affine.
4. `IsSplitTorus.exists_equivariantSection` makes `s₀` equivariant. Here `C.act_comp`
   provides the compatibility of `C.q`, the factorization through `j` provides that of the
   inclusion, and the weight coordinates on `U₂` are linear.
5. Put `sec(x) = σ(x) σ(1)⁻¹`. It is still an equivariant section, because `σ(1)` is fixed by
   the torus, and `sec(1) = 1`.
6. On the universal pair, `sec(x) sec(y) sec(x y)⁻¹` maps to `1` in `V`, so it is the image of
   a unique point of `U₂`; this defines `cocycle`.

## Scope

This module gives the normal form and bilinearity only. It does not identify `V(k)` or
`U₂(k)` with a field, does not compare the cocycle with a hermitian or trace form, and does not
construct `RootUnitaryCoordinates`.
