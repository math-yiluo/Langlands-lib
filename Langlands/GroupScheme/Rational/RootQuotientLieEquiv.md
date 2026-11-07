# The Lie algebra of the quotient of a multipliable root group

Let `G` be a smooth affine group over a field `k`, `S` a split torus with `i : S ⟶ G`, and `a`
a nonzero character of `S` such that no `n • a` with `n ≥ 3` is a relative root. Let
`U = U_a` and `U₂ = U_{2a}` be represented root groups and `V = U / U₂` the quotient of the
published `DoubleRootCommutatorPairing`. This module proves three things.

1. The differential of the quotient map `q : U ⟶ V`, read on the weight space `g_a` of `a` in
   the Lie algebra of `G`, is a `k`-linear isomorphism `g_a ≅ Lie(V)`.
2. Composing with the point-to-Lie comparison of the vector group `V` identifies the rational
   points `V(k)` with `g_a`.
3. Both identifications commute with every action that fixes the split torus: the action on
   `G` on one side, the induced action on `V` on the other.

The intended use is the multipliable-root case of quasi-split coordinates. A Galois descent of
`g_a` to a field (published `rootOrbitFieldWeightSpaceEquiv`, Worker 1620) then gives field
coordinates on `V(k)` together with the action of the centralizer of `S`.

Provenance: the module is internal. The surjectivity argument lifts a tangent vector of `V`
through the section of the published `nonempty_heisenbergNormalForm` (module
`RootHeisenbergNormalForm`). The computation of the tangent space of the root functor
(`tangentSubmodule_subgroup`, `semigroupWeightSpan_cyclicTail`) and the weight decomposition
(`isInternal_weightSpace_of_isSplitTorus`) are published. The equivariance proofs follow the
published `rootPointLieEquiv_act` (module `RootPointLieAutomorphisms`): they evaluate the action
at a rational point to an automorphism with `basePointIso`.

All declarations live in namespace `Langlands.GroupScheme.RelativeRoot`.

## Weight spaces and the tangent space of a root group

In this section `G` is affine over `Spec k` and `S` is split. Here `weightSpace i χ` is the
weight space of `χ` in the Lie algebra `Additive (lieKernel G k)`, and `tangentSubmodule P` is
the tangent space at the identity of a subgroup functor `P`.

- `disjoint_weightSpace_two_nsmul`: for `a ≠ 0` and `G` locally of finite type, the weight
  spaces of `a` and `2 • a` are disjoint. The weight decomposition is a direct sum and
  `a ≠ 2 • a`.
- Assume from here on that `G` is smooth. `weightSpace_nsmul_le_tangentSubmodule`: for `a ≠ 0`
  and `n ≥ 1`, the weight space of `n • a` lies in the tangent space of the root functor
  `subgroup i a`. `weightSpace_le_tangentSubmodule` is the case `n = 1`.
- `tangentSubmodule_le_weightSpace_sup_of_noHigherRoots` and
  `tangentSubmodule_eq_weightSpace_sup_of_noHigherRoots`: if `a ≠ 0` and no `n • a` with
  `n ≥ 3` is a relative root, then the tangent space of `subgroup i a` equals
  `weightSpace i a ⊔ weightSpace i (2 • a)`.

## The differential of the quotient map (namespace `DoubleRootCommutatorPairing`)

Let `C : DoubleRootCommutatorPairing i a hj hj₂`, with represented root groups
`j : U ⟶ G` of `a` and `j₂ : U₂ ⟶ G` of `2 • a`, and quotient map `C.q : U ⟶ C.V`. `U` is
affine over `Spec k`.

- `isAffineHom_V`: `C.V` is affine over `Spec k`, because it is a vector group. From here on
  this is an instance argument.
- `targetMapLinear_q_eq_zero_iff`: a tangent vector `Y` of `U` has `dq Y = 0` exactly when
  `dj Y` is tangent to `subgroup i (2 • a)`. The kernel of `q` is the preimage of that
  subgroup functor.

Below, `hS : IsSplitTorus S`, `ha : a ≠ 0` and `hhigh : ∀ n ≥ 3, n • a ∉ relativeRoots i`.

- `rootQuotientLieMap C hS ha : weightSpace i a →ₗ[k] Lie(C.V)`. It sends `X` to `dq Y`,
  where `Y` is the unique tangent vector of `U` with `dj Y = X` (published
  `representedTangentLinearEquiv`).
- `rootQuotientLieMap_eq_of_sub_mem`: `rootQuotientLieMap X = dq Y` for every tangent vector
  `Y` of `U` with `dj Y - X` tangent to `subgroup i (2 • a)`.
- `rootQuotientLieMap_injective`. If `dq Y = 0` then `X = dj Y` is tangent to
  `subgroup i (2 • a)`. That tangent space is the weight space of `2 • a`, by the published
  `tangentSubmodule_eq_weightSpace_of_noHigherRoots`, and `2 • a` has no higher multiples
  that are roots. So `X` lies in two disjoint weight spaces and vanishes.
- `rootQuotientLieMap_surjective`. Let `Z` be a tangent vector of `C.V`. Choose a Heisenberg
  normal form (published `nonempty_heisenbergNormalForm`, which needs `hhigh`). Its section
  `sec : C.V ⟶ U` is normalized at the identity (`one_sec`), so `Y = Z ≫ sec` is a tangent
  vector of `U` with `dq Y = Z` (`sec_comp`). Write `dj Y = X₁ + X₂` with `X₁` of weight `a`
  and `X₂` of weight `2 • a`. Then `rootQuotientLieMap X₁ = dq Y = Z`.
- `rootQuotientLieEquiv C hS ha hhigh : weightSpace i a ≃ₗ[k] Lie(C.V)`: the bijective map
  above, as a linear equivalence. It involves no choice.
- `rootQuotientLieEquiv_apply`: it agrees with `rootQuotientLieMap`.
- `rootQuotientLieEquiv_symm_apply`: the inverse sends `dq Y` to `X` whenever `dj Y - X` lies
  in the weight space of `2 • a`.

## Naturality

- `targetMapLinear_mem_weightSpace_of_fixes`: if a group endomorphism `σ : G ⟶ G` satisfies
  `i ≫ σ = i`, its differential preserves the weight space of every character. This uses the
  published `lieKernelHomLinear_mem_weightSpace`.
- `rootQuotientLieMap_naturality` and `rootQuotientLieEquiv_naturality`. Let `σ : G ⟶ G`
  fix `i`, and let `ρ : U ⟶ U` and `τ : C.V ⟶ C.V` be group endomorphisms with
  `ρ ≫ j = j ≫ σ` and `ρ ≫ C.q = C.q ≫ τ`. Then `rootQuotientLieEquiv (dσ X) =
  dτ (rootQuotientLieEquiv X)` for every `X` in `weightSpace i a`.

## Equivariance for an action fixing the torus (section `Action`)

Let `D` be a group scheme over `Spec k` and `b : AutomorphicAction D G` an action with
`hfix : b.act z (t ≫ i) = t ≫ i` for all points `z` of `D` and `t` of `S`. The published
`rootActionOfFixesTorus` and `torusQuotientAction C b hfix` are the induced actions of `D` on
`U` and on `C.V`. For a rational point `h` of `D`, `rationalCoeffEquiv k D h` is the
corresponding point with coefficients in `k`, and `b.differential` is the differential of the
action (published).

- `constantPoint_eq_rationalCoeffEquiv`: the constant point of `h` at the base coefficient
  algebra is `rationalCoeffEquiv k D h`.
- `differential_mem_weightSpace_of_fixes`: `b.differential (rationalCoeffEquiv k D h)` preserves
  the weight space of every character.
- `rootActionBasePointIso_comp` and `rootActionBasePointIso_comp_q`: evaluated at `h`, the
  actions on `U`, `G` and `C.V` satisfy `ρ ≫ j = j ≫ σ` and `ρ ≫ C.q = C.q ≫ τ`.
- `rootQuotientLieEquiv_act`: for every rational point `h` of `D` and `X` in
  `weightSpace i a`,
  `rootQuotientLieEquiv (b.differential h X) =
  (torusQuotientAction C b hfix).differential h (rootQuotientLieEquiv X)`, where `h` is used
  through `rationalCoeffEquiv k D h`.

## Rational points of the quotient

- `rootQuotientPointLieEquiv C hS ha hhigh : Additive (rationalPoints C.V) ≃+ weightSpace i a`.
  It is the composite of `rationalCoeffEquiv`, the published point-to-Lie comparison
  `vectorPointLieEquiv` for one chosen system of weight vector coordinates of weight `a` on
  `C.V` (from the field `C.weightVectorStructure`), and the inverse of
  `rootQuotientLieEquiv`. The point-to-Lie comparison does not depend on the choice of weight
  coordinates of the same weight (published `vectorPointLieEquiv_eq_of_weight`).

In section `PointAction`, `D` is also affine over `Spec k`.

- `rationalCoeffEquiv_torusQuotientAction`: `rationalCoeffEquiv` turns the action of a
  rational point `h` on `V(k)` into the action of `rationalCoeffEquiv k D h`.
- `rootQuotientLieEquiv_symm_act`: the inverse of `rootQuotientLieEquiv` intertwines the two
  differentials.
- `rootQuotientPointLieEquiv_act`: for every rational point `h` of `D` and `v` in `V(k)`, the
  image of `(torusQuotientAction C b hfix).act h v` in the Lie algebra of `G` is
  `b.differential (rationalCoeffEquiv k D h)` applied to the image of `v`. The proof uses the
  linearity of the action of `D` in weight coordinates (published
  `isLinearVectorCoordinates_torusQuotientAction`) and the published `vectorPointLieEquiv_act`.

## Scope

The module identifies `V(k)` with `g_a` and transports actions fixing `S`. It does not
identify `g_a` with a field and does not construct the field data of
`HeisenbergUnitaryData`. It does not prove that the centralizer of `S` is a torus.
