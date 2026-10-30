# Finite-set section avoidance from a basis of section generation opens

This module proves `Langlands.AlgebraicGeometry.Picard.FiniteSectionAvoidanceStatement` as the
theorem `Langlands.AlgebraicGeometry.Picard.finiteSectionAvoidance`, for an arbitrary universe
`u` and with no further hypotheses. Let `X` be a scheme and `L` a line bundle on `X`. Suppose
the generation opens `X_s = L.sectionOpen s` of global sections `s` of positive tensor powers
`L^{⊗ n}` (`n ≥ 1`) form a basis of the topology. In other words, for every open `W` and every
point `x ∈ W` there is such an `s` with `x ∈ X_s ⊆ W`. Then for every finite set `E` of points
contained in an open `W`, some global section `s` of some `L^{⊗ n}` with `n ≥ 1` satisfies
`E ⊆ X_s` and `X_s ⊆ W`.

The statement is motivated by Stacks Project Lemma 28.30.6 (tag 09NV), which proves it by
graded prime avoidance. The implemented proof uses a different route: an induction on the
number of points that, at each step, adds two sections raised to a common degree.

It uses these published results:

- `Langlands.SchemeModule.lineBundleResidueOpenComparison` (`SectionResidueComparison`): for a
  line bundle `M` and a global section `s` of `M`, the set of points where the residue-field
  value `residueSection M s x` is nonzero (`nonvanishingLocus M s`) equals the trivialization
  open `trivializationOpen M s`;
- `Langlands.AlgebraicGeometry.Picard.tensorPow_isLocallyFreeRankOne` (`TensorRankOneProof`):
  every tensor power `L^{⊗ n}` of a line bundle is a line bundle;
- `Langlands.AlgebraicGeometry.Picard.exists_trivializationOpen_eq_of_dvd`
  (`AlgebraicExtensionAmpleExistenceSpreadingProof`): if `0 < N` and `n ∣ N`, every global
  section of `L^{⊗ n}` has a global section of `L^{⊗ N}` with the same trivialization open;
- `Langlands.SchemeModule.sectionHom_app_one` (`TensorSections`): the morphism
  `sectionHom M s : O_X ⟶ M` sends `1` over `U` to the restriction of `s` to `U`;
- Mathlib's instance that pullback of module sheaves along a scheme morphism is an additive
  functor.

All helper results are in the namespace
`Langlands.AlgebraicGeometry.Picard.FiniteSectionAvoidance`.

## `sectionHom_add`

For a module sheaf `M` and global sections `s, t`,
`sectionHom M (s + t) = sectionHom M s + sectionHom M t`.

Proof as implemented. A morphism `φ : O_X ⟶ M` is linear over `Γ(X, U)` on each open `U`, so
`φ.app U a = a • φ.app U 1`. Both sides are compared on each open `U` and each `a ∈ Γ(X, U)`
(`Scheme.Modules.hom_ext`). After this rewriting, both sides depend only on the values at `1`.
By `sectionHom_app_one`, these values are restrictions of `s + t`, `s` and `t`, and
restriction is additive.

## `residueSection_add` and `residueHom`

For a module sheaf `M`, global sections `s, t` and a point `x`,
`residueSection M (s + t) x = residueSection M s x + residueSection M t x`.

Proof as implemented. By definition, the residue-field value is the value at `1` over the
whole open of the composite of `(pullbackUnitIso f).inv` with the pullback of `sectionHom M s`
along `f = X.fromSpecResidueField x`. By `sectionHom_add`, the additivity of the pullback
functor, and the distributivity of composition over addition, the composite for `s + t` is the
sum of the composites for `s` and `t`. Evaluation at `1` is additive.

`residueHom M x` packages `s ↦ residueSection M s x` as an additive group homomorphism from
`GlobalSections M` to the global sections of the residue-field fibre.

## `mem_sectionOpen_iff`

For a line bundle `L`, a section `s` of `L^{⊗ n}` and a point `x`, `x ∈ L.sectionOpen s` if and
only if `residueHom (L^{⊗ n}) x s ≠ 0`.

Proof as implemented. `L.sectionOpen s` is `trivializationOpen (L^{⊗ n}) s`. Apply
`lineBundleResidueOpenComparison` to the line bundle `L^{⊗ n}`, which is a line bundle by
`tensorPow_isLocallyFreeRankOne`. Membership in `nonvanishingLocus` is, by definition,
nonvanishing of the residue-field value.

## `exists_combined_section`

Let `n, m ≥ 1`, `t` a section of `L^{⊗ n}` and `v` a section of `L^{⊗ m}`. Then some section
`w` of some `L^{⊗ N}` with `N ≥ 1` satisfies:

- `X_w ⊆ X_t ∪ X_v`;
- every point in `X_t` but not in `X_v` is in `X_w`;
- every point in `X_v` but not in `X_t` is in `X_w`.

Proof as implemented. Let `N = n * m > 0`. By `exists_trivializationOpen_eq_of_dvd`, there are
sections `t'` and `v'` of `L^{⊗ N}` with `X_{t'} = X_t` and `X_{v'} = X_v`. Let `w = t' + v'`.
By `mem_sectionOpen_iff`, a point is in each of these opens exactly when the residue-field
value of the corresponding section is nonzero, and the value of `w` is the sum of the values of
`t'` and `v'`. If the value of `w` at `x` is nonzero, then one of the two summands is nonzero.
If exactly one of the values of `t'` and `v'` is nonzero, then their sum equals that value and
is nonzero.

## Main theorem `finiteSectionAvoidance`

Proof as implemented. Fix `X`, `L` and the basis hypothesis. Prove, by induction on `k`, that
the conclusion holds for every finite `E` with `E.ncard = k` and every open `W ⊇ E`.

- **`k = 0`.** Then `E` is empty. Take the zero section of `L^{⊗ 1}`. Its residue-field values
  are all zero, so by `mem_sectionOpen_iff` its generation open is empty. That open is
  contained in `W`, and it contains `E = ∅`.
- **`k + 1`.** `E` is nonempty and finite. Choose `a ∈ E` maximal in `E` for the
  specialization preorder (`Set.Finite.exists_maximalFor` with `Specialization.toEquiv`).
  Under Mathlib's order on `Specialization X`, this means: if `y ∈ E` and `y ⤳ a`, then
  `a ⤳ y`. The set `E \ {a}` has `k` points. By the induction hypothesis it has a section `t`
  of some `L^{⊗ n}` with `n ≥ 1`, `E \ {a} ⊆ X_t` and `X_t ⊆ W`.
  - If `a ∈ X_t`, then `t` works for `E`.
  - Otherwise, let `C` be the union of the closures of the points of `E \ {a}`. It is closed,
    as a finite union of closed sets. Let `W' = W ∩ (X \ C)`. Then `a ∈ W'`. Otherwise
    `a ∈ closure {y}` for some `y ∈ E \ {a}`, that is, `y ⤳ a`. By maximality `a ⤳ y`, and
    `y ∈ X_t` with `X_t` open would then put `a` in `X_t`, a contradiction. The basis
    hypothesis gives a section `v` of some `L^{⊗ m}` with `m ≥ 1`, `a ∈ X_v` and
    `X_v ⊆ W'`. Apply `exists_combined_section` to `t` and `v` to get `w`.
    - The point `a` is in `X_v` and not in `X_t`, so `a ∈ X_w`.
    - Each `y ∈ E \ {a}` is in `X_t`. It is not in `X_v`, because `y ∈ C` and `X_v ⊆ W'`
      avoids `C`. So `y ∈ X_w`.
    - Finally, `X_w ⊆ X_t ∪ X_v ⊆ W ∪ W' = W`.

The theorem follows by applying this claim with `k = E.ncard`.
