# Heisenberg field data with trace compatibility from separating character values

The published structure `HeisenbergUnitaryData C N s` (module `RootUnitaryHeisenbergAssembly`)
collects the field data from which quadratic unitary coordinates of a multipliable root are
built. Two of its fields concern the cocycle `form` of the Heisenberg normal form `N` written
in the field coordinates:

- `form_add`: additivity in the second argument;
- `form_trace`: `form (f x) y + form x (f y) = (f + f̄) form x y` for every `f` in the
  quadratic extension, where `f̄` is its conjugate.

This module replaces both fields by hypotheses at the level of rational points. Additivity
holds automatically, in both arguments. `k`-homogeneity holds when the coordinates are
`k`-linear through the identifications of `V(k)` and `U_{2a}(k)` with weight spaces of the Lie
algebra. For trace compatibility it suffices that

- the cocycle in coordinates is `k`-linear in each argument, and
- there is a field `L` over `k` with as many `k`-embeddings of the extension `E` as its
  degree, such that the products of two embeddings separate the pairs `{π, π ∘ σ}` on the
  values of the character on `Z(k)`. Here `σ` is the conjugation of `E` over the base field.

The scaling fields `first_act` and `second_act`, together with the equivariance of the
cocycle (published `EquivariantHeisenbergNormalForm.cocycle_act_torus`), make the cocycle norm
equivariant at each character value. The algebraic theorem
`Langlands.Algebra.NormEquivariantBilinear.add_eq_trace_mul` (module
`Algebra/NormEquivariantBilinear`) then gives trace compatibility. No scheme-level property of
the character is used.

Provenance: internal. It combines the published `HeisenbergUnitaryData`,
`EquivariantHeisenbergNormalForm.cocycle_act_torus` and
`HeisenbergNormalForm.isBilinearVectorPairing_cocycle`, the module
`RootUnitaryHeisenbergAdditivity` (`HeisenbergNormalForm.form_add_of_cocycle_eq`), the module
`Algebra/NormEquivariantBilinear` (`add_eq_trace_mul`), and for homogeneity the helper module
`GroupScheme/Rational/RootHeisenbergCocycleLie`.

All declarations live in namespace `Langlands.Geometry.Building`.

## Setting

As in `RootUnitaryHeisenbergAssembly`: `k` is a field, `S` a commutative group scheme over
`Spec k` with `i : S.toGrp ⟶ G`, `jZ : Z ⟶ G` a group scheme over `Spec k` mapping to `G`, and
`a` a character of `S`. `C : DoubleRootCommutatorPairing i a hj hj₂` is the quotient datum
with quotient `C.V = U_a / U_{2a}`. `N` is an equivariant Heisenberg normal form for the
conjugation action of `Z`, with `hfix` the hypothesis that this action fixes `S`. Finally
`s : S.toGrp ⟶ Z`.

## Additivity in the first argument (section `Additivity`)

Here `G` is affine and smooth over `Spec k`.

- `HeisenbergNormalForm.cocycle_lift_mul_left M hS ha hhigh`: for every test scheme `T` and
  points `x, x', y` of `C.V` over `T`,
  `M.cocycle (x x', y) = M.cocycle (x, y) · M.cocycle (x', y)`. It is the first component of
  the published bilinearity in weight coordinates, as for `cocycle_lift_mul_right` in
  `RootUnitaryHeisenbergAdditivity`.
- `HeisenbergNormalForm.form_add_left_of_cocycle_eq`: for group isomorphisms
  `first : Multiplicative E ≃* V(k)` and `second : Multiplicative H ≃* U_{2a}(k)` and a function
  `form` related to the cocycle as in the field `cocycle_eq`,
  `form (x + x') y = form x y + form x' y`.

## Homogeneity in coordinates (section `Homogeneity`)

Here `G` is affine and smooth over `Spec k`, the root groups `U`, `U₂` and the quotient `C.V`
are affine, and `hS`, `ha`, `hhigh` are as above. Let `E` be a `k`-module and `H` an additive
subgroup of `E` with `c • w ∈ H` for all `c : k` and `w ∈ H` (`hH`). Let
`first : Multiplicative E ≃* V(k)`, `second : Multiplicative H ≃* U_{2a}(k)` and `form` satisfy
`cocycle_eq`.

- `HeisenbergNormalForm.form_smul_left_of_lie M hS ha hhigh first second form cocycle_eq hH
  hfirst hsecond`. The hypothesis `hfirst` states that the image of `first (c • x)` in the Lie
  algebra of `G` under `rootQuotientPointLieEquiv` is `c` times that of `first x`. The
  hypothesis `hsecond` states the same for `second` and `doubleRootPointLieEquiv`, for
  `w' = c • w`. Then `form (c • x) y = c • form x y`. Proof: by
  `doubleRootPointLieEquiv_cocycle_smul_left`, the value of the cocycle at
  `(first (c • x), first y)` and `second (c • w)` have the same image in the weight space of
  `2 • a`, where `w` is the coordinate of the value at `(first x, first y)`. That
  identification is injective.
- `HeisenbergNormalForm.form_smul_right_of_lie`: the same for the second argument,
  `form x (c • y) = c • form x y`.

## The structure `HeisenbergUnitarySeparationData C N s`

It has the fields of `HeisenbergUnitaryData C N s` except `form_add` and `form_trace`:
`base`, `extension` with their instance fields, `first`, `second`, `form`, `cocycle_eq`,
`form_nonsymm`, `character`, `restriction`, `first_act` and `second_act`, with the same
statements. Write `E` for `extension`, `χ(z)` for the character value
`rationalCharacterEval character (rationalExtend k extension Z z)` at `z ∈ Z(k)` (the
expression used in `first_act`), and `σ` for the conjugation `SU3Root.conjugation base
extension`, viewed as a `k`-algebra map `E →ₐ[k] E`. The structure has the further fields:

- `form_smul_left : ∀ (c : k) x y, form (c • x) y = c • form x y`;
- `form_smul_right : ∀ (c : k) x y, form x (c • y) = c • form x y`;
- `splitting : Type u`, with instance fields `Field splitting` and `Algebra k splitting`;
- `card_embeddings : Nat.card (E →ₐ[k] splitting) = Module.finrank k E`;
- `separation`: for all `k`-algebra maps `π τ ρ : E →ₐ[k] splitting`, if
  `τ(c) ρ(c) = π(c) π(σ c)` for every `c` in the range of `z ↦ χ(z)`, then either `τ = π` and
  `ρ = π ∘ σ`, or `τ = π ∘ σ` and `ρ = π`.

The last two fields are the hypotheses `hcard` and `hsep` of `add_eq_trace_mul`, for the set of
character values.

## Results (namespace `HeisenbergUnitarySeparationData`)

Let `R : HeisenbergUnitarySeparationData C N s`.

- `value R z`: the character value `χ(z)`.
- `norm_mul_mem_traceZero`: `χ(z) σ(χ(z)) w` is trace zero whenever `w` is.
- `form_norm`: `form (χ(z) x) (χ(z) y) = χ(z) σ(χ(z)) form x y` for every `z ∈ Z(k)`. Proof:
  by `first_act`, the coordinates `χ(z) x` and `χ(z) y` are the images of `x` and `y` under
  the action of `z`. The cocycle is equivariant (`cocycle_act_torus`), and the action of `z`
  on `U_{2a}(k)` multiplies the trace-zero coordinate by `χ(z) σ(χ(z))` (`second_act`).

Assume now that `G` is affine and smooth over `Spec k`, `hS : IsSplitTorus S`, `ha : a ≠ 0` and
`hhigh : ∀ n ≥ 3, n • a ∉ relativeRoots i`.

- `form_add_left` and `form_add_right`: `form` is additive in each argument.
- `bilinear R hS ha hhigh`: `form` as a `k`-bilinear map.
- `form_trace`: `form (f x) y + form x (f y) = (f + σ f) form x y` for all `f, x, y`. This is
  `add_eq_trace_mul` applied to `card_embeddings`, `σ`, the set of character values,
  `bilinear`, `form_norm` and `separation`. The finiteness instance on `E →ₐ[k] splitting` is
  Mathlib's, from finite dimensionality of `E`.
- `toHeisenbergUnitaryData R hS ha hhigh : HeisenbergUnitaryData C N s`: the same data, with
  `form_add := form_add_right` and `form_trace := form_trace`.

## Scope

This is a reduction. It does not construct the field coordinates, the character or the field
`splitting`. It does not prove that given coordinates are `k`-linear through the Lie-algebra
identifications, that the character values satisfy `separation`, or that the cocycle is not
symmetric. It does not prove that the centralizer of `S` is a torus.
