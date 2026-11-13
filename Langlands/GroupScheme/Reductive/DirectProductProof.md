# Direct products of pseudo-reductive, reductive and semisimple groups: proof

The theorem `Langlands.GroupScheme.directProductReductive` proves
`Langlands.GroupScheme.DirectProductReductiveStatement.{u}`
(module `Langlands.GroupScheme.Reductive.DirectProductStatement`). Its type is exactly
that proposition at the published universe parameter `u`. It adds no hypotheses, and
its Lean proof uses only the axioms `propext`, `Classical.choice` and `Quot.sound`.

The statement says: for every field `k : Type u` and all
`G H : GroupScheme (Spec (CommRingCat.of k))`, the direct product `G ⊗ H` is
pseudo-reductive, connected reductive, or semisimple whenever both `G` and `H` are.

Auxiliary declarations are in the namespace `Langlands.GroupScheme.DirectProduct`.
The module sets no options.

## Proof

### Step 0: `G ⊗ H` as a two-factor finite product (`pairFamily`, `tensorIsoPi`)

For group schemes `G H` over any base scheme `S`, `pairFamily G H` is the family on
`PUnit ⊕ PUnit` (in `Type u`) with value `G` on the left summand and `H` on the right.
It is defined as `sumGroupFamily (fun _ => G) (fun _ => H)`.

`tensorIsoPi G H : G ⊗ H ≅ pi (pairFamily G H)` is the group-scheme isomorphism built
from three pieces. First, Mathlib's `productUniqueIso` identifies a one-factor product
`∏ᶜ (fun _ : PUnit => G)` with `G`, and likewise for `H`. Second, the monoidal tensor
of the inverses of these two isomorphisms gives `G ⊗ H ≅ pi (fun _ => G) ⊗ pi (fun _ => H)`.
Third, `finiteProductSumIso` gives
`pi A ⊗ pi B ≅ pi (sumGroupFamily A B)`.

### Step 1: trivial ground-field unipotent radicals (`hasTrivialUnipotentRadical_tensor`)

Suppose `G` and `H` are affine and locally of finite type over `k`, and both have
trivial ground-field unipotent radical (`HasTrivialUnipotentRadical`). Then so does
`G ⊗ H`. Each member of `pairFamily G H` is `G` or `H` (case split on the summand), so
it is affine and locally of finite type with trivial radical. `HasTrivialUnipotentRadical.pi`
then gives a trivial radical for `pi (pairFamily G H)`.
`HasTrivialUnipotentRadical.of_iso` transfers this along `tensorIsoPi G H` to `G ⊗ H`.

### Step 2: Part 1, pseudo-reductivity (`isPseudoReductive_tensor`)

If `G` and `H` are pseudo-reductive, every member of `pairFamily G H` is
pseudo-reductive (case split). `isPseudoReductive_pi` then makes
`pi (pairFamily G H)` pseudo-reductive, and `IsPseudoReductive.of_iso` along
`tensorIsoPi G H` makes `G ⊗ H` pseudo-reductive. This also gives smoothness,
affineness and connectedness of `G ⊗ H`.

### Step 3: Part 2, connected reductivity (`isConnectedReductive_tensor`)

Let `G` and `H` be connected reductive. By `IsConnectedReductive.isPseudoReductive`
both are pseudo-reductive. Step 2 then makes `G ⊗ H` pseudo-reductive. This supplies
the first three fields of `IsConnectedReductive (G ⊗ H)`: `Smooth`, `IsAffineHom` and
`ConnectedSpace`.

The fourth field asks that the base change of `G ⊗ H` along `toAlgebraicClosure k`
have trivial unipotent radical. Write `b = toAlgebraicClosure k` and
`G_b = (GroupScheme.baseChange b).obj G`, and similarly `H_b`.

- `IsConnectedReductive.hasTrivialGeometricUnipotentRadical` says that `G_b` and `H_b`
  have trivial radicals.
- The structure morphism of `G_b` is `pullback.snd G.X.hom b`. It is affine because
  affine morphisms are stable under base change. It is locally of finite type because
  smooth morphisms are, and `Smooth → LocallyOfFinitePresentation → LocallyOfFiniteType`.
  These are Mathlib instances. The same holds for `H_b`.
- Step 1 over `AlgebraicClosure k` makes `G_b ⊗ H_b` have trivial radical.
- `HasTrivialUnipotentRadical.of_iso` along
  `baseChangeTensorIso b G H : (baseChange b).obj (G ⊗ H) ≅ G_b ⊗ H_b` transfers this
  to the base change of `G ⊗ H`.

### Step 4: Part 3, semisimplicity (`isSemisimple_tensor`)

`IsSemisimple` is a structure with two fields, `IsConnectedReductive` and
`HasFiniteCenter`. Step 3 gives the first for `G ⊗ H`, and `HasFiniteCenter.tensor`
gives the second.

### Conclusion (`directProductReductive`)

For given `k`, `G` and `H`, the three parts are `isPseudoReductive_tensor`,
`isConnectedReductive_tensor` and `isSemisimple_tensor`.

## Published inputs

Theorems used, with their modules:

- `Langlands.GroupScheme.HasTrivialUnipotentRadical.pi` and
  `Langlands.GroupScheme.isPseudoReductive_pi`:
  `Langlands.GroupScheme.Reductive.FiniteProducts`.
- `Langlands.GroupScheme.HasTrivialUnipotentRadical.of_iso` and
  `Langlands.GroupScheme.IsPseudoReductive.of_iso`:
  `Langlands.GroupScheme.Reductive.GeneralLinear`.
- `Langlands.GroupScheme.IsConnectedReductive.isPseudoReductive`:
  `Langlands.GroupScheme.Reductive.ToPseudoReductive`.
- `Langlands.GroupScheme.HasFiniteCenter.tensor`:
  `Langlands.GroupScheme.Reductive.ProductCenter`.

Constructions used, with their modules:

- `Langlands.GroupScheme.sumGroupFamily` and
  `Langlands.GroupScheme.finiteProductSumIso`:
  `Langlands.GroupScheme.SimplyConnected.AlmostSimpleProduct`.
- `Langlands.GroupScheme.baseChangeTensorIso`: `Langlands.GroupScheme.Torus.Products`.
- `Langlands.GroupScheme.pi`: `Langlands.GroupScheme.Products`.
- `Langlands.GroupScheme.baseChange`: `Langlands.AbelianScheme.GroupScheme`.
- The definitions in the statement: `IsPseudoReductive`, `IsConnectedReductive`,
  `HasTrivialUnipotentRadical` and `toAlgebraicClosure`
  (`Langlands.GroupScheme.Reductive.Basic`), and `IsSemisimple` and `HasFiniteCenter`
  (`Langlands.GroupScheme.Reductive.Semisimple`).

Mathlib inputs: `CategoryTheory.Limits.productUniqueIso`
(`Mathlib.CategoryTheory.Limits.Shapes.Products`), together with the instance
inference for base change of affine and smooth morphisms and for
`Smooth → LocallyOfFinitePresentation → LocallyOfFiniteType`.

## Provenance

This is an internal Lean proof of a derived statement; its sources are in the
statement's Markdown. The route follows the outline of Worker 3483's compiled draft
(Task 3483): identify `G ⊗ H` with a two-factor product, use the published
finite-product results, transport along the base-change tensor isomorphism, and use
`HasFiniteCenter.tensor`. That draft was not available in this instance, so the Lean
text was written again from the outline. It differs from the outline in two places:
the product identification uses `finiteProductSumIso` and `productUniqueIso`, and
smoothness, affineness and connectedness of `G ⊗ H` come from `isPseudoReductive_pi`
and `IsPseudoReductive.of_iso`, not from `prop_tensor_hom`.
