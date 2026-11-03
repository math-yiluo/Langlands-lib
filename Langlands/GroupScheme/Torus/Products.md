# Finite products of tori

Worker 1143.

This module proves that finite products of tori over a field are tori. It
also gives the group-scheme isomorphisms used in the proof. These are
internal consequences of the published definitions
`Langlands.GroupScheme.IsSplitTorus` (`Torus/Split.lean`) and
`Langlands.GroupScheme.IsTorus` (`Torus/Lattice.lean`). A group scheme over a
field `k` is a torus if it becomes isomorphic to a split torus `𝔾_m^I`, with
`I` finite, after base change to some extension field of `k` in the same
universe. No separability, characteristic or perfectness condition appears
anywhere. Products are the categorical ones in `GroupScheme S = Grp (Over S)`:
the binary product `G ⊗ H` of the cartesian monoidal structure, and the finite
product `pi G = ∏ᶜ G` of `Products.lean`.

## Base change of binary products

`baseChangeTensorIso b G H` is an isomorphism of group schemes over `S'`,
`(baseChange b).obj (G ⊗ H) ≅ (baseChange b).obj G ⊗ (baseChange b).obj H`, for
any morphism of schemes `b : S' ⟶ S`. Here
`baseChange b = (Over.pullback b).mapGrp`. Pullback along `b` is a braided
functor of the cartesian monoidal categories `Over S ⥤ Over S'`, so Mathlib's
`Functor.mapGrp.instMonoidal` makes `baseChange b` monoidal. The isomorphism is
the inverse of that structure map `Functor.Monoidal.μIso`.

## Isomorphisms between products

- `piOptionMulEquiv` is `Equiv.piOptionEquivProd` as a multiplicative
  equivalence: a family over `Option α` corresponds to its value at `none`
  together with the family of its values at `some a`.
- `piOptionIso G : pi G ≅ G none ⊗ pi (fun a => G (some a))`, for a family `G`
  indexed by `Option α` with `α` finite. The proof builds it from points with
  the published `isoOfPoints`. On each test scheme `T`, `piOptionPointsEquiv`
  composes the point descriptions `piPointsEquiv` and `productPointsEquiv`
  with `piOptionMulEquiv`. `productPointsEquiv_piOptionPointsEquiv` computes
  its two coordinates. `piOptionPointsEquiv_naturality` proves naturality in
  `T`, comparing coordinates with the universal properties of the two
  products.
- `piEquivIso e H : pi (fun a => H (e a)) ≅ pi H` reindexes a finite product
  along an equivalence `e : α ≃ β`. It is Mathlib's `Pi.whiskerEquiv` with
  identity isomorphisms on the factors.
- `piEmptyIso H : pi H ≅ splitTorus S PEmpty`: two products indexed by the
  empty type are isomorphic, again by `Pi.whiskerEquiv`.
- `tensorUnitIso : 𝟙_ (GroupScheme S) ≅ splitTorus S PEmpty`: both group
  schemes are terminal objects of `GroupScheme S`. For the empty product the
  module checks this directly from `Pi.lift` and `Pi.hom_ext`.
  `isSplitTorus_tensorUnit` then says that the trivial group scheme is a split
  torus of rank zero.

## Tori over a field

All statements in this part are over `Spec k` for a field `k`.

- `IsSplitTorus.tensor_isTorus`: if `G` is a split torus and `H` is a torus,
  then `G ⊗ H` is a torus. Let `L` be a splitting field of `H`. By the
  published `IsSplitTorus.baseChange`, `G` stays split over `L`. The published
  `IsSplitTorus.tensor` says that the product of the two split base changes is
  split. `baseChangeTensorIso` identifies that product with the base change of
  `G ⊗ H`, so `L` splits `G ⊗ H`.
- `IsTorus.tensor`: the product of two tori is a torus. Let `K` be a
  splitting field of `G`. Over `K`, the base change of `G` is split and the base
  change of `H` is a torus by the published `IsTorus.baseChange`. The previous
  result and `baseChangeTensorIso` show that the base change of `G ⊗ H` to `K`
  is a torus. The published `IsTorus.of_baseChange` then descends this to `k`.
- `isTorus_tensorUnit`: the trivial group scheme is a torus.
- `IsTorus.pi`: for a finite index type `I : Type u` and a family `T` of tori,
  `pi T` is a torus. The proof uses `Finite.induction_empty_option`. An
  equivalence of index types is handled by `piEquivIso`. The empty product is
  the rank-zero split torus by `piEmptyIso`. The step from `α` to `Option α`
  combines `piOptionIso` with `IsTorus.tensor`.

The published `IsTorus.of_iso` from `Torus/MaximalTransport.lean` transports
the torus predicate along each group-scheme isomorphism used in the proof.

The module only proves facts about the existing predicates; it adds no
hypotheses to them. It does not compute the rank or the character lattice of a
product.
