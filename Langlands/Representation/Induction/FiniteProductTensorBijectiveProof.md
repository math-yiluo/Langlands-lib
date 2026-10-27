# Bijectivity of the finite-product induction tensor map

This module proves the published proposition
`Langlands.Induction.FiniteProductTensorBijectiveTheorem.{uK,uI,uG,uV}` from
[`FiniteProductTensorBijectiveStatement`](FiniteProductTensorBijectiveStatement.md).
The closing theorem is

```
theorem Langlands.Induction.finiteProductTensorMap_bijective :
    FiniteProductTensorBijectiveTheorem.{uK, uI, uG, uV}
```

It keeps all four universes independent and adds no hypotheses. For every
field `k`, finite index type `ι` (including the empty type), groups `G i` that
are `NonarchimedeanGroup` and `WeaklyLocallyCompactSpace`, subgroups `P i` with
`CompactSpace (LeftQuotient (P i))`, vector spaces `V i` and arbitrary
representations `σ i : Representation k (P i) (V i)`, the published map
`finiteProductTensorMap P σ` from
[`FiniteProductTensor`](FiniteProductTensor.md) is bijective. Its target is
smooth induction from the literal `Subgroup.pi Set.univ P` with
`productInducing P σ`. The inducing actions need not be smooth, and nothing
is assumed about dimension or admissibility. The statement pair and its import
closure are unchanged. This module imports the statement module,
[`CompactLocalSection`](CompactLocalSection.md),
[`Tensor/FiniteProperties`](../Tensor/FiniteProperties.md) and Mathlib's
`Mathlib.GroupTheory.DoubleCoset`.

Inside the proof, `classical` and `Fintype.ofFinite ι` turn `Finite ι` into
`Fintype ι` and `DecidableEq ι`. The two halves are
`FiniteProductTensorBijective.finiteProductTensorMap_injective` and
`FiniteProductTensorBijective.finiteProductTensorMap_surjective`. All
auxiliary declarations are in the namespace
`Langlands.Induction.FiniteProductTensorBijective`.

## One factor: double-coset sections

Section `Factor` fixes a field `k`, a topological group `G`, a subgroup `P`, a
representation `σ : Representation k P V` and an open subgroup `K`.

- `smoothFunctions_ext`: two elements of `SmoothFunctions P σ` are equal when
  their values (`eval`) agree at every point.
- `evalLinear y`: evaluation at `y` as a `k`-linear map. `eval_zero` and
  `eval_sum` follow: evaluation sends `0` to `0` and commutes with finite sums.
- `doubleClass P K y`: the class `DoubleCoset.mk P K y` of `y` in Mathlib's
  `DoubleCoset.Quotient P K`, that is, `P \ G / K`.
- `finite_doubleCosetQuotient`: if `LeftQuotient P` is compact, then
  `P \ G / K` is finite. The published
  `exists_finset_doubleCoset_cover` (in `CompactQuotientProof`) gives a finite
  `t : Finset G` with every `y` of the form `p * i * l`, where `i ∈ t`,
  `p ∈ P` and `l ∈ K`. Hence `i ↦ doubleClass P K i` maps `t` onto the
  quotient. The cover may list one double coset more than once, so the proof
  sums over the quotient itself, which has each class once. A representative
  is `q.out`, and `DoubleCoset.out_eq'` says `q.out` lies in `q`.

From here on, `K` also has compact underlying set (`hK`). The published
`compactDoubleCosetSection P σ K hK x v hv` (in `CompactLocalSection`) is a
compactly supported section for every `v` fixed by
`conjOpenSubgroup P K x = P ∩ x K x⁻¹`.

- `section_eval_mul`: for `a ∈ P` and `b ∈ K`, the section takes the value
  `σ a v` at `a * x * b`. This restates `compactDoubleCosetSection_apply`.
- `section_eval_of_ne`: the section vanishes at every `y` whose double coset
  differs from that of `x`. If the value at `y` were nonzero, then by
  `compactDoubleCosetSection_support_subset` the coset `P y` would equal
  `P (x * l)` for some `l ∈ K`. Then `y * (x * l)⁻¹ ∈ P`, which puts `y` in
  `P x K`, a contradiction.
- `sectionMap P σ K hK x`: the section construction as a `k`-linear map from
  the fixed space `fixedVectors σ (conjOpenSubgroup P K x)` to
  `SmoothFunctions P σ`. To check additivity and homogeneity, evaluate at `y`.
  If `y = a * x * b` lies in `P x K`, both sides are computed by
  `section_eval_mul`, using linearity of `σ a`. Otherwise both sides are `0`
  by `section_eval_of_ne`.
- `pointEvaluation P σ K x`: the `k`-linear map that evaluates a `K`-fixed
  smooth induced function at `x`. It lands in the fixed space of
  `conjOpenSubgroup P K x` by the published `eval_mem_fixedVectors`.
- `subtype_eq_sum`: when the quotient `P \ G / K` has a `Fintype` instance,
  the inclusion of `fixedVectors (smoothInduced P σ) K` into the smooth
  functions equals
  `∑ q, sectionMap P σ K hK q.out ∘ₗ pointEvaluation P σ K q.out`.
  Evaluate both sides at `y`. Only the term for `q = doubleClass P K y` can be
  nonzero, by `section_eval_of_ne`. For that term write `y = a * q.out * b`.
  The fixed function `f` takes the value `σ a (f q.out)` at `y`, by the
  published `eval_mul_of_mem_fixedVectors` and `eval_covariant`, and
  `section_eval_mul` gives the same value for the section.

## Products of sections

Section `Product` works with families `G i`, `P i`, `σ i` and open subgroups
`K i`.

- `productSection P σ K hK x`: the tensor product
  `PiTensorProduct.map (fun i => sectionMap (P i) (σ i) (K i) (hK i) (x i))`.
  It sends `⨂ i, fixedVectors (σ i) (conjOpenSubgroup (P i) (K i) (x i))` to
  `⨂ i, SmoothFunctions (P i) (σ i)`.
- `coefficientInclusion P σ K x`: the tensor product of the inclusions of
  those fixed spaces into `V i`. Its target is `⨂ i, V i`.
- `map_subtype_injective`: over a field, the tensor product of the inclusions
  of any submodules `W i ≤ V i` is injective. Choose complements `C i` with
  `Submodule.exists_isCompl`. The tensor product of the projections
  `Submodule.projectionOnto (W i) (C i)` is a left inverse, because
  `PiTensorProduct.map_comp` and `PiTensorProduct.map_id` reduce the
  composite to the identity.
- `eval_productSection`: for `p ∈ Subgroup.pi Set.univ P` and `b` with every
  `b i ∈ K i`, the image of `t` under
  `finiteProductTensorMap P σ ∘ productSection P σ K hK x` takes the value
  `productInducing P σ p (coefficientInclusion P σ K x t)` at `p * x * b`.
  Both sides are linear in `t`, so `PiTensorProduct.ext` reduces this to pure
  tensors. For those, the published `finiteProductTensorMap_tprod_eval` and
  `productInducing_tprod` reduce it to `section_eval_mul` in each coordinate.
- `eval_productSection_self`: with `p = 1` and `b = 1`, that value at `x` is
  `coefficientInclusion P σ K x t`.
- `eval_productSection_of_ne`: the same image vanishes at every `g` with some
  coordinate `g j` outside the double coset of `x j`. On pure tensors the
  `j`-th factor of the value is `0` by `section_eval_of_ne`, and
  `MultilinearMap.map_coord_zero` makes the pure tensor `0`.
- `exists_decomposition`: if `g i` lies in the double coset of `x i` for every
  `i`, then `g = p * x * b` with `p ∈ Subgroup.pi Set.univ P` and every
  `b i ∈ K i`. The coordinate factors are chosen with `choose`.
- `eval_mem_fixedVectors_pi`: let `F` be a smooth function on the product that
  is invariant under right translation by every `b` with `b i ∈ K i`. Then
  `F x` is fixed by `FiniteTensor.external σ` restricted to
  `Subgroup.pi Set.univ (fun i => conjOpenSubgroup (P i) (K i) (x i))`. This
  lemma transports the actual product-subgroup action explicitly. An element
  `a` of this coordinate product gives an element `p` of
  `Subgroup.pi Set.univ P` with the same coordinates. The action
  `FiniteTensor.external σ a` is `productInducing P σ p` by definition. Since
  every `(x⁻¹ * p * x) i` lies in `K i` (by `mem_conjOpenSubgroup`),
  covariance and right invariance give
  `productInducing P σ p (F x) = F (p * x) = F (x * (x⁻¹ * p * x)) = F x`.

## Levels

Section `Main` assumes the hypotheses of the target, with `Fintype ι` and
`DecidableEq ι`.

- `exists_compact_level`: every family of open subgroups `L i` contains a
  family of compact open subgroups `K i`. Apply the published
  `Langlands.compactOpenSubgroupBasis` in each factor. It uses the
  nonarchimedean and weakly locally compact hypotheses.
- `range_map_fixed_mono`: if `M i ⊆ L i` for every `i`, then the range of the
  tensor product of the inclusions of `L`-fixed vectors lies in the range for
  `M`. The `L`-inclusion factors through the `M`-inclusion via
  `Submodule.inclusion`.
- `exists_level`: every `z : ⨂ i, SmoothFunctions (P i) (σ i)` lies in that
  range for some family of open subgroups `L`. By induction on `z`: a scaled
  pure tensor is handled by the published `smoothInduced_smooth`, which gives
  an open stabilizer for each factor. For a sum, use the intersections
  `L i ⊓ M i` and `range_map_fixed_mono`.

## Surjectivity

`finiteProductTensorMap_surjective`. Let `F` be a smooth function on the
product. `smoothInduced_smooth` gives an open subgroup `L` of `∀ i, G i` that
fixes `F`. Its preimages under the continuous homomorphisms
`MonoidHom.mulSingle G i` are open subgroups of the factors. Shrink them to
compact open subgroups `K i` with `exists_compact_level`. If every `b i` lies
in `K i`, then `b ∈ L` by `Subgroup.pi_mem_of_mulSingle_mem`. So `F` is right
invariant under all such `b`, which is the uniform open right stabilizer used
in the argument.

Each `P i \ G i / K i` is finite and is given a `Fintype` instance. For a
tuple `q` of classes, let `rep q` be the tuple of representatives
`(q i).out`. By `eval_mem_fixedVectors_pi`, the published
`FiniteTensor.fixedVectors_external_le` (in `Tensor/FiniteProperties`, valid
over a field without finite-dimensionality) gives a tensor `t q` with
`coefficientInclusion P σ K (rep q) (t q) = F (rep q)`. The candidate preimage
is `∑ q, productSection P σ K hK (rep q) (t q)`.

To compare values at `g`, let `q0` be the tuple of classes of the coordinates
of `g`. Every term with `q ≠ q0` vanishes at `g` by
`eval_productSection_of_ne`, because some coordinate class differs. For
`q0`, `exists_decomposition` writes `g = p * rep q0 * b`. Then
`eval_productSection`, the choice of `t q0`, covariance (`eval_covariant`)
and right invariance give the value `F g`.

## Injectivity

`finiteProductTensorMap_injective`. Suppose `z` maps to `0`. By `exists_level`
and `exists_compact_level`, `z` comes from a tensor `y` of `K`-fixed
functions for a compact open family `K` (`range_map_fixed_mono` passes to the
smaller level). Equip each quotient with a `Fintype` instance and define `rep`
as before.

The key identity `hexp` expands the tensor product of the inclusions of the
`K`-fixed spaces as
`∑ q, productSection P σ K hK (rep q) ∘ₗ PiTensorProduct.map (fun i => pointEvaluation (P i) (σ i) (K i) (rep q i))`.
Substitute `subtype_eq_sum` in every factor. Then `MultilinearMap.map_sum`,
applied to `PiTensorProduct.mapMultilinear`, turns the tensor product of the
finite sums into a sum over tuples of classes. This also covers the empty
family. Each term is rewritten with `PiTensorProduct.map_comp`.

For each tuple `q0`, evaluate the zero image at `rep q0`. The terms for
`q ≠ q0` vanish by `eval_productSection_of_ne`. By `eval_productSection_self`,
the term for `q0` is the `coefficientInclusion` of the coefficient
`u q0 = PiTensorProduct.map (fun i => pointEvaluation ... (rep q0 i)) y`. So
this inclusion of `u q0` is `0`, and `map_subtype_injective` gives
`u q0 = 0`. By `hexp`, `z` is the sum of the `productSection` images of the
`u q`, so `z = 0`.

## Provenance

The theorem is a derived internal extension of I. N. Bernstein and
A. V. Zelevinsky, *Induced representations of reductive p-adic groups I*,
Ann. Sci. ENS (4) 10 (1977), 441–472 (registered as
`bernstein-zelevinsky-1977-induced-i`). Section 1.8(a), printed p. 444, defines
induction by covariance and uniform right invariance. Proposition 1.9(e),
printed p. 445, identifies smooth and compact induction when `G` is compact
modulo the inducing subgroup. Proposition 1.9(g), on the same page, states
that compact induction commutes with external tensor factors and is called
directly verifiable there. The original does not state this finite-family
version over an arbitrary field with arbitrary inducing actions. The proof
above is an implementation of that direct verification with double-coset
sections. It follows the route Worker 321 suggested in the task context:
compact levels inside a uniform stabilizer via `MonoidHom.mulSingle`, distinct
double-coset representatives, sections from `compactDoubleCosetSection`,
`fixedVectors_external_le` for surjectivity, and `MultilinearMap.map_sum` with
split inclusions for injectivity. Worker 321 contributed that proof design
and is credited as a coauthor. Worker 256 wrote the Lean declarations, the
lemma decomposition and the proofs.
