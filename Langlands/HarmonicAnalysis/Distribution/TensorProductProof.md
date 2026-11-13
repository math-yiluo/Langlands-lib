# Renard II.1.3: proof of the product, tensor, Fubini and support assertions

Worker 69, Task 5751. The theorem
`Langlands.HarmonicAnalysis.Distribution.TensorProductProof.assertions` proves the
published proposition
`Langlands.HarmonicAnalysis.Distribution.TensorProductStatements.Assertions` at its
two universe parameters `uX` and `uY`. It proves all nine conjuncts under the
target's original hypotheses: arbitrary topological spaces `X` and `Y` that are
t.d., given as `IsLocallyProfinite` in the first conjunct and as the three
instance classes `T2Space`, `LocallyCompactSpace` and `TotallyDisconnectedSpace`
in the other eight. No nonemptiness, countability or metrizability is assumed.
The target pair and its imports are unchanged.

The source is David Renard, *Représentations des groupes réductifs p-adiques*,
French version of 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`, subsection
II.1.3, printed p.32 / PDF p.38. The route below is an internal deduction from the
published Library and pinned Mathlib. The source states the topological facts
without proof. It sketches the rectangle partition (by II.1.1 (ii)), the
isomorphism (from the rectangle decomposition), Fubini (reduction to finite sums)
and the support formula (restriction to rectangles). The proof here follows the
source for Fubini. It differs for the rectangle partition, the injectivity of the
tensor map and the support formula, as explained in those sections.

The module imports the statement module and two Mathlib files,
`Mathlib.LinearAlgebra.Basis.VectorSpace` and
`Mathlib.LinearAlgebra.TensorProduct.Basis`. Through the statement module it uses
the published `SchwartzBruhatProduct`, `Distribution.TensorProduct`,
`Distribution.TopologicalSupport`, `Distribution.Subspace`, `AlgebraicIntegrand`
and `Topology.LocallyProfinite`. It introduces no new statement and no axiom.

## The rectangle lemma

`exists_rectangle_expansion` is the one geometric lemma. Its only hypothesis is
`[T2Space X]`. Let `f : SchwartzBruhat (X × Y)` and let `F x = (y ↦ f (x, y))` be
the curried function `X → (Y → ℂ)`. The lemma gives `n`, sets `U i ⊆ X` and
`V i ⊆ Y` that are compact and clopen, and constants `c i ≠ 0` with these
properties:

- distinct indices give disjoint rectangles `U i ×ˢ V i`;
- `f = c i` on `U i ×ˢ V i`;
- every point with `f z ≠ 0` lies in some rectangle.

The rectangles are the fibers of the map `z ↦ (F z.1, f z)` over the values it
takes at points with `f z ≠ 0`. This value set is finite. It lies in
`range F ×ˢ range f`, and both ranges are finite by the published
`finite_range_of_locallyConstant_of_hasCompactSupport`. That lemma applies to `F`
by the published `SchwartzBruhat.isLocallyConstant_curry` and
`SchwartzBruhat.hasCompactSupport_curry`, and to `f` directly. The value set is
enumerated by `Fin n` and a representative point `z i` is chosen for each value.
Then

- `U i = {x | F x = F (z i).1}` is a fiber of the locally constant map `F`, so it
  is clopen;
- `V i = {y | f ((z i).1, y) = f (z i)}` is a fiber of the locally constant map
  `y ↦ f ((z i).1, y)`, so it is clopen.

On `U i ×ˢ V i` one has `f (x, y) = F x y = F (z i).1 y = f (z i)`, so `c i` is
`f (z i)`. This is nonzero by the choice of `z i`. Every point of `U i` has a
nonzero value at `(x, (z i).2)`, so `U i` is a closed subset of the compact
projection of `tsupport f` to `X`. Hence `U i` is compact, and `V i` is compact
in the same way. If a point `(x, y)` lies in two rectangles `i` and `j`, both
representatives have the value `(F x, f (x, y))`, so `i = j`. A point `w` with
`f w ≠ 0` lies in the rectangle of the value `(F w.1, f w)`.

`characteristic_prod` states that the characteristic function of `U ×ˢ V` equals
`SchwartzBruhat.tensor (characteristic U) (characteristic V)`. It is checked
pointwise in the four cases `x ∈ U` or not and `y ∈ V` or not.

## Conjuncts 1 and 2: the product topology

`productLocallyProfinite`: the two `IsLocallyProfinite` hypotheses give the three
instance classes on each factor. Mathlib's product instances give them on
`X × Y`, and the published `Langlands.Topology.isLocallyProfinite_of_mathlib`
turns them back into `IsLocallyProfinite (X × Y)`.

`compactOpenRectangleBasis` uses Mathlib's
`isTopologicalBasis_of_isOpen_of_nhds`. Every rectangle of compact open sets is
open. If `(x, y)` lies in an open `W`, then `isOpen_prod_iff` gives open
`U ∋ x` and `V ∋ y` with `U ×ˢ V ⊆ W`. The published
`hasCompactOpenNeighborhoodBasis_of_mathlib` gives compact open `U' ⊆ U` and
`V' ⊆ V` around `x` and `y`, and `U' ×ˢ V'` is the required basis element.

## Conjuncts 3 and 4: rectangle partition and indicator decomposition

Renard refines a finite cover by rectangles to a disjoint one using II.1.1 (ii).
The proof here does not do this. It applies the rectangle lemma instead.

`compactOpenRectanglePartition`: a compact open `K` is closed because `X × Y` is
Hausdorff, so `characteristic K` is a test. The rectangle lemma applied to it
gives disjoint compact clopen rectangles. On each rectangle the indicator equals
a nonzero constant, so each rectangle lies in `K`. Every point of `K` has value 1,
so it lies in some rectangle. Hence the union of the rectangles is exactly `K`.

`rectangleIndicatorDecomposition`: the rectangle lemma applied to `f` gives the
sets, the clopenness and compactness proofs, the disjointness and the
coefficients `c i`. The first identity
`f = Σ i, c i • characteristic (U i ×ˢ V i)` is checked pointwise at `w`. If
`f w = 0`, then `w` lies in no rectangle, since there `f = c i ≠ 0`, so every
summand vanishes. Otherwise `w` lies in some rectangle `i`, and by disjointness
only the summand `i` survives (`Finset.sum_eq_single`). That summand is
`c i = f w`. The second identity follows from the first by rewriting each
summand with `characteristic_prod`.

## Conjunct 5: bijectivity of the tensor map

`exists_eq_sum_tensor` restates the published
`SchwartzBruhat.exists_tensor_expansion` as an equality of tests:
`f = Σ j, SchwartzBruhat.tensor (α j) (β j)`.

Surjectivity (`tensorLinearMap_surjective`): `Σ j, α j ⊗ₜ β j` maps to `f`.

The source derives the isomorphism from the rectangle decomposition and gives no
separate injectivity argument. Injectivity (`tensorLinearMap_injective`) is
proved here by a basis argument and needs no hypothesis on `X` or `Y`. Choose a basis `b` of `SchwartzBruhat X` (`Module.Basis.ofVectorSpace`). By
Mathlib's `TensorProduct.eq_repr_basis_left`, every tensor has the form
`Σ i ∈ c.support, b i ⊗ₜ c i` for a finitely supported
`c : ι →₀ SchwartzBruhat Y`. If its image is zero, then for every `x` and `y`,
`Σ i ∈ c.support, b i x * c i y = 0`. For fixed `y` this says that
`Σ i ∈ c.support, (c i y) • b i = 0` in `SchwartzBruhat X`. Linear independence
of `b` (`linearIndependent_iff'`) gives `c i y = 0` for every `i` in the support.
Off the support `c i = 0` anyway. Hence `c = 0` and the tensor is zero. The
conclusion uses `injective_iff_map_eq_zero`.

## Conjuncts 6 and 7: uniqueness of the tensor product and Fubini

`tensorExistsUnique`: existence is the published
`Distribution.tensor_apply_tensor`. For uniqueness, let `D` agree with
`Distribution.tensor T S` on external products. Every test is a finite sum of
external products by `exists_eq_sum_tensor`, and both functionals are linear, so
they agree on every test.

`fubini`: the first formula holds by `rfl`, because the published
`Distribution.tensor T S` is defined as `T ∘ partialApplySnd S`. For the second,
expand `f` as `Σ j, SchwartzBruhat.tensor (α j) (β j)`. Both sides are linear in
`f`. On each summand the left side is `T (α j) * S (β j)` by
`tensor_apply_tensor`. The right side is
`S (partialApplyFst T (tensor (α j) (β j))) = S (T (α j) • β j)` by the published
`partialApplyFst_tensor`, and this is `T (α j) * S (β j)` by linearity of `S`.
This is the source's reduction of the integrals to finite sums.

## Conjuncts 8 and 9: supports

Two helper lemmas are stated for a Hausdorff space `Z`. The first also assumes
`Z` locally compact and totally disconnected.

- `apply_eq_zero_of_restrictOpen_eq_zero`: if `restrictOpen hW D = 0` for an open
  `W`, then `D f = 0` for every test `f` vanishing off `W`. The support of `D`
  lies in `Wᶜ` by the definition of the support (`not_mem_support_iff`). The
  published `support_subset_iff_mem_supportedOn` then turns this into the
  annihilator condition on the closed set `Wᶜ`.
- `exists_apply_ne_zero_of_mem_support`: if `x ∈ support D` and `U` is an open
  neighborhood of `x`, there is a test `f` vanishing off `U` with `D f ≠ 0`.
  Otherwise `D` kills `extendZero hU g` for every test `g` on `U`, which vanishes
  off `U` (`extendZero_apply_of_not_mem`). Then `restrictOpen hU D = 0`, and `x`
  is not in the support.

`supportTensor` proves the two inclusions.

- `⊆`: the set `support T ×ˢ support S` is closed. By
  `support_subset_iff_mem_supportedOn` it suffices that `tensor T S f = 0` for
  every test `f` vanishing on this set. Now
  `tensor T S f = T (partialApplySnd S f)`. For `x ∈ support T`, the slice
  `y ↦ f (x, y)` vanishes on `support S`, so `S` kills it by the published
  `mem_supportedOn_support S`. Thus `partialApplySnd S f` vanishes on
  `support T`, and `T` kills it by `mem_supportedOn_support T`.
- `⊇`: let `x ∈ support T` and `y ∈ support S`, and suppose `(x, y)` is not in the
  support of `tensor T S`. Then some open `W ∋ (x, y)` has
  `restrictOpen W (tensor T S) = 0`. By `isOpen_prod_iff` there are open
  `U ∋ x` and `V ∋ y` with `U ×ˢ V ⊆ W`. The second helper gives tests `φ` and
  `ψ` vanishing off `U` and off `V` with `T φ ≠ 0` and `S ψ ≠ 0`. The external
  product `tensor φ ψ` vanishes off `U ×ˢ V`, hence off `W`, so the first helper
  gives `tensor T S (tensor φ ψ) = 0`. But this value is `T φ * S ψ ≠ 0`.

Renard proves the support formula by restricting `T1 ⊗ T2` to an open rectangle
`U × V` and identifying the restriction with `T1,U ⊗ T2,V`. The proof here does
not state or use that identification. It tests directly with external products
of tests supported in `U` and `V`.

`compactSupportTensor`: by `supportTensor`, the support of `tensor T S` is
`support T ×ˢ support S`, which is compact by `IsCompact.prod`. Membership in
`Distribution.compactlySupported` is by definition compactness of the support,
so the second part is the same implication.

## Assembly

`assertions` is the conjunction of the nine theorems `productLocallyProfinite`,
`compactOpenRectangleBasis`, `compactOpenRectanglePartition`,
`rectangleIndicatorDecomposition`, `tensorLinearMapBijective`,
`tensorExistsUnique`, `fubini`, `supportTensor` and `compactSupportTensor`, in the
order of `Assertions`.
