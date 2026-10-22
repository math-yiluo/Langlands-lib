# A comparison chain map from the finite cyclic resolution to the bar resolution

This auxiliary module constructs an explicit chain map
`Langlands.Cohomology.CyclicH2.cyclicToBar k g hg` from the complex of Mathlib's
finite cyclic projective resolution `Rep.FiniteCyclicGroup.resolution k g hg` to
Mathlib's unnormalized bar complex `Rep.barComplex k G`. It is part of the proof
of the cyclic cocycle-sum comparison and does not itself establish that final
statement.

## Setting

Let `k : Type u` be a commutative ring and `G : Type u` a commutative group
with a `Fintype` instance. Let `g : G` satisfy `hg : ∀ x, x ∈ Subgroup.zpowers g`,
so that `g` generates `G`, and write `n = Fintype.card G`. No invertibility,
field, or nontriviality assumption is made; the group of order one is included.

Every term of the cyclic resolution is the left regular representation `k[G]`.
Its differential from degree one to degree zero is `g − 1`, and from degree two
to degree one it is the norm element `N = ∑_{h ∈ G} h`. The degree-`m` term of
the bar complex is the free representation on `G^m`; write `[a₁|…|aₘ]` for the
basis element `Finsupp.single ![a₁, …, aₘ] (MonoidAlgebra.single 1 1)`. Mathlib's
bar differential gives `d[a] = a·[] − []` and `d[a|b] = a·[b] − [ab] + [a]`.

## The components in degrees zero, one, and two

The components are the `k[G]`-linear maps out of `k[G]` determined, through
`Rep.leftRegularHom`, by the image of the unit `1 = MonoidAlgebra.single 1 1`:

- `CyclicToBar.f₀ k` sends `1` to `[]`;
- `CyclicToBar.f₁ k g` sends `1` to `[g]`;
- `CyclicToBar.f₂ k g` sends `1` to `∑_{i=0}^{n-1} [g^i | g]`.

The lemma `CyclicToBar.comm₁` proves `f₁ ≫ d₁₀ = d₁₀ ≫ f₀`: both sides send `1`
to `g·[] − []`. The lemma `CyclicToBar.comm₂` proves `f₂ ≫ d₂₁ = d₂₁ ≫ f₁`. On
the bar side, the boundary of `[g^i|g]` is `g^i·[g] + [g^i] − [g^(i+1)]`. Summing
over `0 ≤ i < n`, the last two terms telescope to `[1] − [g^n] = 0`, using
`g^n = 1`. The first terms give `∑_{i<n} g^i·[g]`. The helper
`CyclicToBar.sum_range_card_pow` reindexes `i ↦ g^i` as a bijection from
`{0, …, n−1}` onto `G`, so this sum equals `N·[g]`, the image of `1` on the
other side. Both commutativity proofs reduce to the unit through
`leftRegular_hom_ext`, which is the injectivity of `Rep.leftRegularHomEquiv`.

## The chain map

`cyclicToBar` is built with `ChainComplex.mkHom` from `f₀`, `f₁`, and `comm₁`.
The recursive step receives the previous two components together with their
commutation proof. In the step producing degree two, the definition tests
classically whether the supplied degree-one component equals `f₁`. If it does,
the step returns `f₂` with the proof `comm₂`. Otherwise, and in every step
producing degree three or higher, it returns Mathlib's
`ProjectiveResolution.liftFSucc` for the cyclic and bar resolutions. Since the
recursion actually supplies `f₁`, the lemma `cyclicToBar_f_two` shows that the
degree-two component is `f₂`; `cyclicToBar_f_zero` shows that the degree-zero
component is `f₀` by definition. The components in degrees three and higher
are noncanonical lifts and are not described further; the proof of the target
uses only degrees zero and two.

## Interface lemmas

- `cyclicToBar_f_two_single` states that the degree-two component sends `1` to
  `∑_{i ∈ Finset.range n} Finsupp.single ![g ^ i, g] (MonoidAlgebra.single 1 1)`.
- `cyclicToBar_f_zero_comp_π` states that composing the degree-zero component
  with the degree-zero augmentation of `Rep.barResolution k G` gives the
  degree-zero augmentation of the cyclic resolution. The bar augmentation is,
  by definition, the inverse of `Rep.diagonalSuccIsoFree k G 0` followed by
  `Rep.standardComplex.ε k G`. The helper `diagonalSuccIsoFree_inv_single`
  computes that inverse on basis elements: `single f (single h r)` goes to
  `single (h • Fin.partialProd f) r`. Hence `[]` maps to the identity element
  of `G`, which the standard augmentation sends to `1 : k`. The cyclic
  augmentation is `Rep.leftRegularHom (Rep.trivial k G k) 1`
  (`resolution_π_f_zero`), which also sends `1` to `1`.

## Provenance

The construction is an internal chain-level derivation from Mathlib's
definitions; it is not a verbatim result of the original literature. The
values `[]`, `[g]`, and `∑_{i<n} [g^i|g]` and the telescoping argument are the
comparison design recorded in the published statement
`Langlands.Cohomology.CyclicH2.CocycleSumComparison`, supplied by Worker 28 and
documented there by Worker 25. Worker 262 implemented this module.
