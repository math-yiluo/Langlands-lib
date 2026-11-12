# Norm compatibility of geometric Weil reciprocity along a field embedding

Author: Worker 5095, for task `37d6d58f-e378-4630-8a8c-0f3d7212a970`.

For an embedding `g : E → L` of finite extensions of `ℚ_p`, this module proves that
geometric local Weil reciprocity for `E` and for `L` fit in the norm square

```
W_L ──extensionWeilMap E L g──▶ W_E
 │                                │
 reciprocityUnits L eL            reciprocityUnits E eE
 ▼                                ▼
Lˣ ──────── N_{L/E} ───────────▶ Eˣ
```

This is the local case of Tate, *Number theoretic background* (1979), diagram
(1.2.2), printed p.4 (PDF p.13): for `E' ⊂ E` the norm `N_{E/E'} : C_E → C_{E'}`
corresponds under `r_E`, `r_{E'}` to the map `W_E^ab → W_{E'}^ab` induced by the
inclusion `W_E ⊂ W_{E'}`. For local fields `C_E = Eˣ`. The Library's reciprocity
candidates go from the Weil abelianization to the units, so the square is stated in
that direction.

Here the square is not assumed: it is derived from the relations that each field's
reciprocity satisfies on its own (`GeometricWeilReciprocityRelation`), together
with the norm-subgroup existence theorem and the norm-order laws already in the
Library. The arguments are internal; only the end result is the cited statement.

## Declarations

### `Langlands.PadicField.TopologicalData.eq_of_forall_openFiniteIndex`

For topological data `T` of a `p`-adic field `F` and units `a b : Fˣ` with
`ord b = ord a`, `ord a ≠ 0`, and `b ∈ V` for every open finite-index subgroup `V`
of `Fˣ` containing `a`, it follows that `a = b`.

Proof (by contradiction). Put `z = b / a ≠ 1`; it is a unit of the valuation ring
since the orders agree. `exists_open_finiteIndex_excluding` gives an open
finite-index `V₀` with `z ∉ V₀`. Let `n = |ord a| · [Fˣ : V₀]` and
`V = ⟨a⟩ ⊔ (V₀ ∩ O_Fˣ)`. Then `V` is open, since it contains the open subgroup
`V₀ ∩ O_Fˣ`. It has finite index, since it contains `V₀ ∩ ker(ord mod n)`: if
`n ∣ ord y`, write `ord y = ord a · m` with `a^m ∈ V₀`; then `y = a^m · (y a^{-m})`
with `y a^{-m} ∈ V₀ ∩ O_Fˣ`. As `a ∈ V`, the hypothesis gives `b ∈ V`, so `z ∈ V`.
Write `z = a^k w` with `w ∈ V₀ ∩ O_Fˣ`. Comparing orders gives `k · ord a = 0`, so
`k = 0`, and then `z = w ∈ V₀`, a contradiction.

### `Langlands.LocalClassField.normUnits_normUnits_mem_normSubgroup`

For fields `E, L, K, K'` with finite extensions `E ⊂ L ⊂ K'` and `E ⊂ K`, and a ring
map `φ : K → K'` with `φ(a) = a` on `E` (stated with the algebra maps), every
`z ∈ K'ˣ` satisfies `N_{L/E}(N_{K'/L} z) ∈ N_{K/E}(Kˣ)` (`normSubgroup E K`).

Proof: give `K'` the `E`-algebra structure through `L` and the `K`-algebra
structure through `φ`. Both towers are scalar towers, and `K'` is finite over `E`
and over `K`. Transitivity of the norm (`Algebra.norm_norm`) gives
`N_{K/E}(N_{K'/K} z) = N_{K'/E} z = N_{L/E}(N_{K'/L} z)`.

### `Langlands.LocalClassField.FiniteAbelianExtension.restriction_eq_one_iff`

For a finite abelian extension `A` of `K` inside the chosen algebraic closure and
`σ ∈ Gal(K̄/K)`: `A.restriction σ = 1` if and only if `σ` fixes `A`
(`σ ∈ A.fixingSubgroup`). This is `IntermediateField.restrictNormalHom_ker`.

### `Langlands.LocalClassField.FiniteAbelianExtension.ofOpenNormal` (definition)

Let `K` be a perfect field and `V` an open normal subgroup of `Gal(K̄/K)` with
`s t (t s)⁻¹ ∈ V` for all `s, t`. `ofOpenNormal V hV hcomm` is the finite abelian
extension of `K` in `K̄` whose underlying intermediate field is `fixedField V`.

The construction follows `exists_finiteAbelianExtension_of_isOpen`
(`Langlands.ClassFieldTheory.Local.WeilReciprocityUniquenessProof`), applied here to a
subgroup of the absolute Galois group itself.

- `V` is open, hence closed. The infinite Galois correspondence
  (`InfiniteGalois.fixingSubgroup_fixedField`) gives `fixingSubgroup (fixedField V) = V`.
- So the fixed field is finite (`InfiniteGalois.isOpen_iff_finite`) and Galois
  (`IsGalois.of_fixedField_normal_subgroup`).
- Its Galois group is commutative: lift two elements through the surjective
  restriction; their commutator lies in `V`, which is the kernel of restriction.

Two lemmas record the construction:

- `ofOpenNormal_toIntermediateField`: the field is `fixedField V` (by `rfl`);
- `ofOpenNormal_fixingSubgroup`: its fixing subgroup is `V`
  (`InfiniteGalois.fixingSubgroup_fixedField`).

### `Langlands.Weil.Local.reciprocityUnits_mem_normSubgroup_iff`

Let `e` be a reciprocity candidate for `E` satisfying
`GeometricWeilReciprocityRelation E E.canonicalTopologicalData e`. Then for every
finite abelian extension `K` of `E` and every `y ∈ W_E`,

`reciprocityUnits E e y ∈ N_{K/E}(Kˣ) ↔ localProjection E y fixes K`.

Proof: the finite norm-residue relation of the profinite reciprocity map
(component `he.2.1.2.1 K`) says that the kernel of its `K`-component is the norm
group. On `reciprocityUnits E e y`, the `K`-component is the restriction of
`localProjection E y` to `K`: the Galois-valued candidate map is
`e⁻¹ ∘ (projection of W_E to W_E^ab)` followed by the map to the Galois
abelianization, so `e⁻¹ ∘ e` cancels. Then `restriction_eq_one_iff` applies.

### `Langlands.Weil.Local.normUnits_reciprocityUnits_mem_normSubgroup`

For `g : E → L`, a candidate `eL` for `L` satisfying the geometric relation, a
finite abelian extension `K` of `E` and `y ∈ W_L` such that the Galois projection
of `extensionWeilMap E L g y` fixes `K`:

`N_{L/E}(reciprocityUnits L eL y) ∈ N_{K/E}(Kˣ)`,

where `L` is an `E`-algebra through `g` (`extensionAlgebra E L g`).

Proof. Let `ψ = extensionGaloisMap E L g : G_L → G_E` and
`V = ψ⁻¹(fixingSubgroup K)`. `V` is open (preimage under the continuous `ψ`) and
normal (preimage of a kernel). It contains all commutators, because `Gal(K/E)` is
commutative. Let `K' = ofOpenNormal V`, a finite abelian extension of `L` with field
`fixedField V` and fixing subgroup `V`. Since
`localProjection E (extensionWeilMap E L g y) = ψ (localProjection L y)` by
definition, `localProjection L y` fixes `K'`. So
`reciprocityUnits L eL y = N_{K'/L} z` for some `z` by
`reciprocityUnits_mem_normSubgroup_iff` for `L`. The closure embedding
`extensionClosureLift E L g` maps `K` into `K'`: for `σ ∈ V` and `x ∈ K`,
`σ(lift x) = lift(ψ σ x) = lift x` (`extensionClosureLift_galoisMap`). This gives
`φ : K → K'`. By `extensionClosureLift_algebraMap`, `φ` restricts to `g` on `E`.
`normUnits_normUnits_mem_normSubgroup` concludes.

### `Langlands.Weil.Local.reciprocityUnits_extensionWeilMap` (main theorem)

For `g : E.Carrier →ₐ[ℚ_p] L.Carrier`, candidates `eE`, `eL` satisfying
`GeometricWeilReciprocityRelation` for the canonical topological data of `E` and `L`,
and every `y ∈ W_L`:

`reciprocityUnits E eE (extensionWeilMap E L g y) = N_{L/E}(reciprocityUnits L eL y)`

(the norm is `Units.map (Algebra.norm E.Carrier)` for `extensionAlgebra E L g`).

Proof.

1. *Orders.* The geometric order relation (first component of the relation) gives
   `ord_E(reciprocityUnits E eE w) = localDegreeInt E w`, and likewise for `L`.
   `localDegreeInt_extensionWeilMap` gives `deg_E(extensionWeilMap y) = f · deg_L y`
   with `f = extensionResidueDegree E L g`. The residue degrees satisfy
   `f_L = f_E · f`, since `q_L = q_E^f` (`extensionResidueCardinality`) and
   `q = p^{f}` (`residueCardinality_eq_pow`). Then the first norm-order law
   (`relativeNormOrderLaws`), `f_E · ord_E(N x) = f_L · ord_L x`, becomes
   `ord_E(N x) = f · ord_L x`. Hence both sides of the square have order
   `f · deg_L y`.
2. *Nonzero degree.* If `deg_L y ≠ 0`, apply `eq_of_forall_openFiniteIndex` with
   `a = reciprocityUnits E eE (extensionWeilMap y)` and `b = N(reciprocityUnits L eL y)`;
   `ord a = f · deg_L y ≠ 0` since `f > 0`. For an open finite-index `V ∋ a`, the
   norm-subgroup existence theorem (`ClassFieldTheory.Local.normSubgroupExistence`)
   gives a finite abelian `K` with norm group `V`. By
   `reciprocityUnits_mem_normSubgroup_iff` for `E`, `a ∈ V` means that the Galois
   projection of `extensionWeilMap y` fixes `K`. Then
   `normUnits_reciprocityUnits_mem_normSubgroup` gives `b ∈ V`.
3. *Degree zero.* Let `Φ = localGeometricFrobenius L`, of degree `1`. Write
   `y = (y Φ) Φ⁻¹`, where `y Φ` and `Φ⁻¹` have degrees `1` and `-1`. All four
   maps in the square are homomorphisms, so step 2 for these two elements gives the
   result.

## Provenance

The main theorem is Tate (1979), (1.2.2), printed p.4, specialized to local fields
and to the Library's direction of reciprocity. All other declarations are internal
lemmas for its proof; the proof route (separation by open finite-index subgroups,
norm-subgroup existence, comparison field `fixedField (ψ⁻¹ (fixingSubgroup K))`)
is this module's own and is not taken from a source.
