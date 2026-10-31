# Homology comparison for acyclic terms and acyclic homology: proof

Author: Worker 281. This module proves Worker 595's statement
`Langlands.Cohomology.AcyclicTermsHomologyComparisonStatement` from the module
`Langlands.Cohomology.AcyclicResolution.AcyclicTermsHomologyComparisonStatement`. It imports
that statement module unchanged. It also imports Worker 61's
`Langlands.Cohomology.RightDerivedSequence`, the long exact sequence of right derived
functors in the namespace `Langlands.Cohomology.DerivedPlus`, and Worker 716's
`Langlands.Cohomology.AcyclicResolution.ComparisonProof`.

Composition `f ≫ g` is `f` followed by `g`. `RᵏF` is Mathlib's `F.rightDerived k`. An object
`X` is *`F`-acyclic* if `(F.rightDerived (r + 1)).obj X` is zero for every `r : ℕ`. For the
complex `K : CochainComplex C ℕ`, write `Kⁿ` for `K.X n`, `Zⁿ` for Mathlib's cycles object
`K.cycles n` and `Hⁿ` for `K.homology n`. Mathlib's maps are `K.iCycles n : Zⁿ ⟶ Kⁿ`,
`K.toCycles i n : Kⁱ ⟶ Zⁿ` (the differential lifted to the cycles) and
`K.homologyπ n : Zⁿ ⟶ Hⁿ`. `F K` is the mapped complex
`(F.mapHomologicalComplex (ComplexShape.up ℕ)).obj K`.

## Theorem

`Langlands.Cohomology.acyclicTermsHomologyComparisonStatement :
AcyclicTermsHomologyComparisonStatement.{u, v, u', v'}`, with all four universe parameters
free and no hypotheses beyond those of the statement. Spelled out: let `C : Type u` be an
abelian category (`Category.{v} C`) with `[HasInjectiveResolutions C]`, let `D : Type u'` be
an abelian category (`Category.{v'} D`), and let `F : C ⥤ D` be additive and preserve finite
limits. Let `K : CochainComplex C ℕ` be a complex such that every term `Kⁱ` and every homology
object `Hⁱ` is `F`-acyclic. Then for every `n : ℕ` there is an isomorphism from the
degree-`n` homology of `F K` to `F.obj Hⁿ`. The complex need not be exact.

The statement's Markdown gives its provenance: an internal statement motivated by dimension
shifting. The Lean proof follows that sketch. Induction shows that all cycles and boundaries
are `F`-acyclic. Then `F` keeps the two short exact sequences exact, and the resulting kernel
and cokernel identifications compute the homology of `F K`.

## Helper results

All helpers are in the namespace `Langlands.Cohomology.AcyclicTermsComparison`.

### The two short exact sequences (section `Sequences`)

Here `C` is any abelian category and `K : CochainComplex C ℕ`.

- `homologySc K i j`: the short complex `Kⁱ ⟶ Zʲ ⟶ Hʲ` with maps `K.toCycles i j` and
  `K.homologyπ j`. Its cycles object, the kernel of `Zʲ ⟶ Hʲ`, is used as the boundaries
  object `Bʲ`. No separate image construction is used.
- `homologySc_exact K i j hi`: if `(ComplexShape.up ℕ).prev j = i`, this short complex is
  exact. Mathlib's `K.homologyIsCokernel i j hi` says that `K.homologyπ j` is a cokernel of
  `K.toCycles i j`.
- `boundariesSc K i j`: the short complex `Bʲ ⟶ Zʲ ⟶ Hʲ`, with the inclusion of the cycles of
  `homologySc K i j` followed by `K.homologyπ j`.
- `boundariesSc_shortExact K i j`: `0 ⟶ Bʲ ⟶ Zʲ ⟶ Hʲ ⟶ 0` is short exact. The first map is
  a kernel of the second by construction, it is a monomorphism, and `K.homologyπ j` is an
  epimorphism.
- `iCycles_toCycles K i j`: `K.iCycles i ≫ K.toCycles i j = 0`. After composing with the
  monomorphism `K.iCycles j`, this is `K.iCycles i ≫ K.d i j = 0`.
- `cyclesSc K i j`: the short complex `Zⁱ ⟶ Kⁱ ⟶ Bʲ`, with `K.iCycles i` followed by the
  lift of `K.toCycles i j` to the cycles of `homologySc K i j`. It is a complex by
  `iCycles_toCycles`.
- `cyclesSc_shortExact K i j hij`: if `i + 1 = j`, then `0 ⟶ Zⁱ ⟶ Kⁱ ⟶ Bʲ ⟶ 0` is short
  exact. For exactness in the middle, a morphism of short complexes goes from `cyclesSc K i j`
  to `Zⁱ ⟶ Kⁱ ⟶ Kʲ` (with maps `K.iCycles i` and `K.d i j`). It is the identity on the first
  two terms and the monomorphism `Bʲ ⟶ Zʲ ⟶ Kʲ` on the third. The target is exact by
  Mathlib's `K.cyclesIsKernel`, so the source is exact by
  `ShortComplex.exact_iff_of_epi_of_isIso_of_mono`. The last map is an epimorphism because
  `homologySc K i j` is exact (`homologySc_exact`, using `CochainComplex.prev_nat_succ`).

### Acyclicity of cycles and boundaries (section `Acyclic`)

This section assumes `[EnoughInjectives C]` and chosen derived categories
`[HasDerivedCategory.{w} C]` and `[HasDerivedCategory.{w'} D]`, the setting of Worker 61's long
exact sequence. `F` is additive. `hX` and `hH` are the statement's two acyclicity hypotheses.

- `isZero_rightDerived_boundaries F K hX i hZ r`: if `Zⁱ` is `F`-acyclic, then so is `Bⁱ⁺¹`.
  `DerivedPlus.rightDerived_exact₃` applied to `cyclesSc_shortExact K i (i + 1)` in degrees
  `r + 1` and `r + 2` makes `R^{r+1}F Kⁱ ⟶ R^{r+1}F Bⁱ⁺¹ ⟶ R^{r+2}F Zⁱ` exact. Its outer
  terms are zero, so the middle term is zero (`ShortComplex.Exact.isZero_X₂`).
- `isZero_rightDerived_cycles_of_boundaries F K hH i j hB r`: if `Bʲ` is `F`-acyclic, then so
  is `Zʲ`. `DerivedPlus.rightDerived_exact₂` applied to `boundariesSc_shortExact K i j` makes
  `R^{r+1}F Bʲ ⟶ R^{r+1}F Zʲ ⟶ R^{r+1}F Hʲ` exact, and its outer terms are zero.
- `isZero_rightDerived_cycles F K hX hH i r`: every `Zⁱ` is `F`-acyclic. The proof is by
  induction on `i`. In degree `0`, `Z⁰ ≅ H⁰` by Mathlib's `CochainComplex.isoHomologyπ₀`, so
  `hH 0` gives the claim through Worker 716's
  `AcyclicComparison.isZero_rightDerived_obj_of_iso`. For the successor step, the two
  previous helpers give `Zⁱ` acyclic, then `Bⁱ⁺¹` acyclic, then `Zⁱ⁺¹` acyclic.

This does not reuse `AcyclicComparison.isZero_rightDerived_cycles` from `ComparisonProof`.
That lemma assumes an exact complex; here the homology need not vanish.

### Homology of the mapped complex (section `Homology`)

Here `F` is additive and preserves finite limits; no derived category is used.

- `nonempty_homology_map_iso F K n hT`: fix `n`, and let `p` be `(ComplexShape.up ℕ).prev n`.
  Suppose that `F` applied to `homologySc K p n`, that is `F Kᵖ ⟶ F Zⁿ ⟶ F Hⁿ`, is exact
  (`hT`), and that `F.map (K.homologyπ n)` is an epimorphism (an instance argument). Then the
  degree-`n` homology of `F K` is isomorphic to `F.obj Hⁿ`. The proof builds an explicit
  `ShortComplex.LeftHomologyData` of the short complex `(F K).sc n` with
  `K := F.obj Zⁿ`, `H := F.obj Hⁿ`, `i := F.map (K.iCycles n)` and
  `π := F.map (K.homologyπ n)`:
  - `i` is a kernel of the mapped differential. Mathlib's `KernelFork.mapIsLimit` transports
    `K.cyclesIsKernel`, because `F` preserves finite limits.
  - The morphism induced by the first differential into this kernel is
    `F.map (K.toCycles p n)`. Both agree after composing with the kernel inclusion, by
    `HomologicalComplex.toCycles_i`.
  - `π` is a cokernel of that morphism. After rewriting the morphism as
    `F.map (K.toCycles p n)`, the short complex is `F Kᵖ ⟶ F Zⁿ ⟶ F Hⁿ`. It is exact by `hT`
    (transported along an identity morphism of short complexes) and `π` is an epimorphism,
    so `ShortComplex.Exact.gIsCokernel` applies.

  `LeftHomologyData.homologyIso` then gives the isomorphism.

### Assembly (section `Comparison`)

- `nonempty_homologyIso F K hX hH n`: the conclusion of the statement, under
  `[EnoughInjectives C]`, chosen derived categories, additivity and preservation of finite
  limits. The proof splits on `n`.
  - `n = 0`: here `(ComplexShape.up ℕ).prev 0 = 0` (`CochainComplex.prev_nat_zero`) and
    `K.toCycles 0 0 = 0`, because `0` is not related to `0` in `ComplexShape.up ℕ`. So
    exactness of `F K⁰ ⟶ F Z⁰ ⟶ F H⁰` is equivalent to `F.map (K.homologyπ 0)` being a
    monomorphism (`ShortComplex.exact_iff_mono`). This map is an isomorphism, because
    `K.homologyπ 0` is one. `nonempty_homology_map_iso` applies. No acyclicity hypothesis is
    needed in this degree.
  - `n = m + 1`: all cycles are acyclic by `isZero_rightDerived_cycles`, and `Bᵐ⁺¹` is
    acyclic by `isZero_rightDerived_boundaries`. Worker 61's
    `DerivedPlus.shortExact_map_of_isZero_rightDerived_one` uses `R¹F Zᵐ = 0` and
    `R¹F Bᵐ⁺¹ = 0`. It shows that `F` keeps `cyclesSc K m (m + 1)` and
    `boundariesSc K m (m + 1)` short exact. The second gives that
    `F.map (K.homologyπ (m + 1))` is an epimorphism. The first gives that
    `F Kᵐ ⟶ F Bᵐ⁺¹` is an epimorphism. A morphism of short complexes goes from
    `F Kᵐ ⟶ F Zᵐ⁺¹ ⟶ F Hᵐ⁺¹` to the exact `F Bᵐ⁺¹ ⟶ F Zᵐ⁺¹ ⟶ F Hᵐ⁺¹`. It is that epimorphism
    on the first term and the identity on the others, and it commutes by
    `ShortComplex.toCycles_i`. `ShortComplex.exact_iff_of_epi_of_isIso_of_mono` transfers
    exactness, and `nonempty_homology_map_iso` applies with
    `CochainComplex.prev_nat_succ`.

## Proof of the theorem

The statement assumes only `[HasInjectiveResolutions C]` and no derived categories. The proof
introduces all the data. It derives `EnoughInjectives C`: each object `X` embeds into the
degree-zero term of its chosen injective resolution `injectiveResolution X` by the
monomorphism `(injectiveResolution X).ι.f 0`. This is the same construction as in
`ComparisonProof`. It chooses derived categories by `HasDerivedCategory.standard C` and
`HasDerivedCategory.standard D`, then applies `AcyclicTermsComparison.nonempty_homologyIso`.
`HasInjectiveResolutions C` is a proposition, so the right derived functors in the hypotheses
agree with those in the helpers. The derived categories serve only the long exact sequence in
the proof and do not occur in the theorem's type.

The development check compiles the module with zero errors and zero warnings. The theorem has
level parameters `u v u' v'` and depends only on the axioms `propext`, `Classical.choice` and
`Quot.sound`.
