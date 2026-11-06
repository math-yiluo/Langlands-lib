# Hecke algebras of levels over arbitrary rings

This internal construction defines, for a group `G`, a commutative ring `R`
and subgroups `K L M` of `G`, the spaces `R[G/L]^K` of `K`-invariant
finitely supported functions on `G ⧸ L`, their action on fixed vectors of
representations, the convolution between them, and the Hecke algebra
`R[G/K]^K` of a subgroup `K` acting on `K`-fixed vectors. For compact open
levels it identifies the double-coset operators `[K g L]` of
`Langlands.Shimura.LevelHecke` with the action of explicit elements of
`R[G/L]^K`, so that the composite of two double-coset operators is the
action of a convolution. All declarations are in namespace
`Langlands.Shimura.LevelHecke`.

## Motivation and scope

Hecke operators on the cohomology of the Harris level towers, with
coefficients such as `ℤ/ℓ^n`, are composed and compared through the Hecke
algebra of a level. This module provides that algebra and its module
structure on fixed vectors without dividing by indices and without Haar
measures.

The module does not decompose a product of double-coset elements into a
combination of double-coset elements (no structure constants are computed),
does not prove that the double-coset elements form an `R`-basis of
`R[G/K]^K`, and asserts no commutativity. It makes no comparison with the
complex Haar-measure `HeckeAlgebra μ` and its corners in
`Langlands.Representation.Hecke`. Geometric Hecke correspondences on the
schemes of a tower are separate obligations.

## Permutation modules and Frobenius reciprocity

Let `G : Type v` be a group, `R : Type t` a commutative ring and
`L : Subgroup G`.

- `permRep R L` is the published permutation representation
  `Langlands.Induction.permutation R G (G ⧸ L) R` on `G ⧸ L →₀ R`, in which
  `g` moves the value at `z` to `g • z` (so `(g a)(z) = a(g⁻¹ z)`).
- `HeckeSpace R K L` is the module `fixedVectors (permRep R L) K` of
  `K`-invariant elements of `R[G/L]`.
- `unitElement L : HeckeSpace R L L` is `δ_L`, the function with value `1` at
  the coset `L` and `0` elsewhere (`unitElement_coe`).

Let `ρ : Representation R G V` be any representation on an `R`-module `V`.

- `cosetVector ρ v q`, for `v` fixed by `L` and `q = x L`, is `ρ(x) v`; it is
  independent of the representative (`cosetVector_mk`), equivariant
  (`cosetVector_smul`) and additive and `R`-linear in `v`.
- `frobenius ρ v : (permRep R L).IntertwiningMap ρ` is the intertwining map
  `R[G/L] → V` given by `Finsupp.linearCombination` of `cosetVector ρ v`, so
  it sends `δ_{xL}` to `ρ(x) v` (`frobenius_apply`). It sends `δ_L` to `v`
  (`frobenius_unitElement`), and `frobenius_eval` states that every
  intertwining map `φ` from `R[G/L]` equals the Frobenius map of `φ(δ_L)`.

## Action on fixed vectors

- `heckeAct ρ K L : HeckeSpace R K L →ₗ[R] fixedVectors ρ L →ₗ[R]
  fixedVectors ρ K` sends `(a, v)` to `frobenius ρ v a`, the vector
  `∑_{xL} a(xL) ρ(x) v` (`heckeAct_coe`, and `heckeAct_apply` with the
  representatives `Quotient.out`). It is `K`-fixed because `frobenius ρ v` is
  an intertwining map and `a` is `K`-invariant.
- `heckeAct_unitElement`: `δ_L` acts as the identity on `L`-fixed vectors.
- `heckeAct_permRep_unitElement`: on `R[G/M]`, an element `a` of
  `R[G/M]^K` sends `δ_M` to `a`.
- `fixedVectorsMap_heckeAct`: the action commutes with the maps on fixed
  vectors induced by intertwining maps.
- `heckeAct_heckeAct`: `a • (b • v) = (a • b) • v` for
  `a ∈ R[G/L]^K`, `b ∈ R[G/M]^L` and `v ∈ V^M`, where `a • b` is the action
  of `a` on `b`, viewed as an `L`-fixed vector of `permRep R M`. The proof
  writes `b • v` as the image of `b` under `frobenius ρ v` and uses
  `fixedVectorsMap_heckeAct`.

## Convolution and the Hecke algebra

- `heckeMul R K L M : HeckeSpace R K L →ₗ[R] HeckeSpace R L M →ₗ[R]
  HeckeSpace R K M` is `heckeAct (permRep R M) K L`. `heckeMul_apply` gives
  the convolution formula `(a * b)(z) = ∑_{yL} a(yL) b(y⁻¹ z)`, with
  `y = Quotient.out (yL)`, and `heckeMul_assoc` is its associativity.
- `LevelHeckeAlgebra R K` is a type synonym of `HeckeSpace R K K`, with the
  inherited `AddCommGroup` and `R`-module structures and the identity
  `ofHeckeSpace`. Its `Ring` instance has multiplication `heckeMul R K K K`
  (`mul_def`) and unit `δ_K` (`one_def`); its `Algebra R` instance is
  `Algebra.ofModule` from the bilinearity of `heckeMul`.
- `LevelHeckeAlgebra.instModuleFixedVectors`: for every representation `ρ`,
  `fixedVectors ρ K` is a left module over `LevelHeckeAlgebra R K` with
  `a • v = heckeAct ρ K K a v` (`smul_def`); `mul_smul` is
  `heckeAct_heckeAct`. The instance `IsScalarTower R (LevelHeckeAlgebra R K)
  (fixedVectors ρ K)` records compatibility with the `R`-module structure.

## Double-coset elements of compact open levels

Let now `G` be a topological group and `K L M : CompactOpenLevel G`, with
the published finite coset types `HeckeCosets K L g = K / (K ∩ g L g⁻¹)` of
`Langlands.Shimura.LevelHecke`.

- `cosetPoint K L g` sends the coset of `k` to `k g L ∈ G ⧸ L`.
  `cosetPoint_injective` states that it is injective, and
  `mem_range_cosetPoint` that its range is the `K`-orbit of `g L` in `G ⧸ L`,
  that is, the image of the double coset `K g L`.
- `heckeElement R K L g : HeckeSpace R K L` is `[K g L] δ_L`, the published
  double-coset operator of `permRep R L` applied to `δ_L`.
  `heckeElement_coe` writes it as `∑_q δ_{cosetPoint q}`, and
  `heckeElement_apply` states that it is the indicator function of the
  `K`-orbit of `g L`.
- `heckeAct_heckeElement`: the action of `heckeElement R K L g` on `V^L` is
  the published `heckeOperator ρ K L g`. The proof applies the published
  `fixedVectorsMap_heckeOperator` to `frobenius ρ v` and evaluates at `δ_L`.
- `heckeOperator_comp_heckeOperator`: for `g h : G`,
  `[K g L] ∘ [L h M]` is the action of the convolution
  `heckeMul R K L M (heckeElement R K L g) (heckeElement R L M h)`.
- `doubleCoset K g : LevelHeckeAlgebra R K` is `heckeElement R K K g`.
  `doubleCoset_smul` states that it acts on `K`-fixed vectors as
  `heckeOperator ρ K K g`, `doubleCoset_one` that `doubleCoset K 1 = 1`, and
  `heckeOperator_comp_heckeOperator_self` that
  `[K g K] ∘ [K h K]` is the action of `doubleCoset K g * doubleCoset K h`.

## Smooth representations

For a topological group `G` and `K : Subgroup G`,
`heckeModuleFunctor R K : SmoothRep R G ⥤ ModuleCat (LevelHeckeAlgebra R K)`
sends a smooth representation to its `K`-fixed vectors with the module
structure above (`heckeModuleFunctor_obj`) and an intertwining map to its
restriction `fixedVectorsMap`, which is linear over the Hecke algebra by
`fixedVectorsMap_heckeAct`.

## Provenance

This is an internal construction from Mathlib's `Finsupp.linearCombination`,
`Finsupp.lhom_ext`, `Finsupp.apply_linearCombination`,
`Representation.IntertwiningMap`, `Algebra.ofModule`, `ModuleCat.ofHom` and
`QuotientGroup.induction_on`, together with the published
`Langlands.Induction.permutation`, `permutation_single`, `permutation_apply`,
`fixedVectors`, `fixedVectorsMap`, `SmoothRep` and `CompactOpenLevel`, and
the operators `heckeOperator`, `heckeOperator_apply`,
`heckeOperator_self`, `fixedVectorsMap_heckeOperator`, `HeckeCosets` and
`mem_heckeLevel` of `Langlands.Shimura.LevelHecke`. No algebra law,
module law or identification with double-coset operators is supplied as
input. The description of the Hecke algebra of `K` as `K`-invariants of
`R[G/K]` acting on `K`-fixed vectors through Frobenius reciprocity is the
standard one for Hecke algebras of pairs `(G, K)`, here for unnormalized
coset sums over an arbitrary commutative ring.
