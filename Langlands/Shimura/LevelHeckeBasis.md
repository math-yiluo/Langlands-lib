# Double-coset bases, structure constants and degrees of level Hecke algebras

This internal construction supplements `Langlands.Shimura.LevelHeckeAlgebra`.
For compact open levels `K L M` of a topological group `G` and a commutative
ring `R`, it shows that the elements `[K g L] δ_L` form an `R`-basis of
`R[G/L]^K` indexed by the double cosets `K \ G / L`. It computes the
coordinates of a convolution `[K g L] δ_L * [L h M] δ_M` in this basis as
integer structure constants, and it defines the degree character of the Hecke
algebra. All declarations are in namespace `Langlands.Shimura.LevelHecke`.

## Motivation and scope

Hecke operators on the cohomology of the Harris level towers, with
coefficients such as `ℤ/ℓ^n`, are computed through their action on a basis of
the Hecke algebra of a level. This module gives that basis for unnormalized
coset sums over an arbitrary commutative ring, without Haar measures.

The module proves no commutativity of the Hecke algebra and no formula for
structure constants beyond their definition as a number of cosets. It makes no
comparison with the complex Haar-measure Hecke algebras of
`Langlands.Representation.Hecke`. Geometric Hecke correspondences on the
schemes of a tower are separate obligations.

## Invariant functions on a set with finite orbits

Let `G` be a group acting on a type `X`, `R` a commutative ring and
`K : Subgroup G`. The `K`-invariant elements of `X →₀ R` are the published
`fixedVectors (permutation R G X R) K`.

- `apply_smul_of_mem_fixedVectors` and `apply_eq_of_mem_orbit`: a
  `K`-invariant function is constant on `K`-orbits.
- `mem_orbit_out_of_mk_eq` and `out_mk_mem_orbit`: a point lies in the orbit
  of the chosen representative `Quotient.out` of its orbit.

Assume `hK : ∀ y, (MulAction.orbit K y).Finite`.

- `orbitIndicator R K hK O : X →₀ R` is the indicator function `1_O` of the
  orbit `O` (`orbitIndicator_apply`). It is finitely supported because `O` is
  finite, and `K`-invariant (`orbitIndicator_mem`).
- `orbitCoordinates R K` is the `R`-linear map sending an invariant function
  `f` to the finitely supported function `O ↦ f(Quotient.out O)` on the orbits
  (`orbitCoordinates_apply`); it needs no finiteness hypothesis.
- `orbitSum R K hK` is the `R`-linear map `c ↦ ∑_O c(O) 1_O`, built with
  `Finsupp.linearCombination`. `orbitSum_apply` states that its value at `y`
  is `c` evaluated at the orbit of `y`.
- `orbitEquiv R K hK` is the linear equivalence between the invariant
  functions and the finitely supported functions on
  `MulAction.orbitRel.Quotient K X`, with forward map `orbitCoordinates` and
  inverse `orbitSum`.
- `orbitBasis R K hK` is the basis `Module.Basis.ofRepr (orbitEquiv R K hK)`.
  `orbitBasis_coe` states that its vector at `O` is `1_O`, and
  `orbitBasis_repr_apply` that the coordinate at `O` is the value at
  `Quotient.out O`.

## Orbits on cosets and double cosets

For subgroups `K L` of a group `G`:

- `mk_mem_orbit_iff`: the coset `z L` lies in the `K`-orbit of `h L` exactly
  when `z ∈ K h L`, the Mathlib set `DoubleCoset.doubleCoset h K L`.
- `orbitDoubleCosetEquiv K L` is the equivalence between the `K`-orbits on
  `G ⧸ L` and the Mathlib quotient `DoubleCoset.Quotient K L`, sending the
  orbit of `g L` to `DoubleCoset.mk K L g` (`orbitDoubleCosetEquiv_mk`,
  `orbitDoubleCosetEquiv_symm_mk`).
- `inv_mul_mem_doubleCoset_mul_right`: for `l ∈ L`, the condition
  `(y l)⁻¹ x ∈ L h M` is equivalent to `y⁻¹ x ∈ L h M`, so it depends only on
  the coset `y L`.

## The double-coset basis

Let now `G` be a topological group and `K L M : CompactOpenLevel G`, with the
published `HeckeSpace`, `heckeElement`, `cosetPoint` and `heckeMul` of
`Langlands.Shimura.LevelHeckeAlgebra` and the finite coset types
`HeckeCosets K L g = K / (K ∩ g L g⁻¹)` of `Langlands.Shimura.LevelHecke`.

- `finite_orbit`: every `K`-orbit on `G ⧸ L` is finite, since the orbit of
  `g L` is the range of `cosetPoint K L g` (published
  `mem_range_cosetPoint`).
- `heckeBasis R K L` is the basis of `R[G/L]^K` indexed by
  `DoubleCoset.Quotient K L`, obtained by reindexing `orbitBasis` along
  `orbitDoubleCosetEquiv`. `heckeBasis_mk` states that its vector at
  `K g L` is `heckeElement R K L g`, that is `[K g L] δ_L`, and
  `heckeBasis_repr_mk` that the coordinate of `a` at `K g L` is the value
  `a(g L)`.
- `heckeElement_eq_of_mk_eq`: `[K g L] δ_L` depends only on the double coset
  `K g L`. `heckeElement_eq_iff`: over a nontrivial ring, `[K g L] δ_L =
  [K g' L] δ_L` exactly when `K g L = K g' L`.
- `range_heckeElement` and `span_heckeElement`: the elements `[K g L] δ_L`
  are exactly the basis vectors and span `R[G/L]^K`. The instance
  `Module.Free R (HeckeSpace R K L)` follows.

## Structure constants

- `heckeStructureConstant K L M g h x : ℕ` is the number of cosets
  `q ∈ HeckeCosets K L g` such that `(k g)⁻¹ x ∈ L h M`, where `k` is the
  chosen representative `Quotient.out q`. The elements `k g` run over
  representatives of the cosets `y L` contained in `K g L`, and by
  `inv_mul_mem_doubleCoset_mul_right` the condition depends only on `y L`.
- `heckeMul_heckeElement_apply`: the convolution
  `[K g L] δ_L * [L h M] δ_M` takes the value
  `heckeStructureConstant K L M g h x` at `x M`. The proof expands the
  convolution through the published `heckeAct_coe`, `frobenius_apply` and
  `heckeElement_coe`, and evaluates the indicator function with
  `mk_mem_orbit_iff`.
- `heckeBasis_repr_heckeMul`: the coordinate of this convolution at `K x M`
  is `heckeStructureConstant K L M g h x`.
- `heckeMul_heckeElement`: the convolution equals the finite sum
  `∑_q c(g, h; x_q) [K x_q M] δ_M` over the double cosets `q` in the support
  of its coordinates, with `x_q = Quotient.out q`.

## The Hecke algebra of a level

- `heckeAlgebraBasis R K` is the basis of `LevelHeckeAlgebra R K` indexed by
  `K \ G / K`, the image of `heckeBasis R K K` under `ofHeckeSpace`.
  `heckeAlgebraBasis_mk` states that its vector at `K g K` is the published
  `doubleCoset K g`.
- `doubleCoset_eq_of_mk_eq`, `doubleCoset_eq_iff` (over a nontrivial ring)
  and `span_doubleCoset` are the corresponding statements for the elements
  `[K g K]` of the Hecke algebra.
- `doubleCoset_mul_doubleCoset`: `[K g K] * [K h K]` is the sum of
  `heckeStructureConstant K K K g h x_q • [K x_q K]` over the double cosets
  `q` in the support of the product.

## Degrees

For a group `G` and subgroups `K L M` (no topology is needed):

- `heckeDegree R K L : HeckeSpace R K L →ₗ[R] R` is
  `deg a = ∑_{y L} a(y L)` (`heckeDegree_apply`).
- `heckeAct_trivial`: on the `L`-fixed vectors of the trivial representation
  of `G` on `R`, an element `a` of `R[G/L]^K` acts by multiplication by
  `deg a`.
- `heckeDegree_heckeMul`: `deg (a * b) = deg a * deg b` for
  `a ∈ R[G/L]^K` and `b ∈ R[G/M]^L`. The proof applies the published
  associativity `heckeAct_heckeAct` to the trivial representation and the
  fixed vector `1`.
- `heckeDegree_unitElement`: `deg δ_L = 1`.
- `heckeDegree_heckeElement`: for compact open levels, the degree of
  `[K g L] δ_L` is the cardinality of `HeckeCosets K L g`, that is the index
  `[K : K ∩ g L g⁻¹]`.
- `LevelHeckeAlgebra.degreeHom R K : LevelHeckeAlgebra R K →ₐ[R] R` is the
  degree as an `R`-algebra homomorphism (`degreeHom_apply`), built with
  `AlgHom.ofLinearMap` from `heckeDegree_unitElement` and
  `heckeDegree_heckeMul`. `LevelHeckeAlgebra.smul_trivial` states that the
  Hecke algebra acts on the `K`-fixed vectors of the trivial representation
  through `degreeHom`, and `LevelHeckeAlgebra.degreeHom_doubleCoset` that
  `deg [K g K]` is the cardinality of `HeckeCosets K K g`.

## Provenance

This is an internal construction from Mathlib's `Finsupp.onFinset`,
`Finsupp.linearCombination`, `Module.Basis.ofRepr`, `Module.Basis.reindex`,
`Module.Basis.map`, `Module.Free.of_basis`, `MulAction.orbitRel`,
`DoubleCoset.doubleCoset`, `DoubleCoset.Quotient`, `DoubleCoset.mk`,
`Representation.trivial` and `AlgHom.ofLinearMap`, together with the
published `Langlands.Induction.permutation`, `permutation_apply`,
`fixedVectors`, `CompactOpenLevel`, `HeckeCosets`, and `HeckeSpace`,
`unitElement`, `cosetVector`, `frobenius`, `heckeAct`, `heckeAct_heckeAct`,
`heckeMul`, `LevelHeckeAlgebra`, `cosetPoint`, `mem_range_cosetPoint`,
`heckeElement` and `doubleCoset` of `Langlands.Shimura.LevelHeckeAlgebra`.
No basis, structure constant or multiplicativity statement is supplied as
input. The double-coset basis, the structure constants as numbers of cosets
and the degree (index) character are the standard ones for Hecke algebras of
pairs `(G, K)` with `K` compact open, here for unnormalized coset sums over an
arbitrary commutative ring.
