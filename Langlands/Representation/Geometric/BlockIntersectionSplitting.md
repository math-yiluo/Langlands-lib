# Continuous Levi-first coordinates for a block intersection

This module constructs canonical Levi-first coordinates on the intersection of
a subgroup with an actual standard block parabolic of `GeneralLinear n R`, and
proves that they form a homeomorphism for the induced subgroup topologies. It
is an internal construction from the published block groups, their split
diagonal-block projection and the published literal decomposability predicate.

## Scope and hypotheses

Throughout, `R : Type uR` is any commutative ring in an arbitrary universe,
`n` is any natural number (including `n = 0`), `B : GeneralLinear.BlockShape n`
is any block shape, and `H` is any subgroup of `GeneralLinear n R`. Write
`P = B.parabolic R` for the upper block triangular parabolic,
`M = B.leviSubgroup R` for the actual block diagonal subgroup (the range of
`B.leviEmbedding R`), and `U = B.unipotentSubgroup R` for the block unipotent
radical included as a subgroup of `GeneralLinear n R`. All of these are the
published definitions of `Langlands.Group.GL.Blocks`.

The constructions assume exactly the existing literal predicate

`hd : General.IsDecomposable H (B.leviSubgroup R) (B.unipotentSubgroup R)`

from `Langlands.Representation.Geometric.GeneralIntersections`. It is the set
equality `H ∩ (M U) = (H ∩ M)(H ∩ U)` of pointwise subset products in
`GeneralLinear n R`; its elementwise form `General.isDecomposable_iff` is used.
The algebraic constructions need only `CommRing R`. The topological ones add
only `TopologicalSpace R` and `IsTopologicalRing R`. No field, nontriviality,
Hausdorff, local compactness, closedness of `H`, permutation, refinement or
continuous-decomposition hypothesis is assumed. The two lemmas about the whole
parabolic below do not use `H` or `hd`.

## Declarations

All declarations are in the namespace `Langlands.Geometric`.

For an element `x` of `H ⊓ P`, `xP` denotes the same matrix viewed in
`B.parabolic R`, namely `⟨x.val, x.property.2⟩`, and

`m(x) = B.leviEmbedding R (B.leviProjection R xP)`.

Whole-parabolic lemmas:

- `blockParabolic_mem_levi_mul_unipotent`: for every `g : B.parabolic R`, the
  matrix `g.val` lies in the set product `(M : Set _) * (U : Set _)`. The proof
  uses the Levi-first factors `B.leviEmbedding R (B.leviProjection R g)` and
  `(B.leviInParabolic R (B.leviProjection R g))⁻¹ * g`. The second lies in the
  published `B.unipotentRadical R`, the kernel of `B.leviProjection R`, because
  `B.leviProjection R` is a homomorphism and `B.leviProjection_section` gives
  `B.leviProjection R (B.leviInParabolic R m) = m`.
- `blockParabolic_levi_factor_unique`: if `m ∈ M`, `u ∈ U` and `m * u = g.val`
  for `g : B.parabolic R`, then
  `B.leviEmbedding R (B.leviProjection R g) = m`. The proof writes `m` as an
  embedded Levi element and `u` as the image of a radical element, then applies
  the homomorphism `B.leviProjection R`: it is the identity on
  `B.leviInParabolic R` by the section law and sends the radical to `1`.

Constructions on the intersection (using `hd`):

- `blockIntersection_leviProjection_mem`: `m(x) ∈ H` for every `x : H ⊓ P`.
  The elementwise form of `hd`, applied to `x` and the membership given by
  `blockParabolic_mem_levi_mul_unipotent`, yields some factorization
  `x = m' * u'` with `m' ∈ H ⊓ M` and `u' ∈ H ⊓ U`.
  `blockParabolic_levi_factor_unique` identifies `m'` with `m(x)`. Thus the
  witnesses supplied by `hd` are used only inside this proposition; they never
  replace the specified projection in a definition.
- `blockIntersectionLeviPart x : H ⊓ M` has value `m(x)`, with the membership
  in `H` above and the membership in `M` witnessed by
  `B.leviProjection R xP`.
- `blockIntersectionUnipotentPart x : H ⊓ U` has value `m(x)⁻¹ * x.val`. It lies
  in `H` by subgroup closure and in `U` as the image of the radical element
  `(B.leviInParabolic R (B.leviProjection R xP))⁻¹ * xP`, by the same kernel
  calculation.
- `blockIntersectionLeviPart_val` and `blockIntersectionUnipotentPart_val`
  (simp lemmas, proved by `rfl`) state these two value formulas.
- `blockIntersectionDecomposition : (H ⊓ P) ≃ (H ⊓ M) × (H ⊓ U)` is the
  equivalence with forward map
  `x ↦ (blockIntersectionLeviPart x, blockIntersectionUnipotentPart x)`, that
  is `x ↦ (m(x), m(x)⁻¹ * x)`, and inverse map `(m, u) ↦ m * u`. The product
  lies in `H` by subgroup closure and in `P` because `M` and `U` are contained
  in `P` (`B.leviAsParabolic R` and `B.mem_unipotentSubgroup_iff`). The left
  inverse law is the cancellation `m(x) * (m(x)⁻¹ * x) = x`. The right inverse
  law applies `blockParabolic_levi_factor_unique` to `m * u`, which gives
  `m(m * u) = m`, and then cancels: `m⁻¹ * (m * u) = u`.
- `blockIntersectionDecomposition_eq_factors`: if `m : H ⊓ M`, `u : H ⊓ U` and
  `m.val * u.val = x.val`, then `blockIntersectionDecomposition x = (m, u)`.
  This is the uniqueness of the factors, proved by injectivity of the inverse
  map.

Topological constructions (adding `[TopologicalSpace R] [IsTopologicalRing R]`):

- `continuous_blockIntersectionLeviPart`: the Levi coordinate is continuous. It
  is the composition of the subtype inclusion `H ⊓ P → P`, the published
  continuous projection `B.leviProjectionContinuous R` and the published
  continuous embedding `B.leviEmbeddingContinuous R`, corestricted to the
  subgroup `H ⊓ M`.
- `continuous_blockIntersectionUnipotentPart`: the radical coordinate is
  continuous, by continuity of inversion and multiplication in
  `GeneralLinear n R` applied to the Levi coordinate and the inclusion of `x`.
- `blockIntersectionDecompositionHomeomorph :
  (H ⊓ B.parabolic R) ≃ₜ (H ⊓ B.leviSubgroup R) × (H ⊓ B.unipotentSubgroup R)`
  has underlying equivalence `blockIntersectionDecomposition`. Its forward
  continuity is the pair of the two coordinate continuity results. Its inverse
  is continuous because `mu ↦ mu.1.val * mu.2.val` is the product, under
  continuous multiplication in `GeneralLinear n R`, of the two subtype
  inclusions composed with the two projections of the product space.
- `blockIntersectionDecompositionHomeomorph_fst_val`,
  `blockIntersectionDecompositionHomeomorph_snd_val` and
  `blockIntersectionDecompositionHomeomorph_symm_val` (simp lemmas, proved by
  `rfl`) state the value formulas `m(x)`, `m(x)⁻¹ * x.val` and
  `mu.1.val * mu.2.val`.
- `blockIntersectionDecompositionHomeomorph_toEquiv` (by `rfl`) states that
  the underlying equivalence is `blockIntersectionDecomposition`, and
  `blockIntersectionDecompositionHomeomorph_eq_factors` is the uniqueness
  statement above for the homeomorphism.

All three subgroup types carry the subspace topology induced from the actual
matrix group `GeneralLinear n R`, and the target carries the product topology.
The result is a homeomorphism of topological spaces. No group structure on the
product and no direct-product group law is asserted; in general `H ⊓ M` does not
commute with `H ⊓ U`.

## Factor order

The factor order is Levi first: the inverse map is `(m, u) ↦ m * u` and the
radical coordinate is `m(x)⁻¹ * x`. The published whole-parabolic
`Langlands.GeneralLinear.BlockShape.decompositionHomeomorph` instead has type
`B.parabolic R ≃ₜ B.unipotentRadical R × B.Levi R`, uses the radical-first
order `g = u * m`, and has radical coordinate
`g * (B.leviInParabolic R (B.leviProjection R g))⁻¹`. Both use the same Levi
projection, but the radical coordinates `m⁻¹ * g` and `g * m⁻¹` differ by
conjugation by `m`. Hence swapping the coordinates of that homeomorphism would
give the inverse `(m, u) ↦ u * m`, not the `m * u` map constructed here. That
homeomorphism also concerns the whole parabolic with the abstract Levi product
`B.Levi R`, not intersections with `H`.

## Provenance

Bernstein and Zelevinsky (1977), section 5.1, printed page 460 (PDF page 21),
call a subgroup `H` decomposable with respect to `(M, U)` if
`H ∩ (MU) = (H ∩ M).(H ∩ U)`, and condition 5.1(4) imposes this on six
subgroups. The source does not state the canonical arbitrary-ring coordinates, their
uniqueness, or the homeomorphism constructed here. These are internal
derivations from the published projection and the literal predicate, using
only the section law, the radical kernel, subgroup closure, group cancellation,
and continuity of the published Levi maps and of the group operations.
Literature ID: `bernstein-zelevinsky-1977-induced-i`, SHA-256
`8424600228ab72c5937e45edceefcae410a2a0b8f5ebf282185691542aa89092`;
printed pages 459–462 (sections 5.1–5.6 and the start of 5.7, PDF pages
20–23) were read.

The imported modules `Langlands.Group.GL.Blocks` and
`Langlands.Representation.Geometric.GeneralIntersections` and their Markdown
are unchanged.

## Remaining obligations

In concrete applications `hd` must be supplied by the separate block
six-decomposition result; this module does not prove it for any `H`. Using
this construction adds no hypothesis to any later normalized Jacquet
comparison. The module constructs no orbit integral or quotient measure, proves
no compact induction in stages, Haar scaling or character cancellation, and
identifies no representation functors.

Authors: Worker 76 (construction draft), Worker 1091 (homeomorphism-level
uniqueness lemmas, documentation and submission).
