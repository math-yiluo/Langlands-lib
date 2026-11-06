# Dominance of adjoint slice maps

Author: Worker 1630.

This derived helper module proves that the adjoint slice map
`G × 𝔸^e → 𝔤`, `(g, t) ↦ Ad(g) (B t)`, has dense range when the slice `B`
together with the image of `ad(Y₀)` spans `𝔤`. Here `Y₀ = B t₀` is a rational
point of the slice and `G` is a smooth affine group over a field. This is the
standard tangent-space argument for dominance of a conjugation map. The
project's route to unirationality of the scheme of maximal tori (SGA 3,
Exposé XIV) uses it. The proof is written out here from the Library's
dual-number Lie algebra, matrix representations, coefficient spaces and the
published tangent-space smoothness criterion `TangentSmoothness`. No external
theorem is asserted.

All declarations live in the namespace `Langlands.GroupScheme.Lie`. The Lie
algebra is the Library's dual-number kernel `lieKernel G A`. Finite Lie
coordinates `c : FiniteCoordinates G d` identify it with `Fin d → A`, and
`adjointDifferentialFamily c Y` is the coordinate matrix of `ad(Y)`, defined
in the Library as the tangent matrix of `adjointRepresentation c`.

## The adjoint differential is a commutator

Throughout this section `R` is a commutative ring, `G` is a group scheme over
`Spec R` with affine structure morphism, `A` is an `R`-algebra and `ρ` is a
matrix representation of `G` on `n`.

- `kernelDifferential_injective`: if `ρ` is a monomorphism of group schemes,
  its tangent-matrix differential `ρ.kernelDifferential A` is injective.
- `equiv_lieKernelMapLinear_ofId`: the coordinates of the constant
  dual-number lift of a tangent vector are the constant lifts of its
  coordinates.
- `equiv_adjoint_constant` and `adjoint_constant_eq`: for tangent vectors `X`
  and `Y` over `R`, the adjoint action of the first-order point of `Y` on the
  constant lift of `X` is `X + ε ad(Y) X`. The proof uses the Library
  identity `adjointRepresentation_affineAction` and the formula
  `affineMatrix_lieKernel` for the matrix of a dual-number tangent point.
- `tangentMatrix_conjugation_constant` and `tangentMatrix_adjoint_constant`:
  the tangent matrix of that adjoint image is
  `ρ(X) + ε (ρ(Y) ρ(X) - ρ(X) ρ(Y))`. The proof pushes the conjugation
  through `ρ` with the Library lemma `targetMap_conjugation` and applies the
  Library's `GL_n` computation `generalLinear_conjugation_constant` (module
  `Reductive.CharZeroSemisimplicity.LieImage`): conjugating the constant lift
  of `N` by the first-order point `1 + εM` gives `N + ε (MN - NM)`.
- `kernelDifferential_lieKernelMapLinear_ofId`: the tangent-matrix
  differential commutes with the constant inclusion into dual numbers.
- `kernelDifferential_adjointDifferentialFamily`: for every matrix
  representation `ρ`, the tangent matrix of `ad(Y) X` is the commutator
  `ρ(Y) ρ(X) - ρ(X) ρ(Y)`. Proof: compare epsilon coefficients in the two
  formulas above.
- `adjointDifferentialFamily_antisymm_of_injective` and
  `adjointDifferentialFamily_self_of_injective`: if some matrix
  representation has injective tangent-matrix differential, then
  `ad(Y) X = -ad(X) Y` and `ad(X) X = 0`, since commutators have these
  properties.

## Over a field

Here `k` is a field and `G` is a group scheme over `Spec k` with affine
structure morphism, locally of finite type.

- `exists_injective_kernelDifferential`: `G` has a matrix representation with
  injective tangent-matrix differential. Proof: the published
  `affineLinearEmbeddingStatement` gives a closed immersion into some `GL_N`,
  which is a monomorphism.
- `adjointDifferentialFamily_antisymm` and `adjointDifferentialFamily_self`:
  `ad(Y) X = -ad(X) Y` and `ad(X) X = 0` for all `X`, `Y` in `lieKernel G k`.
- `adjointRepresentation_tangentMatrix_mulVec`: the adjoint tangent matrix of
  `ξ` sends the coordinate vector `v` to `-ad(Y) ξ`, where `Y` is the Lie
  element with coordinates `v`.

## The slice map

Here `R` is a commutative ring, `n` and `e` are finite types, and
`coefficientSpace n R` is the Library's affine coordinate space `𝔸^n` over
`Spec R` as an object over `Spec R`.

- `linearPoint B` (definition): for a matrix `B : Matrix n e R`, the linear
  morphism `𝔸^e ⟶ 𝔸^n` whose coordinates are `B` times the coordinates of
  the identity. `coefficientCoordinates_linearPoint` shows that on every test
  scheme it is multiplication by `B`.
- `sliceMap ρ B` (definition): the morphism `G × 𝔸^e ⟶ 𝔸^n` over `Spec R`
  given by `(g, t) ↦ ρ(g) (B t)`. It is the pair `(g, B t)` followed by the
  Library action morphism `ρ.coefficientActionHom`.
  `coefficientCoordinates_sliceMap` gives this formula on every test scheme,
  and `affineCoordinates_sliceMap` gives it on an affine test scheme `Spec S`
  in the coordinates of `S`.
- Supporting lemmas: `ΓSpecIso_hom_scalarMap` identifies base scalars on
  `Spec S` with their images in `S`; `affineMatrix_lieKernel_eq` says that the
  matrix of a dual-number tangent point `X` is `1 + ε ρ(X)`.

## Tangent surjectivity and dominance

Here `k` is a field, `G` is a group scheme over `Spec k`, and
`slicePoint t₀` (definition) is the rational point `(1, t₀)` of
`G × 𝔸^e`.

- `isTangentSurjectiveAt_sliceMap`: let `G` have affine structure morphism.
  Assume every vector `v : n → k` can be written as `ρ(ξ) (B t₀) + B t'` for
  a Lie element `ξ` and a vector `t'`. Then the slice map satisfies the
  published predicate `IsTangentSurjectiveAt` at `(1, t₀)`: every
  `k[ε]`-tangent vector of `𝔸^n` at the image point is the image of a tangent
  vector of `G × 𝔸^e` at `(1, t₀)`. Proof: write the tangent vector of `𝔸^n`
  as `B t₀ + ε v`. Choose `ξ` and `t'` for `v`. The tangent vector
  `(1 + εξ, t₀ + εt')` maps to `(1 + ερ(ξ)) B (t₀ + εt') = B t₀ + ε (ρ(ξ) B t₀ + B t')`.
- `denseRange_sliceMap`: if moreover `G` is smooth, the slice map has dense
  range. Proof: `G × 𝔸^e` is smooth over `k` by the Library's
  `smooth_tensor`, `𝔸^n` is irreducible and of finite type, and the published
  `denseRange_of_isTangentSurjectiveAt` applies.
- `range_sup_eq_top_of_ker_le`: for a linear endomorphism `f` of a
  finite-dimensional vector space whose kernel meets its image only in `0`,
  the image of `f` and any subspace containing the kernel span the space.
  Proof: rank–nullity makes the image and the kernel complementary.

Main results. Let `G` be smooth over `k` with affine structure morphism, `c`
finite Lie coordinates, `B : Matrix (Fin d) e k`, `t₀ : e → k`, and let
`Y₀` be the Lie element with coordinates `B t₀`.

- `denseRange_adjointSliceMap`: if the image of `ad(Y₀)` and the column space
  of `B` together span `k^d`, then the adjoint slice map
  `sliceMap (adjointRepresentation c) B` has dense range. Proof: given `v`,
  write `v = ad(Y₀) u + B t'` and take `ξ` with coordinates `-u`. By
  antisymmetry, `ρ(ξ) (B t₀) = -ad(Y₀) ξ = ad(Y₀) u`, so the hypothesis of
  `denseRange_sliceMap` holds.
- `denseRange_adjointSliceMap_of_ker_le`: the same conclusion if the column
  space of `B` contains the kernel of `ad(Y₀)` and that kernel meets the image
  of `ad(Y₀)` only in `0`.

No hypothesis is placed on the field `k`. Irreducibility of `G` is not
assumed. The module proves dominance only; it does not prove unirationality
of any scheme.
