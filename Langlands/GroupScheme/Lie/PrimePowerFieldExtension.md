# Prime powers of Lie elements under field extension

Author: Worker 1420.

This internal, derived module compares the restricted prime powers `X ↦ X^[p^r]` of tangent
vectors of an affine group `G` over `k` across coefficient extensions. The Library defines the
prime power `Lie.primePowerKernel H X p r` only for tangent vectors of `H` with coefficients in
its own base ring. A tangent vector of `G` with coefficients in a `k`-algebra `F` is therefore
first moved to an `F`-rational tangent vector of the base change `G_F`. The comparisons below
work through matrix representations. They are inputs of the semisimple-centralizer case
(Case C) of the induction for `MaximalTorusParameterUnirationalStatement`. In that case a
relation among prime powers of a generic Lie element must survive passage to larger fields
and conjugation. No literature statement is formalized here.

Throughout, `G_K` is the base change `(GroupScheme.baseChange (algebraBaseMap k K)).obj G` of
`G` along `k → K`, and `Lie.kernelBaseChangeEquiv k K G A` is the Library's identification of
the tangent vectors of `G_K` with coefficients in a `K`-algebra `A` with those of `G` with
coefficients in `A`.

## Representations and base change

For a commutative ring `k`, a `k`-algebra `K`, a group scheme `G` over `k` and a matrix
representation `ρ` of `G` on `Fin n`, let `ρ_K` be its scalar extension
`ρ.baseChange (algebraBaseMap k K)` to `G_K`.

- `MatrixRepresentation.affineMatrix_baseChange`: for every `K`-algebra `A` (with compatible
  `k`-algebra structure) and every affine `A`-point `x` of `G_K`, the matrix of `ρ_K` at `x`
  equals the matrix of `ρ` at the corresponding `A`-point of `G` (the Library's
  `Lie.affineBaseChangeEquiv`). The proof compares the published point-matrix base-change and
  naturality lemmas and cancels the isomorphism `Γ(Spec A) ≅ A`.
- `MatrixRepresentation.tangentMatrix_baseChange`: likewise for tangent vectors. The tangent
  matrix of `ρ_K` at a tangent vector `X` of `G_K` with coefficients in `A` equals the tangent
  matrix of `ρ` at `Lie.kernelBaseChangeEquiv k K G A X`. The proof applies the previous
  lemma over the dual numbers `A[ε]` and reads off the `ε`-coefficient.

## Monomorphic representations

For a group scheme `G` over any commutative ring `R` and a representation `ρ` of `G`:

- `MatrixRepresentation.tangentMatrix_injective`: if the underlying morphism of `ρ` is a
  monomorphism, then `ρ.tangentMatrix A` is injective for every `R`-algebra `A`. This follows
  from the Library's `lieKernelTarget_injective`.
- `MatrixRepresentation.tangentMatrix_conjugation`: for every affine `A`-point `g` of `G`, the
  tangent matrix of the conjugate `lieKernelConjugation G g X` is `M X M⁻¹`, where `M` is the
  matrix of `ρ` at `g` and `X` stands for its tangent matrix. No monomorphism hypothesis is
  needed.

## Field prime powers

Let `k` be a commutative ring, `F` a `k`-algebra of characteristic `p` (prime), and `G` an
affine group over `k`.

- `fieldPrimePower k F G X p r` (definition): for a tangent vector `X` of `G` with
  coefficients in `F`, take the `F`-rational tangent vector of `G_F` corresponding to `X`, form
  its prime power `Lie.primePowerKernel G_F _ p r`, and transport the result back with
  `Lie.kernelBaseChangeEquiv k F G F`. When `F = k`, this is the restricted `p^r`-th power of
  `X` computed in the base change of `G` along the identity.
- `MatrixRepresentation.tangentMatrix_fieldPrimePower`: every representation `ρ` of `G` sends
  `fieldPrimePower k F G X p r` to the `p^r`-th power of the tangent matrix of `X`. The proof
  combines `tangentMatrix_baseChange` with the Library's `tangentMatrix_primePowerKernel` for
  `ρ_F`.
- `lieKernelMap_fieldPrimePower_of_mono`: given a monomorphic representation of `G`, for every
  `k`-algebra homomorphism `φ : F → F'` into another `k`-algebra of characteristic `p`, the
  coefficient change `lieKernelMap G φ` sends `fieldPrimePower k F G X p r` to
  `fieldPrimePower k F' G (lieKernelMap G φ X) p r`.
- `lieKernelConjugation_fieldPrimePower_of_mono`: given a monomorphic representation, conjugation
  by an affine `F`-point `g` of `G` commutes with `fieldPrimePower k F G · p r`.

The last two are proved by applying the injective tangent matrix map of the monomorphic
representation. Both sides then become `p^r`-th powers of tangent matrices, which commute
with entrywise ring maps and with conjugation by an invertible matrix.

## Over a field

Now let `k` be a field and `G` affine and locally of finite type over `k`.

- `exists_mono_matrixRepresentation`: `G` has a matrix representation whose underlying
  morphism is a monomorphism. It is obtained from the Library's proof
  `affineLinearEmbeddingStatement` of `AffineLinearEmbeddingStatement`: closed immersions are
  monomorphisms.
- `lieKernelMap_fieldPrimePower` and `lieKernelConjugation_fieldPrimePower`: the two
  commutation results above, without a representation hypothesis.

## Prime-power relations

Let `F` be a field that is a `k`-algebra of characteristic `p` (prime), with `k` a commutative
ring and `G` affine over `k`. Tangent vectors with coefficients in `F` form an `F`-vector space
through the Library's `lieKernelModule` (written additively).

- `HasPrimePowerRelation X p m` (definition): there are a finite set `s` of natural numbers and
  coefficients `c : ℕ → F` such that `m ∈ s`, every element of `s` is at least `m`,
  `c m ≠ 0`, and `∑_{i ∈ s} c i • X^[p^i] = 0`, where `X^[p^i]` is
  `fieldPrimePower k F G X p i`.
- `exists_hasPrimePowerRelation`: if `G` is locally of finite type, every `X` has a
  prime-power relation at some `m`. The tangent space is finite-dimensional over `F`, so the
  family `i ↦ X^[p^i]` is linearly dependent; `m` is the least index in the support of a
  nontrivial dependence.
- `HasPrimePowerRelation.isGeometricallySemisimpleMatrix`: under a prime-power relation at `m`,
  every representation of `G` has geometrically semisimple tangent matrix at `X^[p^m]`. The
  relation becomes `∑ c i • M^(p^i) = 0` for the tangent matrix `M` of `X`. The Library's
  `Lie.isGeometricallySemisimpleMatrix_primePower_of_relation` then applies.
- `HasPrimePowerRelation.isSemisimpleElement`: under a prime-power relation at `m`, the
  `F`-rational tangent vector of `G_F` corresponding to `X^[p^m]` is a semisimple element of
  `G_F` in the sense of the Library's `Lie.IsSemisimpleElement`: every representation of `G_F`
  (not only scalar extensions of representations of `G`) has geometrically semisimple tangent
  matrix there. The relation is transported to `G_F` by the linear equivalence
  `Lie.kernelBaseChangeLinearEquiv`, where it is a relation among the prime powers
  `Lie.primePowerKernel G_F _ p i`.
- `HasPrimePowerRelation.map_of_mono` and `HasPrimePowerRelation.conjugation_of_mono`: given a
  monomorphic representation of `G`, a prime-power relation at `m` for `X` gives one at the
  same `m` for `lieKernelMap G φ X`, where `φ : F → F'` is a `k`-algebra homomorphism into a
  field of characteristic `p`, with coefficients `φ ∘ c`. It also gives one for the conjugate
  `lieKernelConjugation G g X` by an affine `F`-point `g`, with the same coefficients.
  `φ (c m) ≠ 0` because field homomorphisms are injective.
- `HasPrimePowerRelation.map` and `HasPrimePowerRelation.conjugation`: the same over a field
  `k` with `G` locally of finite type, without a representation hypothesis.

## Provenance

Derived from the Library's `Lie.primePowerKernel`, `MatrixRepresentation.baseChange`,
`MatrixRepresentation.tangentMatrix_primePowerKernel`, `lieKernelTarget_injective`,
`Lie.kernelBaseChangeEquiv`, `Lie.kernelBaseChangeLinearEquiv`,
`affineLinearEmbeddingStatement` and
`Lie.isGeometricallySemisimpleMatrix_primePower_of_relation`. The relation argument follows
the Library's `semisimplePrimePowerExponent` (in `Lie/PrimePowerCentralizer`), which treats
coefficients in the base field `k`; here it is carried out with coefficients in an extension
field. No literature statement is formalized.
