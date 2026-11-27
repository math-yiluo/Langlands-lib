# Existence of the parabolic projection of an enveloping centre

Module `Langlands.Algebra.ParabolicCenterProjectionExistence`, namespace
`Langlands.Algebra.ParabolicCenterProjection`.

`exists_centerProjection` takes a finite-dimensional complex Lie algebra `g`, a complex Lie
algebra `m`, a Lie algebra map `j : m →ₗ⁅ℂ⁆ g` and `H : g` such that

- the eigenvectors of `ad H` with integer eigenvalues span `g`,
- `j` is injective, and its range is the centralizer `{X | ⁅H, X⁆ = 0}`.

It produces a complex algebra map `p` from the centre of `U(g)` to the centre of `U(m)`
such that, for every central `z`, `z - U(j)(p z)` lies in
`positiveRightIdeal H` (module `Langlands.Algebra.ParabolicCenterProjectionFiniteStatement`),
the right ideal spanned by the products `ι(Y) u` with `Y` an eigenvector of `ad H` for a
positive integer eigenvalue. No reductivity is needed for existence.

## Proof

1. Mathlib's `exists_linearIndependent` extracts from the spanning set of integral
   eigenvectors a linearly independent spanning subset `t`, finite because `g` is
   finite-dimensional. It gives a basis `b` of `g` indexed by `t`, and a choice of the
   integer eigenvalue `d a` of each basis vector. The gradings `(d a : ℝ)` and eigenvalues
   `(d a : ℂ)` are related by the real part (`Complex.reAddGroupHom`), as required by
   `Langlands.Algebra.LieWeightCenterProjection`.
2. For a basis vector of grading zero, the hypothesis on the range of `j` gives a preimage
   in `m`. These preimages are linearly independent because `j` is injective. They span
   `m`: for `x ∈ m`, `j x` is an eigenvector of eigenvalue `0`, so `mem_eigenSpan_of_ad`
   puts it in the span of the basis vectors of eigenvalue `0`, which is the image under `j`
   of the span of the preimages; injectivity of `j` brings `x` back. This is a basis `b₀`
   of `m` with `j (b₀ a) = b a`.
3. The positive basis vectors span the Lie subalgebra `positiveWeightLieSubalgebra` with
   its restricted basis. `relativeEnvelopingDecomposition_of_weight` then gives a
   `Langlands.Algebra.RelativeEnvelopingDecomposition` for `U(j)`, and `p` is its
   `centerProjection`.
4. Its congruence holds modulo `positiveWeightRightIdeal b d`. Each generator `ι(b a) v`
   of that ideal with `d a > 0` is a generator of `positiveRightIdeal H`, because `b a` is
   an eigenvector with eigenvalue `d a = (d a - 1).toNat + 1`. Hence the congruence holds
   modulo `positiveRightIdeal H`.

## Provenance

Harish-Chandra, *Two theorems on semi-simple Lie groups*, Ann. of Math. 83 (1966), Lemma 13
and Corollary, printed pp. 95–96 (PDF pp. 22–23), registered as
`provided-3315156dfd5120bb69df4005d1cb66c074532e8f8ab3cd2459c5990658370e91`, constructs the
projection modulo the left ideal `𝔊n` for the split component of a parabolic of a real
semisimple group. The right ideal `n U(g)` used here is its transport by the principal
antiautomorphism of `U(g)`. Here a single element with integral eigenvalues plays the role of
the split component, for an arbitrary finite-dimensional complex Lie algebra. The finiteness of
`p` for reductive `g` is `ParabolicCenterProjectionFiniteStatement`, proved in
`Langlands.Algebra.ParabolicCenterProjectionFiniteProof`.
