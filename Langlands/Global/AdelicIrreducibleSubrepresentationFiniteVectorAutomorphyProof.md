# Automorphy of the finite vectors in an irreducible subrepresentation of `L²([G])`

`Langlands.Global.irreducibleSubrepresentationFiniteVectorAutomorphy` proves
`Langlands.Global.IrreducibleSubrepresentationFiniteVectorAutomorphyStatement`. For an
irreducible closed invariant subspace of the canonical `L²([G])`, every vector with
finite-dimensional `K_∞`-orbit span and an open finite stabilizer has an automorphic
representative. The function on `G(𝔸)` is left invariant under both `G(F)` and the
canonical positive split centre `A_G`. Its evaluation on representatives of `[G]`
agrees with the prescribed vector almost everywhere for the canonical quotient measure.

## Smoothness convention

The forms in the conclusion are those of `IsAutomorphicFunctionOn`. The representative
is continuous, smooth on every archimedean slice and locally constant in the finite
coordinate, as in Borel–Jacquet §4.1. One open subgroup of `G(𝔸_f)` fixes it on the
right for all archimedean slices, as in the common level of §4.2(b) and the compact
open idempotent of §3.2. The other requirements are rational left invariance,
`K_∞`-finiteness, annihilation on every slice by one ideal of finite codimension in the
actual enveloping centre, and moderate growth for the adelic norm of `rho`.
[Smoothness convention of the statement](AdelicIrreducibleSubrepresentationFormReduction.md#smoothness-convention)
[Scope of the tensor product formula in Getz–Hahn (6.1)](../../notes/automorphic/getz-hahn-literal-tensor-boundary.md)

## Lean proof

1. The zero vector is represented by the zero function. For a nonzero vector, the
   proof restricts the canonical bounded right action to the closed submodule `V`.
   A closed invariant subspace of the restriction maps isometrically to a closed
   invariant subspace of the original representation, which proves irreducibility
   of the restriction. `canonicalL2Equiv` intertwines the original action with the
   one on the positive rational quotient, so its inverse composed with the subtype
   inclusion gives a continuous intertwiner from `V` into that quotient's `L²`.
2. The proof intersects the given open finite stabilizer with the standard compact
   open subgroup. `exists_archimedean_smooth_convolution_of_adelicFinite` writes the
   vector as a smooth compact archimedean convolution of a vector fixed at this
   compact open level. `liftArchimedeanKernel` attaches the normalized indicator of
   that level and the Haar comparison factor. `positiveQuotientLpSmoothing` convolves
   the image of the source vector on the positive rational quotient. Left invariance
   under its defining subgroup supplies both required left invariances. The
   all-adelic conjugate mass estimate bounds the value of the convolution by a
   power of the height. The equivalence for a positive-size matrix embedding
   transfers this growth bound to the specified automorphy predicate, also when the
   original representation has size zero.
3. `exists_convolution_enveloping_representative` identifies the differentiated
   convolution on each archimedean slice with the continuous representative of the
   corresponding differentiated Hilbert vector. The identity element of the
   enveloping algebra gives the almost-everywhere equality for the original vector.
   The compact orbit of the continuous representative has finite-dimensional span
   because the linear map from continuous square-integrable representatives to
   `L²` is injective and intertwines right translation. Pulling the span back to the
   group preserves its finite dimensionality.
4. `adelicSmoothCenterActsByScalar` supplies scalar centre action on the subspace of
   archimedean-smooth, finite-level vectors. The ideal of central elements that kill
   the prescribed vector has finite codimension because the image of evaluation on
   that vector lies in its scalar line. Every corresponding derivative of the
   representative is continuous on the quotient and represents zero. Positivity
   of quotient Haar measure on nonempty opens makes that derivative vanish on the
   entire quotient, hence on each archimedean slice. The measure-preserving
   `positiveToCanonicalQuotient` then transports the almost-everywhere equality to
   the canonical measure on `[G]`.

## Provenance

- J. R. Getz and H. Hahn, *An Introduction to Automorphic Representations* (2024),
  Theorem 6.6.4, p. 172 (PDF p. 186), is the discrete-subrepresentation assertion.
  Lemma 9.7.2, pp. 264–265 (PDF pp. 276–277), supplies the pattern of combining a
  smooth compact archimedean kernel with a finite-level idempotent. The Lean proof
  uses the common elliptic reproducer and a norm perturbation on a closed subspace
  to obtain exact smoothing. Registered as `getz-hahn-2024-automorphic-representations`,
  SHA-256 `a125cf9c0f445972cbbd3552b4fb9905ca948108a05880f90eaa43558d09a507`.
- A. Borel and H. Jacquet, *Automorphic forms and automorphic representations* (1979),
  §§3.2 and 4.1, p. 194 (PDF p. 189), and §4.2(b), p. 195 (PDF p. 190).
  Registered as `borel-jacquet-1979-automorphic`, SHA-256
  `3b9fe0145da81d870ef8967be83635cd440a2581fe043e64e63324e22dec4db5`.
- The scalar action combines Segal's theorem and adjoint invariance of the
  actual centre. It applies to the full maximal
  compact subgroup allowed by the statement. Getz–Hahn's October 2026 errata,
  §4.6, p. 1, qualify their Corollary 4.6.3 by connectedness of `K`. Registered as
  `getz-hahn-2024-errata-2026-10`, SHA-256
  `e641ec2a5485443f792935afe5ae4940323755968f784ce290a96d9cd76fc1c2`.
  [Scalar action on product-group smooth vectors](../Representation/Archimedean/ProductSmoothInfinitesimalCharacter.md)
- The fixed-profile reproducer follows the elliptic method of Harish-Chandra,
  *Discrete series for semisimple Lie groups II* (1966), §8, Theorem 1, pp. 18–19.
  [Fixed-profile reproducer](AdelicFixedProfileReproduction.md)
- The growth argument uses the counting and right convolution estimates of
  C. Mœglin and J.-L. Waldspurger,
  *Spectral decomposition and Eisenstein series* (1995), I.2.4–5, pp. 25–27.
  [Growth of quotient convolutions](AdelicQuotientConvolutionGrowth.md)
