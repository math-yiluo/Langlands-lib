# Irreducible subrepresentations in the square-integrable form spectrum

`Langlands.Global.irreducibleSubrepresentationFormSpectrum` proves
`Langlands.Global.IrreducibleSubrepresentationFormSpectrumStatement`. For a presented
parabolic `p : P → G` that is an isomorphism, every irreducible subrepresentation `V`
of the canonical right action on `L²([G])` lies in `squareIntegrableFormSpectrum`,
the closed span defined by the square-integrable induced forms `A²_P`.

The Lean proof applies `irreducibleSubrepresentationFormSpectrum_of_finiteVectorAutomorphy`
to `irreducibleSubrepresentationFiniteVectorAutomorphy`. The latter gives each finite
vector of `V` a representative `φ` that is left invariant under `G(F)` and `A_G` and
agrees with the vector almost everywhere on `[G]`. Automorphy uses the Library's
`IsAutomorphicFunctionOn`, with smooth archimedean slices and a common open finite
level in the convention of Borel–Jacquet. [Proof of finite-vector automorphy](AdelicIrreducibleSubrepresentationFiniteVectorAutomorphyProof.md)

In the reduction, `isSquareIntegrableInducedForm_of_isIso` puts `φ` in `A²_P`.
The unipotent radical has trivial image, the modulus factor is one, and
`l ≫ p : M → G` identifies the split components and transports the canonical
quotient measures up to a positive scalar. The almost-everywhere equality gives
square integrability on `[G]`, which yields the required integrability on
`K × [M]` by measure transport and right invariance. The vector is then a generator
of the span using one form with coefficient one. The theorem
`subset_closure_canonicalL2FiniteVectors` puts all of `V` in the closure of these
finite vectors, and monotonicity of closure gives the inclusion.
[Full-parabolic comparison and reduction](AdelicIrreducibleSubrepresentationFormReduction.md)
[Density of finite vectors](AdelicL2FiniteVectorDensity.md)

## Provenance

- Getz–Hahn, *An Introduction to Automorphic Representations* (2024), gives the
  automorphy assertion for finite vectors in Theorem 6.6.4, p. 172 (PDF p. 186),
  and their density in Lemma 9.7.2, pp. 264–265 (PDF pp. 276–277). Registered as
  `getz-hahn-2024-automorphic-representations`, SHA-256
  `a125cf9c0f445972cbbd3552b4fb9905ca948108a05880f90eaa43558d09a507`.
- Borel–Jacquet, *Automorphic forms and automorphic representations* (1979),
  §§4.1 and 4.2(b), pp. 194–195 (PDF pp. 189–190), gives the slice smoothness
  convention and the common finite level. Registered as
  `borel-jacquet-1979-automorphic`, SHA-256
  `3b9fe0145da81d870ef8967be83635cd440a2581fe043e64e63324e22dec4db5`.
- Lapid, *On Arthur's asymptotic inner product formula of truncated Eisenstein series*
  (2011), §2, p. 311 (volume PDF p. 320), defines `A²_P` and states its density
  in the induced discrete spectrum. The inclusion here is the direction that
  places the irreducible subspaces in the closed span for `P ≅ G`. Registered as
  `lapid-2011-asymptotic-inner-product-truncated-eisenstein`, SHA-256
  `760161175f57a28d2e05de1f5638bc205d33123ae95f67ce4296b4b651fa950b`.
