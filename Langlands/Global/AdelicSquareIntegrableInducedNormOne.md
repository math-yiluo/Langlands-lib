# The norm-one Levi criterion for square-integrable inducing forms

For an automorphic form with the required split-component covariance, the square integrability
condition defining `A²_P` is equivalent to integrability of its absolute square on
`K × (M(F) \ M(𝔸)¹)`. The weighted square defining `A²_P` descends to the canonical Levi quotient.
The norm-one representatives give a measure-preserving homeomorphism to that quotient, and
the inverse modulus in the integrand equals one on each such representative.

An ordinary split-component eigenvector with normalized label `λ` becomes split-component
equivariant with the half modulus after multiplication by `exp(-⟨λ,H_P⟩)`. On the norm-one
Levi slice the height character is one. Thus automorphy of the inverse twist and integrability
of the original eigenvector's absolute square there give membership of the inverse twist in
`A²_P`.

`AdelicSquareIntegrableInducedNormOneStatement` names the equivalence. It uses the inducing
space in Lapid, *On Arthur’s Asymptotic Inner Product Formula of Truncated Eisenstein
Series*, §2, printed p. 311 (volume PDF p. 320, registered as
`lapid-2011-asymptotic-inner-product-truncated-eisenstein`, SHA-256
`760161175f57a28d2e05de1f5638bc205d33123ae95f67ce4296b4b651fa950b`), and the norm-one Levi slice
of Delorme, *On the spectral theorem of Langlands* (2023), §3.4, (3.7), PDF p. 15
(`Delorme--On the spectral theorem of Langlands--2023.pdf`, SHA-256
`9b2e82af72ac45c9745357d475153d43d29ec3e1ea68bf51980acf466110e2df`, registered under
`delorme-2023-spectral-theorem-langlands`). The proof applies the Library's canonical norm-one
quotient measure comparison on the Levi and the identity on the compact factor.

At the minimal standard Levi, the maximal split torus is central. The theorem
`compactSpace_normOneRationalQuotient_bot` applies `centralSplitCompactQuotient` to that Levi.
The norm-one square of a continuous left-invariant parabolic quotient function is continuous on
the product of the compact and the compact Levi quotient. It is integrable there by
`integrable_normOneLeviSquare_bot`.
