# ℓ-adic models of continuous complex Galois representations

`ladicModelOfContinuousComplex` constructs a continuous irreducible
\(\ell\)-adic model of a continuous irreducible complex action of a
compact nonarchimedean group. It uses a specified embedding
\(\overline{\mathbb Q}_\ell\hookrightarrow\mathbb C\).

The complex action has finite image and open kernel. Algebraic coefficient
descent gives a model with the same kernel, so the \(\ell\)-adic action is
continuous. In a finite basis, the finitely many action operators give
finitely many matrix entries. Adjoining these entries to \(\mathbb Q_\ell\)
gives the finite coefficient extension used by `IsLadicDefinedOverFiniteExtension`.
[Coefficient descent](../Weil/Representation/FiniteImageCoefficientDescent.md)

For the absolute Galois group of a nonarchimedean local field, the scalar
extension intertwiner restricts to the local Weil group. Every irreducible
complex Weil class has an unramified twist pulled back from such a Galois
class. Consequently `exists_unramifiedTwist_ladicWeilTransport` gives a
preimage under \(\ell\)-adic transport for a suitable twist, in the same rank.
[Weil–Galois dictionary](HenniartGaloisDictionaryProof.md)

This is the existence direction of the coefficient comparison used in
Henniart's numerical count. See `henniart-1988-numerical`, SHA-256
`3de93884b6c4b26106d614e648cfb7f293f9f40a66ef352c0751e222a602f25c`,
§§4.1–4.2, printed pp. 509–510 (PDF pp. 14–15).
