# Positivity of the adelic induced inner product in Gram form

`Langlands.Global.inducedInnerProductGram` proves
`Langlands.Global.InducedInnerProductGramStatement`. It derives Gram
positivity from the squared norm on `A²_P` in E. Lapid, *On Arthur's
asymptotic inner product formula of truncated Eisenstein series* (2011),
§2, p. 311 (registered source
`lapid-2011-asymptotic-inner-product-truncated-eisenstein`, PDF p. 320).
The signed integral comparison below accounts for the Library's
weighted realization of that norm.

For the finite family in the statement, `squareIntegrableInducedForms`
puts `Φ = ∑ i, x i • φ i` in `A²_P`. The proof expands the kernel of
`inducedInnerProduct` for `(Φ, Φ)` into the double sum. The published
kernel integrability and termwise integration lemmas identify this
diagonal pairing with the Gram sum.

On the positive split component `A` of the Levi, the logarithmic
coordinates give a group homeomorphism to the additive group of `ℝⁿ`.
The proof uses bijectivity of character restriction from the parabolic
to its Levi, the split-centre restriction equivalence on real character
duals, and the dual coordinates of `e`. The pushforward of the Haar
measure on `A` is a positive multiple of Lebesgue measure by Haar
uniqueness. Thus the integral of `β` in the split factor is strictly
positive by `∫ β = 1`, even for signed `β`.

The proof computes the rational quotient integral on the product
fundamental domain `A × D¹`, where `D¹` represents the rational
quotient of the norm-one subgroup. The logarithmic weight depends
only on `A`, and split-component equivariance makes the
modulus-weighted norm square `normWeight` constant along `A`.
Factoring the real Bochner integral and transporting the `D¹` integral
to the canonical Levi quotient gives the diagonal pairing as a
positive constant times the integral of `normWeight` over the product
of `K` and that quotient. Haar uniqueness on the Levi accounts for the
arbitrary input Haar measure.

The `A²_P` hypothesis gives integrability of `normWeight`, which is
nonnegative. A zero diagonal therefore forces it to vanish almost
everywhere. It is continuous, and the product measure gives positive
mass to every nonempty open set, so it vanishes pointwise. The modulus
factor is strictly positive, giving `Φ(mk) = 0` for every Levi point
`m` and `k ∈ K`. Iwasawa coverage and the Levi decomposition express
every adelic point as `umk`. Left invariance under `U(𝔸)` gives `Φ = 0`.
Conversely, the zero function has zero diagonal pairing.

The [coordinate proof](AdelicInducedInnerProductGramCoordinateProof.md) also gives the torus homeomorphism and quotient-integral formulas.
