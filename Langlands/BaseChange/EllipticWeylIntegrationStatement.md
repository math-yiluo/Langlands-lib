# Weyl integration on the regular elliptic set of GL_n modulo the center

Lean module: `Langlands.BaseChange.EllipticWeylIntegrationStatement`. The file states the
proposition `EllipticWeylIntegrationStatement.{u}` and does not prove it.

## The statement

Let `F : Type u` be a nonarchimedean local field of characteristic zero, `0 < n`,
`G = GL_n(F)`, `Z` its center, `G ⧸ Z` with its Borel σ-algebra, and
`E = { gZ : g regular elliptic }`, the image in `G ⧸ Z` of the set of elements whose
characteristic polynomial is separable and irreducible. The statement asserts that there is a
measure `ν` on `G ⧸ Z` with `ν(Eᶜ) = 0` such that for every Haar measure `μ` on `G ⧸ Z` and every
`Φ : G ⧸ Z → ℂ` that is `μ`-integrable on `E`:

1. for `ν`-almost every `x` the function `g ↦ Φ(g x g⁻¹)` is `μ`-integrable;
2. the function `x ↦ ∫_{G/Z} Φ(g x g⁻¹) dμ(g)` is `ν`-integrable;
3. `∫_E Φ dμ = ∫ (∫_{G/Z} Φ(g x g⁻¹) dμ(g)) dν(x)`.

Products and inverses are taken in the quotient group `G ⧸ Z`; `g x g⁻¹` is the class of the
conjugate of a representative. The measure `ν` does not depend on `μ`.

## Source and derivation

The Weyl integration formula on `G(F)`: Henniart–Lemaire, *Changement de base et induction
automorphe pour GL_n en caractéristique non nulle*, Mém. SMF 124 (2011), II.2.10, formula (2),
printed p. 72 (PDF p. 80), with the notation of printed pp. 70–71:

`∫_{G(F)} f(g) θ(g) dg = ∑_{T ∈ 𝒯} |W_T(F)|⁻¹ ∫_{T(F)} |D_G(γ)|_F Λ^{G(F)}(f, γ) θ(γ) dγ_T`,

where `𝒯` is a set of representatives of the conjugacy classes of maximal `F`-tori, `W_T(F)`
the rational Weyl group, `D_G` the Weyl discriminant and `Λ^{G(F)}(f, γ)` the orbital integral
for the quotient measure `dg/dγ_T`. Clozel, *Invariant harmonic analysis on the Schwartz space
of a reductive p-adic group* (1991), uses the same formula modulo the center in the proof of
Theorem 3, printed p. 110 (PDF p. 121), together with the normalization of the remark after
Theorem 3: the sum runs over the elliptic Cartan subgroups modulo conjugation and the Haar
measure `dt` gives mass `1` to `Z\T`. Henniart–Lemaire, II.4.8 (1), printed p. 90 (PDF p. 98),
write the elliptic pairing with the Haar probability measure on `N_{E/F}(E^×)\T(F)`; its
pushforward to the quotient `F^×\T(F) = Z\T` is the Haar probability measure of `Z\T`, which is
Clozel's normalization.

For a function `Φ` on `G ⧸ Z` supported on `E`, only the elliptic tori contribute, and for an
elliptic `T` the quotient `T ⧸ Z` is compact. Writing the Haar measure of `G ⧸ Z` as the quotient
measure on `G/T` times a Haar measure of `T ⧸ Z`, the orbital integral `∫_{G/T} Φ(g t g⁻¹)` is
`∫_{G/Z} Φ(g t g⁻¹) dμ(g)` divided by the volume of `T ⧸ Z`. Hence the measure

`ν = ∑_T |W(G,T)|⁻¹ |D(t)| dt̄`,

the sum over elliptic tori up to conjugacy of the images in `G ⧸ Z` of `|D(t)|` times the Haar
probability measure `dt̄` of `T ⧸ Z`, satisfies the three properties, and it does not depend on
`μ`. It is carried by `E` because `D(t) = 0` at the non-regular points of `T`. The statement
asserts only the existence of such a measure, which is what the elliptic orthogonality
relations in common-measure form use.

Literature IDs
`provided-a0a5445aba86b871bcd83f08813de3234fddb463ff9bb3c9dfd60d2d2fcdae61` (SHA-256
`7af2940c75a75937c1bf9096eb329931d4245cf592e3572db0ff93ec6e76c5e0`) and
`provided-698170812a35ff43dbc4156af9f67a8384f95d97d5836529575e646643af617b` (SHA-256
`c5cb36139e9cf3ed29fe1338a45488236cc69abdc4806d5ba2180456faba08ba`).
