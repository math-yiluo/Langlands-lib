# Ordinary Weyl integration for GLₙ

`Langlands.BaseChange.WeylIntegrationFormulaStatement` states the ordinary Weyl
decomposition of Haar integrals on `GL_n(F)` over a nonarchimedean local field
`F`. It allows every characteristic of `F` and every `n`, including `n = 0`.
The file states the proposition and does not prove it.

## The statement

Fix a Haar measure `μF` on `GeneralLinear n F`, a set `S` of `WeylTorus F n`
with `WeylTorus.IsRepresentativeSet S`, so that `S` contains exactly one member
of each `GL_n(F)`-conjugacy class of rational maximal tori, and an arbitrary
Haar measure `μT T` on the rational point group of each `T ∈ S`. The
proposition asserts the following.

1. Every `T.RationalWeylGroup` is finite. It is the normalizer of `T(F)` in
   `GL_n(F)` modulo `T(F)`, the source's `W_T(F)`. Finiteness makes
   `Nat.card T.RationalWeylGroup` the order `|W_T(F)|`, not the value `0`
   that `Nat.card` takes on an infinite type. The theorem
   `Langlands.BaseChange.WeylTorus.finite_rationalWeylGroup` in
   `Langlands.BaseChange.WeylTorusFinite` proves this finiteness over any
   field.
2. For every `T ∈ S` and every `γ ∈ T.regularPoints` there are a measure
   `μC T γ` on `glCentralizer γ` and a measure `ν T γ` on the left coset space
   `LeftQuotient (glCentralizer γ)`. The measure `μC T γ` is a right invariant
   Haar measure whose pushforward to `GL_n(F)` equals the pushforward of
   `μT T`. The measure `ν T γ` satisfies `QuotientIntegration.IsCompatible`
   for `μF` and `μC T γ`. The two families are chosen once, before the input
   function.
3. Let `f : GL_n(F) → ℂ` be integrable for `μF`. For each `T ∈ S`, at
   `μT T`-almost every regular point `γ`, the orbit function
   `twistedOrbitFunction (MonoidHom.id _) γ f`, which is `x ↦ f(x⁻¹ γ x)` on
   the coset space, is integrable for `ν T γ`. The torus integrand is
   `T.integrationWeight γ * orbitalIntegral γ (ν T γ) f` at regular points
   `γ` of `T(F)` and `0` at the other points. Each torus integrand is
   integrable for `μT T`, the family of the integrals of their norms over
   `S` is summable, and

   `∫ g, f g ∂μF = ∑' T : S, ∫ γ, integrand T γ ∂μT T`.

The coset spaces carry their Borel σ-algebras through
`leftQuotientMeasurableSpace`, installed as a local instance as in
`Langlands.BaseChange.OrbitalIntegral`. Since `orbitalIntegral` is a Bochner
integral, which is `0` for a non-integrable function, the integrability
conclusions are part of the content of the statement.

## Normalization

`WeylTorus.integrationWeight T γ` is `|D_G(γ)|_F / |W_T(F)|`. Here
`weylDiscriminant γ` is the coefficient of `tⁿ` in `det(t − Ad(γ) + 1)` on
`𝔤(F) = M(n, F)` (Henniart–Lemaire, printed p. 70), and
`residueNormalizedAbsoluteValue` is the absolute value with `|ϖ|_F = q⁻¹` for
a uniformizer `ϖ` and residue field cardinality `q` (printed p. 14).

The theorem `Langlands.BaseChange.WeylTorus.glCentralizer_eq_of_regularPoint`
in `Langlands.BaseChange.OrdinaryWeylOrbit` shows that the centralizer of a
regular point of `T(F)` is the subgroup `T(F)` itself.
The pushforward condition therefore says that `μC T γ` is `μT T` on this
subgroup. This is the normalization on printed p. 72: the Haar measure
`dg_γ` on `G_γ(F)` is deduced from `dγ_T` through `γ' ↦ g⁻¹ γ' g`, where
`g ∈ G(F)` conjugates `G_γ` to a torus of the chosen set, and `g = 1` for a
regular point of that torus.

`QuotientIntegration.IsCompatible` describes the quotient measure
`dg / dg_γ` on `G_γ(F) \ G(F)` used in the orbital integrals of printed
p. 15. It requires the measure to be nonzero, regular and invariant under
right translation, and it requires the Weil formula
`∫_{H\G} ∫_H φ(h g) dμ_H(h) dν = ∫_G φ dμF` for compactly supported
continuous `φ`. With these measures,
`orbitalIntegral γ (ν T γ) f = ∫ f(x⁻¹ γ x) dν(x)` is the source's
`Λ^{G(F)}(f, γ)`.

The pushforward condition determines `μC T γ`, because the inclusion of the
closed subgroup `T(F)` is a measurable embedding. A regular quotient measure
is determined by the Weil formula on compactly supported continuous
functions, since every compactly supported continuous function on the coset
space is an average of one on `G(F)`. The existential quantifiers therefore
select the measures of the source.

## Relation to the source formula

Henniart–Lemaire, *Changement de base et induction automorphe pour GLₙ en
caractéristique non nulle*, Mém. SMF 124 (2011), II.2.10, printed pp. 70–72
(PDF pp. 78–80), formula (2), reads

`∫_{G(F)} f(g) θ(g) dg = Σ_{T ∈ 𝒯} |W_T(F)|⁻¹ ∫_{T(F)} |D_G(γ)|_F Λ^{G(F)}(f, γ) θ(γ) dγ_T`

for `f ∈ C_c^∞(G(F))` and a locally integrable `θ` with `θ(g⁻¹ γ g) = θ(γ)`
for almost every regular `γ` and every `g`. The set `𝒯` and the Haar
measures `dγ_T` are chosen as on printed p. 71, which `S` and `μT` encode.

The Lean proposition states the measure decomposition underlying this
identity for arbitrary integrable functions. The function `fθ` is integrable,
and at almost every regular torus point its orbit function is `θ(γ)` times
the orbit function of `f`. The proposition applied to `fθ` therefore gives
formula (2). The torus integrand is `0` off the regular points. In the
source, `D_G(γ)` vanishes exactly off the regular semisimple elements
(printed p. 70), and the non-regular elements of `T(F)` form a null set
for `dγ_T`.

The summability of the integrals of the norms makes the sum over `S`
absolutely convergent, and `S` may be infinite. In characteristic `p > 0`,
`F` has infinitely many separable extensions of degree `p`, so `GL_n(F)` has
infinitely many conjugacy classes of rational maximal tori once `n ≥ p`.

For `n = 0` the group `GL_0(F)` is trivial. Its identity is regular
semisimple, because its characteristic polynomial `1` is separable. The only torus is
the whole group, its weight is `1`, and the formula reduces to the Weil
formula for the quotient of the trivial group by itself.

The registered source ID is
`provided-a0a5445aba86b871bcd83f08813de3234fddb463ff9bb3c9dfd60d2d2fcdae61`.
