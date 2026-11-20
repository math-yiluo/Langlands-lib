# Weyl integration data for GLₙ

`Langlands.BaseChange.WeylIntegrationData` defines the torus data and weight used in
both Weyl integration formulas of Henniart–Lemaire, *Changement de base et induction
automorphe pour GLₙ en caractéristique non nulle*, Mém. SMF 124 (2011), II.2.10,
printed pp. 70–72 (PDF pp. 78–80). The registered source ID is
`provided-a0a5445aba86b871bcd83f08813de3234fddb463ff9bb3c9dfd60d2d2fcdae61`.

## Adjoint action and discriminant

On the matrix Lie algebra `Matrix (Fin n) (Fin n) F`, `linearAdjoint γ` is right
multiplication by `γ⁻¹` followed by left multiplication by `γ`. This sends `X`
to `γ X γ⁻¹`. The discriminant `weylDiscriminant γ` is the coefficient of degree
`n` in the characteristic polynomial of `linearAdjoint γ - LinearMap.id`, using
Mathlib's `LinearMap.charpoly`. This gives the coefficient of `tⁿ` in
`det(t I - Ad(γ) + I)` in the source's definition of `D_G(γ)` on p. 70.

## Rational tori and conjugacy classes

`WeylTorus F n` records a subgroup of `GeneralLinear n F` with a witness that it is
`glCentralizer γ₀` for some `γ₀` satisfying `IsRegularSemisimple`. For positive rank,
the separable characteristic polynomial gives `γ₀` simple spectrum over a splitting
field. Its matrix commutant is the finite étale algebra `F[γ₀]`, and the units in this
commutant give the rational points of the corresponding maximal torus. Over the
infinite local field in the formulas, each maximal torus has a regular semisimple
rational point because the simple-spectrum units form a nonempty Zariski-open subset of its
underlying finite étale algebra. Over an arbitrary field the type ranges over
the subgroups admitting the stated witness.

`WeylTorus.IsConjugate` compares rational point subgroups by the image under
`g ↦ x g x⁻¹` for `x` in `GeneralLinear n F`. `WeylTorus.IsRepresentativeSet` encodes the
choice on p. 71 by asking for exactly one member of the set conjugate to each torus.
`WeylTorus.RationalWeylGroup` is the subgroup normalizer modulo the torus subgroup
included in it. The rational point subgroup generates the matrix algebra `F[γ₀]`
because it contains `γ₀`, so normalizing the subgroup is equivalent to normalizing
that algebra. The exact sequence on p. 71 identifies the resulting quotient
`N_G(T)(F) / T(F)` with the source's `W_T(F)` in the setting of the formulas.

## Torus points over an algebra and the integration domains

`WeylTorus.points T E` centralizes the image of the rational point subgroup under
`baseChange F E n`. The linear equation defining the matrix commutant of `γ₀`
commutes with scalar extension from a field to any commutative `F`-algebra `E`.
The resulting matrix commutant is `E[baseChange F E n γ₀]`, and it commutes with all
base-changed rational torus points. Conversely, the image subgroup contains the
base change of `γ₀`. Its group centralizer therefore gives the units in the extended
commutant, realizing the `T(E)` used in the source.

`WeylTorus.regularPoints T` is the subset of `T(F)` satisfying
`IsRegularSemisimple`. These are the points used in the ordinary integral, since
p. 70 gives the vanishing of `D_G` off the regular semisimple locus.
`WeylTorus.normImage T σ l` consists of the rational torus points `γ` admitting
some `δ` in `T.points E` with `cyclicNorm σ l δ = baseChange F E n γ` in
`GeneralLinear n E`. The definition takes the algebra automorphism `σ` and the
product length `l` as parameters. For a cyclic algebra with generator `σ` of
order `l`, p. 71 identifies the quotient `T(E)^{σ-1} \ T(E)` with the open norm
image in `T(F)` and obtains its Haar measure from `T(F)`. In the resulting
rational-torus formulation of the twisted integral, the domain is
`T.regularPoints ∩ T.normImage σ l` with the restriction of the same Haar measure
used in the ordinary integral for `T`.

## Common weight and scope

`WeylTorus.integrationWeight T γ` divides the Library's
`residueNormalizedAbsoluteValue F (weylDiscriminant γ)` by the real cast of
`Nat.card T.RationalWeylGroup`. At `γ = N(δ)` this gives the same weight as in
the twisted formula on p. 72. The weight uses any nonarchimedean local field.
The algebraic declarations allow independent universes for `F` and `E` and
include `n = 0`, where the matrix group is trivial and the characteristic
polynomial on the zero-dimensional matrix space is `1`.

The Jacobian comparison, rational Weyl group finiteness, torus norm geometry,
and measure identities are subsequent mathematical targets.
