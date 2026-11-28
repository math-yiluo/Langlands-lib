# One center ideal for all regular intertwining integrals

`intertwiningUniformCenterIdeal` proves `IntertwiningUniformCenterIdealStatement`. It constructs
one cofinite ideal of the ambient archimedean enveloping center that annihilates every
plot-smooth infinite slice of the intertwining integral above the regularity threshold.

## The ideal on the common Levi

Write `Z_G` for `AdelicEnvelopingCenter F G hsmooth`, and write `Z_{M'}` for the corresponding
center on the target Levi. The isomorphism `c : M' ⟶ M` from the Weyl conjugation makes
`c ≫ l` the source Levi map on the same group `M'`. The proof uses
`parabolicLeviCenterRestriction` at right translate `1` for each parabolic. It obtains
algebra maps `p_P, p_Q : Z_G → Z_{M'}` that compare the ambient action with the Levi action on
unnormalized restrictions of functions invariant under the respective unipotent radicals.

At a right translate `g`, restriction is restriction at `1` of the right-translated
function. Right translation preserves left unipotent invariance and commutes with `Z_G` by
`plotSmoothCenterAction_rightTranslation`. Thus every right translate of every inducing
slice is killed by the cofinite ideal `J` given by center finiteness of `φ`. The finite
algebra map `p_P` lets `exists_cofinite_center_ideal_of_leviRestriction` extend `J` to a
cofinite ideal `I` of `Z_{M'}` that annihilates all unnormalized inducing restrictions.

## Normalization and the ambient ideal

Let `χ_P(m) = δ_P(c(m))^{-1/2}` and `χ_Q(m) = δ_Q(m)^{1/2}` on `M'(F_∞)`, with the
moduli evaluated through the respective Levi maps. The proof uses the plot-smooth
parameter powers of the signed half-modulus parameters. For each of these characters,
`exists_centerShift_plotSmoothMultiplication` gives an algebra endomorphism `θ` of
`Z_{M'}` such that `D_v(χ f) = χ D_{θ(v)} f`, where `D_v` is the Levi center action.
Write `θ_P` and `θ_Q` for the shifts of `χ_P` and `χ_Q`.

The ambient ideal is the preimage
`(θ_P ∘ θ_Q ∘ p_Q)⁻¹(I)`. It is cofinite by `Langlands.Algebra.quotientFinite_comap`,
which embeds the quotient by the preimage into the finite-dimensional quotient by `I`.
All these maps and ideals are chosen before the parameter `λ`.

For an ambient operator `z` in this ideal, put `y = θ_Q(p_Q(z))`. Since `θ_P(y) ∈ I`,
the shift for `χ_P` shows that `y` annihilates every inducing restriction after
multiplication by `χ_P`. For a target restriction, apply the shift for `χ_Q` to the
restriction normalized by `χ_Q⁻¹`. Multiplication by `χ_Q` sends the action of `y`
on that normalized restriction to the action of `p_Q(z)` on the raw restriction.
The latter agrees with the raw restriction of the ambient action of `z`. The two
target characters multiply to one, and multiplication by `χ_Q` is injective.
This gives the required action identity on normalized target restrictions.

## Passage through the integral

The threshold `R₀` comes from `intertwiningAbsoluteConvergence`. For each regular `λ`,
the proof applies its majorant to the singleton consisting of `λ` in linear
coordinates. The analytic lemma `IsIwasawaCompact.centerAction_intertwiningOperator_eq_zero_of_levi`
uses that majorant and `intertwiningStabilizerModulus`. The latter gives the Haar factor
in the normalized Levi restriction formula. In this formula, for each point of the
integration quotient, the factors depending on `λ` are constant in the Levi variable.
Testing against compactly supported smooth functions on the Levi, the analytic lemma
moves the operator to the test function, uses Fubini and moves the operator back onto
each normalized inducing restriction. Its action there is zero. The target action
identity then gives the claimed annihilation on the plot-smooth output slice.

This implements the center-ideal step of Bernstein–Lapid, *On the meromorphic
continuation of Eisenstein series*, J. Amer. Math. Soc. 37 (2024), §8.2, p. 222,
using the normalized restriction formula (6.5), p. 201. The finite comparison and
extension of the inducing annihilator are the center-finiteness argument of
Mœglin–Waldspurger, *Spectral Decomposition and Eisenstein Series* (1995), I.2.17,
pp. 37–38, expressed with the unnormalized comparison and the character shifts.
