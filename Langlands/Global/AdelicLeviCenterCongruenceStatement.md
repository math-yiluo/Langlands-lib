# The normalized Harish-Chandra congruence of the center, common to two parabolics

Module `Langlands.Global.AdelicLeviCenterCongruenceStatement` contains one `Prop`-valued
definition, `Langlands.Global.LeviRestrictionCenterCongruenceStatement`, and no theorems. It is
the algebraic form, inside the enveloping algebra of `G(F_∞)`, of the normalized Harish-Chandra
homomorphism `𝔷 → 𝔷(𝔪')` and of its independence of the parabolic. This file does not prove
the statement.

## Data and hypotheses

The data and hypotheses are those of `LeviRestrictionCenterTransferStatement` (module
`AdelicLeviCenterTransferStatement`), without the commutator data `hcalc`, `hcalc'`:

- a number field `F` and group schemes `G, P, M, U, Q, M', V` over `F`, with `G`, `P`, `Q`, `M'`
  affine and `P`, `Q` locally of finite type, `G` connected reductive;
- parabolics `p : P → G`, `q : Q → G` with geometric unipotent radicals `iU : U → P`,
  `iV : V → Q` and rational Levi subgroups `l : M → P`, `l' : M' → Q`;
- a Weyl conjugation `(w, c)` (`IsWeylConjugation p l q l' w c`): `w` is a rational point of `G`
  and `c : M' → M` satisfies `l(c(m')) = w⁻¹ l'(m') w`;
- smooth structures `hsmooth` on `G` and `hsmooth'` on `M'`, and a central element `z` of
  `AdelicEnvelopingAlgebra F G hsmooth`.

## Objects

The objects are those of the module `InfiniteAdelicLeviEnveloping`. Write `U(𝔤)`, `U(𝔪')` for
`AdelicEnvelopingAlgebra F G hsmooth` and `AdelicEnvelopingAlgebra F M' hsmooth'`.

- `j_Q = pointEnvelopingMap F hsmooth' hsmooth (l' ≫ q)` and
  `j_P = pointEnvelopingMap F hsmooth' hsmooth (c ≫ l ≫ p)` are the algebra maps
  `U(𝔪') → U(𝔤)` induced by the tangent maps at the identity of `ι_Q, ι_P : M'(F_∞) → G(F_∞)`.
- `δQ(m) = parameterPower F Q (-halfModulusParameter F Q) (l'(m))` and
  `δP(m) = parameterPower F P (-halfModulusParameter F P) (l(c(m)))` are the normalizing
  factors of `LeviRestrictionCenterTransferStatement`, `δ_Q(m)^{-1/2}` and `δ_P(c(m))^{-1/2}`.
- For proofs `hQ`, `hP` that the derivatives at the identity of `δQ`, `δP` vanish on brackets,
  `τ_Q = envelopingCharacterShift F hsmooth' δQ hQ` and
  `τ_P = envelopingCharacterShift F hsmooth' δP hP` are the automorphisms of `U(𝔪')` with
  `τ(Y) = Y + dδ(Y)` on generators.
- `I_V = curveRightIdeal F hsmooth SV` and `I_U = curveRightIdeal F hsmooth SU`, where `SV`
  and `SU` are the images of `V(F_∞)` and `U(F_∞)` in `G(F_∞)` under `iV ≫ q` and `iU ≫ p`: the
  complex spans of the products `ι(1 ⊗ X) · b` with `X` the velocity at `0` of a smooth curve
  through the identity in `SV`, resp. `SU`.

## Conclusion

For all such proofs `hQ`, `hP` there is `y ∈ U(𝔪')` with

1. `z - j_Q(τ_Q y) ∈ I_V`, and
2. `z - j_P(τ_P y) ∈ I_U`.

The derivatives of the smooth characters `δQ`, `δP` do vanish on brackets
(`mvfderiv_character_lie`), so the quantification over `hQ`, `hP` is not vacuous; it lets the
statement use `τ_Q`, `τ_P` without a separate smoothness lemma.

## Mathematical content

Let `𝔤`, `𝔪'` be the complexified Lie algebras of `G(F_∞)`, `M'(F_∞)`, and `𝔳`, `𝔲` those of
`V(F_∞)`, `U(F_∞)`, inside `𝔤`. Knapp–Vogan, Lemma 4.123, decompose
`U(𝔤) = U(𝔪') ⊕ (𝔳̄ U(𝔤) + U(𝔤) 𝔳)` and show that a central `z` has its second component in
`U(𝔤) 𝔳` and its first component `μ_𝔳(z)` in the center of `U(𝔪')`. Applying the antipode `S`
(which preserves the center) gives the mirror form used here: `z - S μ_𝔳(S z) ∈ 𝔳 U(𝔤)`. The
normalized map `τ_𝔳 ∘ μ_𝔳`, with `τ_𝔳(X) = X - ρ(𝔳)(X)` and `ρ(𝔳)` half the sum of the roots
in `𝔳` (written `δ(𝔲)` in Knapp–Vogan (4.124)–(4.128)), equals
`γ_{𝔪'}⁻¹ ∘ γ_𝔤` on the center (Proposition 4.129 (c)), so it does not depend on the parabolic
with Levi factor `𝔪'`. Mirrored by `S`, the element `y = S τ_𝔳 μ_𝔳 (S z)` satisfies
`z - j_Q(τ_Q y) ∈ 𝔳 U(𝔤)`, because `dδQ = -ρ(𝔳)` on `𝔪'` (the derivative of
`|det Ad|_{Lie V}|^{-1/2}`). This is clause 1, since `𝔳 U(𝔤) ⊆ I_V`.

For clause 2, `ι_P(m) = w⁻¹ ι_Q(m) w`, so `j_P = Ad(w⁻¹) ∘ j_Q`. Conjugating by `w` turns
clause 2 into the congruence of `z = Ad(w) z` modulo `Ad(w) 𝔲 · U(𝔤)`, where `Ad(w) 𝔲` is the
nilradical of the parabolic `w P w⁻¹`, whose Levi subgroup is `M'`, and `dδP = -ρ(Ad(w) 𝔲)`.
Independence of the parabolic gives the same `y`. That `Ad(w)` fixes `z` is
`AdelicEnvelopingCenterConjugationStatement`, proved in the Library by
`adelicEnvelopingCenterConjugation`.

## Sources

- A. W. Knapp and D. A. Vogan, *Cohomological Induction and Unitary Representations*, Princeton
  University Press, 1995 (`knapp-vogan-1995-cohomological-induction`), Chapter IV §8:
  Lemma 4.123, printed p. 301; the shift (4.124) and the definitions (4.125)–(4.128), printed
  pp. 302–303; Proposition 4.129 (c) and the sentence before it ("independent of 𝔲"), printed
  p. 303. PDF page = printed page + 22.
- C. Mœglin and J.-L. Waldspurger, *Spectral decomposition and Eisenstein series*, Cambridge
  University Press, 1995 (`moeglin-waldspurger-1995-spectral-decomposition`), I.2.17, printed
  pp. 37–38 (chapter PDF `05.2_pp_18_40_Automorphic_forms_growth_constant_terms.pdf`,
  pp. 20–21): the homomorphism `i : 𝔷 → 𝔷_M`.

## Provenance

Derived. Clause 1 is Knapp–Vogan Lemma 4.123 (b), (c) with the shift (4.124), mirrored by the
antipode to the right ideal `𝔳 U(𝔤)`. Clause 2 with the same `y` is Proposition 4.129 (c)
applied to the parabolic `w P w⁻¹` and transported by `Ad(w)`. The formulation with tangent
maps of the Library's Lie groups, curve tangents of the images of `V(F_∞)` and `U(F_∞)`, and
the derivatives of the normalizing factors of `LeviRestrictionCenterTransferStatement` is
internal to the Library.

The mirrored form is the one that matches the Library's right differentiation, but only after
evaluation on the Levi subgroup. Under right differentiation, an element of `I_V` acts on a
left `V(F_∞)`-invariant function `f` by an operator whose values vanish at the points of the
image of `M'(F_∞)` under `ι_Q`, not at every point of `G(F_∞)`. Indeed, let `X` be the
velocity of a curve `c(t)` in the image of `V(F_∞)` and let `m` lie in the image of `M'(F_∞)`.
Right differentiation by `ι(1 ⊗ X) · b` applies the operator of `b` first and then
differentiates along `X`. The operator of `b` preserves left `V(F_∞)`-invariance. Since `V` is
normalized by `M'`, `m c(t) = (m c(t) m⁻¹) m` with `m c(t) m⁻¹` in the image of `V(F_∞)`, so
the outer derivative at `m` is zero. The same argument applies to `I_U`, left
`U(F_∞)`-invariant functions and the image of `M'(F_∞)` under `ι_P`, which normalizes the
image of `U(F_∞)`.

At other points the vanishing can fail. Take `F = ℚ`, `G = SL₂`, `V` the upper unitriangular
matrices and `f(x) = x₂₂`, which is left `V`-invariant. At `x₀ = [[0, -1], [1, 0]]` and along
`c(t) = 1 + t E₁₂`, `f(x₀ c(t)) = t`, so the derivative of `f` along the generator
`ι(1 ⊗ E₁₂) ∈ I_V` at `x₀` is `1`.

For the restrictions `m ↦ δ(m) f(ι(m) g)` with a general point `g` of `G(F_∞)`, one applies
the vanishing at the Levi to the right translate `x ↦ f(x g)`, which is still left invariant,
and commutes the action of the central `z` with the right translation using the
`Ad`-invariance of the center (`adelicEnvelopingCenterConjugation`). With these steps the
statement gives `LeviRestrictionCenterTransferStatement`.
