# The exponent decomposition from Harish-Chandra's finiteness theorem: the implication

Module `Langlands.Global.AdelicAutomorphicExponentDecompositionReductionStatement` states the
proposition `Langlands.Global.AutomorphicExponentDecompositionReductionStatement` (universe `u`)
and proves nothing.

## Statement

```
AutomorphicExponentDecompositionReductionStatement.{u} :=
  ParabolicHarishChandraFinitenessStatement.{u} → AutomorphicExponentDecompositionStatement.{u}
```

- The premise is `Langlands.Automorphic.GroupSchemeFunctions.ParabolicHarishChandraFinitenessStatement`
  (module `Langlands.Automorphic.GroupSchemeHarishChandraFinitenessStatement`): Harish-Chandra's
  finiteness theorem on a parabolic quotient `V(𝔸)M'(F) \ G(𝔸)` of a connected reductive group
  over a number field. For a maximal compact `K` with `Q(𝔸)K = G(𝔸)`, a closed matrix embedding,
  an ideal `J` of finite codimension in the center of the complex enveloping algebra, an open
  subgroup `L` of `G(𝔸_f)` and a finite-dimensional space `E` of functions on
  `K_∞ = K ∩ G(F_∞)`, the automorphic functions on the quotient that are right invariant under
  `L`, annihilated by `J` and whose functions `k ↦ f(g k)` on `K_∞` lie in `E` span a
  finite-dimensional space.
- The conclusion is `Langlands.Global.AutomorphicExponentDecompositionStatement` (module
  `Langlands.Global.AdelicAutomorphicExponentDecompositionStatement`): for a compatible standard
  parabolic family `fam` of `G`, a maximal compact `K` with `P₀(𝔸)K = G(𝔸)` and maximal compact
  inverse images in the standard Levis, a closed matrix embedding and `Kinf = K ∩ G(F_∞)`, every
  automorphic function `ψ` on `U_Q(𝔸) M_Q(F) \ G(𝔸)` is a finite sum `∑_{λ ∈ s} c λ` of
  automorphic functions on the same quotient with generalized unnormalized exponents `λ` for the
  left action of the positive split component `𝔄_{P_Q}`, cuspidal along `Q` whenever `ψ` is.

Both propositions quantify over number fields `F : Type u`; the implication is stated in one
universe `u`.

## Mathematical origin

The implication is the route by which the decomposition (6.10) of Bernstein–Lapid, and the Lemma
of Mœglin–Waldspurger I.3.2, follow from a finiteness theorem. In Mœglin–Waldspurger I.3.2
(printed pp. 41–43) the decomposition of an automorphic form `φ` on `U(𝔸)M(k) \ G` rests on the
`𝔷(A_M)`-finiteness of `φ` under left translation, deduced in I.2.17 (printed pp. 37–38) from the
homomorphism `𝔷 → 𝔷_M`; the same paragraph I.2.17 records that Harish-Chandra's finiteness
theorem extends to `U(𝔸)M(k) \ G`. Left translation by `𝔄_{P_Q}` keeps an automorphic function
on `U_Q(𝔸) M_Q(F) \ G(𝔸)` in the finite-dimensional space of Harish-Chandra's theorem with the
level, the `K_∞`-types and the annihilating ideal of `φ`: `𝔄_{P_Q}` is central in `M_Q(𝔸)` and
normalizes `U_Q(𝔸)`, and left translations commute with right translations and with the center
of the enveloping algebra. A finite-dimensional continuous representation of `𝔄_{P_Q} ≅ ℝ^r`
splits into generalized eigenspaces whose vectors have the polynomial form of
`HasUnnormalizedExponent` (Mœglin–Waldspurger I.3.1, printed pp. 40–41, for smooth
`𝔷(A_M)`-finite functions on `A_M`), and the components lie in the span of the translates of `φ`,
hence are automorphic, and cuspidal when `φ` is. The constant term of a function along a
smaller standard parabolic commutes with left translation by `𝔄_{P_Q}`.

## Sources

- J. Bernstein and E. Lapid, *On the meromorphic continuation of Eisenstein series*, J. Amer.
  Math. Soc. 37 (2024), registered as `bernstein-lapid-2024-meromorphic-continuation-eisenstein`:
  §6.2, pp. 201–202, (6.1), (6.3) and (6.6); §6.3, p. 203, (6.10).
- C. Mœglin and J.-L. Waldspurger, *Spectral Decomposition and Eisenstein Series* (1995),
  registered as `moeglin-waldspurger-1995-spectral-decomposition`: I.2.17, printed pp. 37–38
  (chapter file `05.2_pp_18_40_Automorphic_forms_growth_constant_terms.pdf`); I.3.1, printed
  pp. 40–41, I.3.2, printed pp. 41–43, and I.3.3, printed pp. 43–45 (chapter file
  `05.3_pp_40_48_Cuspidal_components.pdf`).
- Harish-Chandra, *Automorphic Forms on Semisimple Lie Groups* (LNM 62, 1968), registered as
  `provided-d0ff4732ff6b5d8ecf8562752577df639622e8aad2899ef307bc320213b534af`: Chapter I, §2,
  Theorem 1, printed p. 8, through the premise.
