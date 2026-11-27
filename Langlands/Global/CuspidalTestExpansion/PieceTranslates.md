# Intertwining integrals of positive split translates

Module `Langlands.Global.CuspidalTestExpansion.PieceTranslates`
(namespace `Langlands.Global.StandardParabolicFamily`, with one lemma in
`Langlands.GroupScheme`).

Throughout, `n` is a rational point and `c : M_J → M_{I₁}` satisfies
`IsWeylConjugation (fam.p I₁) (fam.l I₁) (fam.p J) (fam.l J) n c`, and `K` is an Iwasawa
subgroup for `P_{I₁}`.

## Declarations

- `Langlands.GroupScheme.cancel_mono_of_left`: a homomorphism of group schemes whose underlying
  morphism of schemes is a monomorphism can be cancelled on the right.
- `exists_splitComponent_iso_of_iso`: an isomorphism `c` of the standard Levis restricts to an
  isomorphism of their split components `A_J ≅ A_{I₁}` compatible with the inclusions.
- `intertwiningIntegrand_unnormalizedAction_eq`: if `b ∈ P_{I₁}(𝔸)` and `a ∈ G(𝔸)` satisfy
  `p(b) = n⁻¹ a n`, the intertwining integrand of the left translate `h(b ·)` at `y` is
  `b^{-λ}` times `v ↦ h_λ(n⁻¹ a v y)`.
- `integrable_intertwiningIntegrand_of_mem_translateSpan`: if `f` is continuous, left
  `U_{I₁}(𝔸)`-invariant and its intertwining integrand is integrable at every argument, the
  same holds for every element of `translateSpan I₁ f`.
- `intertwiningIntegral_mem_translateSpan`: under the same hypotheses the intertwining integral
  maps `translateSpan I₁ f` into `translateSpan J` of the intertwining integral of `f`.

## Proofs

Integrability. By `Submodule.span_induction` it suffices to treat a single translate by
`b = a_{I₁}(t) ∈ 𝔄_{P_{I₁}}`. Put `m = c⁻¹(b) ∈ M_J(𝔸)` and `a = p_J(l_J(m)) ∈ G(𝔸)`; then
`p(b) = n⁻¹ a n` (`IsWeylConjugation.adelic_comp_eq`). Let
`H = (U_J ∩ n U_{I₁} n⁻¹)(𝔸) ≤ U_J(𝔸)` be the closed adelic stabilizer
(`intertwiningAdelicStabilizer`). Conjugation by `l_J(m)` maps `U_J(𝔸)` to itself, since
`U_J` is normal in `P_J` (`conjAdelic`), and preserves `H`
(`conjAdelic_mem_intertwiningAdelicStabilizer_iff`),
so the change of variables `intertwiningIntegralConjugation` for this conjugation transfers
integrability of the integrand of `f` at `a y` to the integrand `v ↦ f_λ(n⁻¹ a v y)`, and `intertwiningIntegrand_unnormalizedAction_eq` identifies
the integrand of the translate with a constant multiple of the latter. Zero, sums and scalar
multiples are immediate.

Span. Again by `span_induction`, consider a translate by `b = a_{I₁}(t)`. Transport `t` to the
positive points `t'` of `A_J` along the split-component isomorphism of
`exists_splitComponent_iso_of_iso`, let `x_Q ∈ 𝔄_{P_J}` be its image and `a = p_J(x_Q)`, so
that again `p(b) = n⁻¹ a n`. Conjugation by `x_Q` through `positiveIntertwiningRadicalAction`
preserves `H` (`positiveIntertwiningRadicalAction_mem_stabilizer`), and
`intertwiningIntegralConjugation` gives `Int f (a y) = R · ∫ f_λ(n⁻¹ a v y) dv`, where `R` is
the Haar factor of the conjugation on `U_J(𝔸)` divided by the Haar factor of its restriction to
`H`, so `R ≠ 0` (`mulEquivHaarChar_pos`). Hence the intertwining
integral of the translate by `b` equals `b^{-λ} R⁻¹` times the translate by `x_Q` of `Int f`,
which lies in `translateSpan J (Int f)`.
