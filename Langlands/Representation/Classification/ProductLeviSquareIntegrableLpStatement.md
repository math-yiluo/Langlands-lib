# Discrete-series coefficients of block Levis below exponent two

`Langlands.GLProductLeviSquareIntegrableLpStatement.{uF,uW}` is a proposition
definition. It proves nothing. It states that the absolute matrix coefficients of
an irreducible representation of an actual standard block Levi that is square
integrable modulo the centre are integrable on the central quotient to some
power strictly below two. This is a derived statement. It is extracted from the
proof of Waldspurger 2003, Corollary III.1.2, as explained below. It is the analytic input of the
proof of `Langlands.GLTemperedDiscreteSeriesIsotypicStatement` in
[TemperedDiscreteSeriesIsotypicStatement](TemperedDiscreteSeriesIsotypicStatement.md).
There, the integral of a coefficient of `σ` against a coefficient of a tempered
`ρ` must converge absolutely, and Hölder's inequality with the exponents `r < 2`
and `r / (r - 1) > 2` gives this.

## Exact statement and binders

The binders up to `σ` are those of `GLLeviDiscreteSeriesTemperedStatement` in
[DiscreteSeriesJacquetStatement](DiscreteSeriesJacquetStatement.md), in the same
order. The proposition quantifies over every prime `p`, every
`F : PadicField p`, its actual topological data `T` with topology `T.topology`,
a positive rank `n` and a standard block shape `B` of `n`. Put
`M = B.Levi F.Carrier = ∏ i, GL_(B.size i)(F)` with the proved instance
`T.leviTopologicalGroup B`, and `Q = M / Z(M)`, the quotient by the actual centre
`Subgroup.center M`. The proposition then quantifies over every Borel measurable
structure on `Q`, every Haar measure `μ` on `Q`, a complex vector space
`W : Type uW` and an actual representation `σ : Representation ℂ M W`. The
hypotheses are

```text
Representation.IsIrreducible σ, IsSquareIntegrableModCenter σ μ.
```

The conclusion is

```lean
∀ (c : UnitaryCentralCharacter σ) (ℓ : SmoothDual σ) (w : W),
  ∃ r : ℝ, 1 < r ∧ r < 2 ∧
    MeasureTheory.MemLp (c.coefficientNorm ℓ w) (ENNReal.ofReal r) μ
```

`UnitaryCentralCharacter σ` is the Library structure of
[ModuloCenter](../MatrixCoefficient/ModuloCenter.md). It is a homomorphism
`Z(M) →* ℂˣ` with open kernel and values of norm one, by which the centre acts on
`W`. The function `c.coefficientNorm ℓ w : Q → ℝ` sends the class of `g` to
`‖ℓ (σ g w)‖`. It is well defined because the centre acts by unitary scalars,
and `UnitaryCentralCharacter.coefficientNorm_eq` shows that it does not depend
on `c`. So quantifying over every `c` is the same as quantifying over one `c`. The functional
`ℓ` ranges over the smooth dual `SmoothDual σ` (the smooth vectors of the
algebraic dual) and `w` over all of `W`. These are exactly the coefficients of
the hypothesis `IsSquareIntegrableModCenter σ μ`, which asserts admissibility
and, for some unitary central character, `MemLp (coefficientNorm ℓ w) 2 μ` for
every such pair.

The exponent `r` may depend on the coefficient `(ℓ, w)`; no uniform exponent is
claimed. The bound `1 < r` costs nothing mathematically: membership in `L^r` and
in `L^2` gives membership in every `L^s` with `r ≤ s ≤ 2`. Nothing is claimed for
non-irreducible representations, other groups, or any other quotient than the
actual central quotient `Q`. The universes `uF` and `uW` are independent.

## Provenance

Waldspurger 2003 (`waldspurger-2003-plancherel`; PDF page = printed page − 234)
treats an admissible representation `π` of a reductive p-adic group `G`
with unitary central character. Section III.1 (printed p.263) defines `π` to be
square integrable when all of its coefficients are square integrable on
`A_G \ G`. Proposition III.1.1 (p.263, citing Casselman's Theorem 4.4.6) shows
that this holds exactly when every exponent `χ` of every Jacquet module `π_P`
satisfies `Re(χ) ∈ ⁺a_P^{G*}`, the open positive cone. Corollary III.1.2
(p.263) then states the Schwartz–Harish-Chandra bound
`|f(g)| ≤ c Ξ(g) (1 + σ(g))^{-r}` on `G¹` for every coefficient `f` and every `r`.

The statement here is not that corollary. The corollary's bound alone does not
give integrability of `|f|^r` for `r < 2`. The statement uses the stronger
estimate obtained in the corollary's proof (printed p.264). Because every
exponent lies in the open cone, there are `C₃ > 0` and `ε > 0` with
`|χ(a)| ≤ C₃ q^{-ε σ(a)}` on the closed positive chamber of `A_M ∩ G¹`. With
`δ_P(a)^{1/2} ≤ C₁ Ξ(a)` and the polynomial factors this gives the exponential
decay `|f(a)| ≤ c δ_0(a)^{1/2} q^{-ε' σ(a)}` on the positive chamber of the
maximal split torus modulo `A_G`, for some `ε' > 0`. Waldspurger I.1(4)
(printed p.241, PDF p.7) gives the Cartan decomposition of `G` as the disjoint
union of the double cosets `K a K` over the closed chamber modulo the compact
group `M_0^1`. I.1(5) (same page) gives uniform two-sided volume bounds
`C₁ δ_0(a)^{-1} ≤ vol(K a K) ≤ C₂ δ_0(a)^{-1}`. The volume is not a constant
multiple of `δ_0(a)^{-1}`: for `GL_2(F)` with `vol(GL_2(O_F)) = 1`, the double
coset of `diag(ϖ, 1)` has volume `q + 1`, while `δ_0(diag(ϖ, 1))^{-1} = q`.
Only the upper bound `vol(K a K) ≤ C₂ δ_0(a)^{-1}` is used. The coefficient `f`
is bi-invariant under an open compact subgroup `H` of `K`, so its values on
`K a K` are values at `a` of the finitely many coefficients obtained by
translating with representatives of `K / H`; the decay bound therefore holds on
all of `K a K` with one constant. With these bounds, `∫ |f|^r`
is dominated by a constant multiple of the lattice sum

```text
Σ_{a ∈ A⁺ / A_G} δ_0(a)^{r/2 - 1} q^{-r ε' σ(a)}.
```

Since `δ_0(a)^{-1} ≤ q^{C σ(a)}` for some constant `C` and the number of lattice
points with `σ(a) = k` grows polynomially in `k`, the sum converges as soon as
`(1 - r/2) C < r ε'`, that is, for every `r < 2` close enough to `2`.

Waldspurger's bounds are on `G¹`. The subgroup `A_G G¹` has finite index in
`G`, and a translate of a coefficient is again a coefficient, so bounds on `G¹`
give integrability on `A_G \ G`. For `G = M = ∏ GL_(n_i)(F)` the split
component `A_M` of the centre is the full centre `Z(M) = ∏ F^×`, so `A_M \ M`
is the quotient `Q` used here. The Library's
`IsSquareIntegrableModCenter σ μ` is the square-integrability of Waldspurger's
III.1 for the actual Haar measure `μ` on `Q`; the choice of Haar measure only
rescales integrals. Irreducibility of `σ` is kept as a hypothesis because it is
the case needed by the consumer, and it makes the Jacquet modules finitely
generated, so that their exponent sets are finite.
