# The simple trace formula comparison between `GL_n` and the units of a central division algebra (statement)

The module defines the proposition
`Langlands.TraceFormula.DivisionAlgebraSimpleTraceComparisonStatement` and four supporting
definitions. The proposition is not proved in this module.

It states the global trace identity of Deligne–Kazhdan–Vignéras between `G = GL_n` and the
unit group `G' = Aˣ` of a central division algebra `A` of dimension `n²` over a number field
`F`. Suppose that a test function `f` on `G(𝔸_F)` has regular elliptic support at two distinct
finite places, that the norm-one average `f'¹` of a test function `f'` on `G'(𝔸_F)` vanishes
at the conjugates of the rational elements with inseparable reduced characteristic
polynomial, that the global orbital integrals of `f` and
`f'` agree at rational elements with the same (reduced) characteristic polynomial, and that
those of `f` vanish at the regular elliptic classes which do not occur in `A`. Then `R'(f')`
on `L²([G'])` and `R_disc(f)` on `L²_disc([G])` are trace class with equal traces.

## Notation from the Library

- `F : Type` is a number field and `A : Type` carries `[DivisionRing A] [Algebra F A]
  [FiniteDimensional F A] [Algebra.IsCentral F A]`, with `Module.finrank F A = n ^ 2`. So `A`
  is a central division algebra over `F`; since `A` is nontrivial, `n ≥ 1`.
- `Gₐ` is a local notation for `FiniteAlgebraUnits.groupScheme (Module.finBasis F A)`, the
  group scheme of units of `A` (the same group scheme as
  `Langlands.Shimura.HarrisClozel.divisionGroup`). `GLₙ` is a local notation for
  `GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of F)`, with local `IsAffine` and
  `Smooth` instances as in `GeneralLinearSimpleTraceFormulaStatement`.
- `AdelicGroupPoints F G` is `G(𝔸_F)`, `RationalGroupPoints F G` is `G(F)`,
  `normOneSubgroup F G` is `G(𝔸_F)¹` (the common kernel of the adelic absolute values of the
  rational characters), `rationalNormOne F G : G(F) → G(𝔸_F)¹` is the diagonal map and
  `rationalNormOneSubgroup F G` its image.
- `canonicalMeasure F G` is the Library's measure on the canonical quotient
  `[G] = A_G G(F) \ G(𝔸_F)` of `Langlands/Global/AdelicRestrictionSplitCentreCanonical.lean`,
  where `A_G` (`canonicalSubgroup F G`) is the group of positive real points of the chosen split
  component of `Res_{F/ℚ} G`. `discreteSpectrum F G hG` is `L²_disc([G])`, the closure of the sum
  of the irreducible closed invariant subspaces of `canonicalL2RightAction`.
- `IsAdelicTestFunction F G h` is the Library's notion of a smooth compactly supported test
  function on `G(𝔸_F)` (Bernstein–Lapid, Example 3.1): `h` is continuous with compact support,
  its archimedean slices are plot-smooth, and it is invariant on the right and on the left under
  an open subgroup of `G(𝔸_{F,f})`. Every finite sum of products of a smooth compactly
  supported function on `G(F_∞)` (smooth along plots, as in `InfinitePlotSmoothFunctions`) and
  a locally constant compactly supported function on `G(𝔸_{F,f})` is such a function.
- `IsRegularElliptic` (`Langlands.JacquetLanglands.RegularElliptic`) means that the
  characteristic polynomial is separable and irreducible. `reducedCharpoly F A a`
  (`Langlands.CentralSimple.reducedCharpoly`) is the reduced characteristic polynomial of
  `a ∈ A`, monic of degree `n`.
- `FiniteAdelicGL.localProjection F n p (AdelicGL.finite F n (adelicHomeomorph F n g))` is the
  component at the finite place `p` of `g ∈ GL_n(𝔸_F)`, and
  `GeneralLinearGroupPoints.rationalEquiv F n` identifies `G(F)` with `GL_n(F)`.
- `twistedCentralizer (MonoidHom.id _) q` is the centralizer of `q` in `G(𝔸_F)¹`,
  `orbitalIntegral q ν h` is `∫ h(x⁻¹ q x) dν(x)` over its left coset space, and
  `IsCompatible C μ μC ν` (`Langlands.QuotientIntegration`) says that `ν` is the quotient of
  `μ` by `μC` in the Weil integration formula; these are used as in
  `GeneralLinearSimpleTraceFormulaStatement`.
- `IsTraceClass` and `operatorTrace` are the Library's trace-class predicate and trace.

## Supporting definitions

- `canonicalIntegratedAction F G hG f hf` is `R(f) φ = ∫ f(g) R(g) φ dg` on
  `L²([G]) = Lp ℂ 2 (canonicalMeasure F G)`, for `Measure.haar` on `G(𝔸_F)`. It is the
  Library's `splitComponentL2IntegratedAction` (so `rationalQuotientL2IntegratedAction`, built
  from `integratedIsometricAction`) at the canonical split components of `Res_{F/ℚ} G` and of
  `G`; the representation it integrates is, by definition, the canonical right regular
  representation `canonicalL2RightAction F G centralSplitTorusCharacter hG`.
- `discreteSpectrum_completeSpace` records that `L²_disc([G])`, a topological closure, is
  complete.
- `canonicalDiscreteIntegratedAction F G hG f hf` is the compression
  `R_disc(f) = P_disc ∘ R(f) ∘ ι_disc` of `R(f)` to `L²_disc([G])`, an operator on that
  subspace, where `P_disc` is the orthogonal projection and `ι_disc` the inclusion.
- `canonicalNormOneAverage F G hG f` is `f¹(x) = ∫_{A_G} f(a x) da` on `G(𝔸_F)¹`, with
  `positivePointMap` for the canonical split component of `G` and its
  `intrinsicPositiveHaarMeasure`. That measure is the Haar measure on `A_G` whose product with
  `Measure.haar` on `G(𝔸_F)¹` is carried to `Measure.haar` on `G(𝔸_F)` by multiplication, so
  `f¹` is the average used by `GeneralLinearSimpleTraceFormulaStatement` and
  `PositiveQuotientTraceComparisonStatement`, written for the canonical split component.
- `finiteAlgebraRationalUnit r` is the unit of `A` given by a rational point `r` of `G'`:
  `FiniteAlgebraUnits.affinePointsEquiv` over `F` gives a unit of `F ⊗[F] A`, then
  `F ⊗[F] A ≃ A`. Composed with `GaloisPointComparison.rationalCoeffEquiv` it is
  `FiniteAlgebraUnits.rationalPointsEquiv`.

## Statement

Fix `F`, `A`, `n` with `finrank F A = n²`, connected-reductivity witnesses
`hD : IsConnectedReductive Gₐ` and `hG : IsConnectedReductive GLₙ`, and finite places
`p₁ ≠ p₂` of `F`. Let `f'` on `G'(𝔸_F)` and `f` on `G(𝔸_F)` satisfy `IsAdelicTestFunction`.
Put `f'¹ = canonicalNormOneAverage F Gₐ hD f'` and `f¹ = canonicalNormOneAverage F GLₙ hG f`.
For a rational point `r` of `G` let `P(r)` be the characteristic polynomial of its matrix, and
for a rational point `r'` of `G'` let `P'(r')` be the reduced characteristic polynomial of
`finiteAlgebraRationalUnit r'`. Assume:

1. **Support at two places.** For every `g ∈ tsupport f`, the components of `g` at `p₁` and at
   `p₂` are regular elliptic.
2. **No inseparable classes for `f'`.** For every rational point `r'` of `G'` with `P'(r')` not
   separable and every `x ∈ G'(𝔸_F)¹`, `f'¹(x⁻¹ r' x) = 0`.
3. **Matching of global orbital integrals.** Let `r` be a rational point of `G` whose matrix is
   regular elliptic and `r'` a rational point of `G'` with `P(r) = P'(r')`. Let `C` and `C'` be
   the centralizers of `r` in `G(𝔸_F)¹` and of `r'` in `G'(𝔸_F)¹`. Take right-invariant
   measures `μC` on `C` and `μD` on `C'`, finite on compacts and positive on nonempty open sets,
   quotient measures `νC` on `C \ G(𝔸_F)¹` and `νD` on `C' \ G'(𝔸_F)¹` compatible with
   `Measure.haar` on the norm-one groups and with `μC`, `μD`, and quotient measures `νR` on
   `(G(F) ∩ C) \ C` and `νRD` on `(G'(F) ∩ C') \ C'` compatible with `μC`, `μD` and the counting
   measures (all quotients with Borel measurable structures). If the covolumes agree,
   `νR(univ) = νRD(univ)`, then `O_r(f¹; νC) = O_{r'}(f'¹; νD)`.
4. **Classes that do not transfer.** Let `r` be a rational point of `G` whose matrix is regular
   elliptic and such that `P(r) ≠ reducedCharpoly F A a` for every `a ∈ A`. For every measure
   `μC` on `C` as above and every quotient measure `νC` compatible with `Measure.haar` on
   `G(𝔸_F)¹` and `μC`, `O_r(f¹; νC) = 0`.

Then there are witnesses `hf'`, `hf` that `f'` and `f` are integrable for `Measure.haar`, the
operator `R'(f') = canonicalIntegratedAction F Gₐ hD f' hf'` is trace class on `L²([G'])`, the
operator `R_disc(f) = canonicalDiscreteIntegratedAction F GLₙ hG f hf` is trace class on
`L²_disc([G])`, and

`operatorTrace R'(f') = operatorTrace R_disc(f)`.

### Associated measures

Both centralizers in hypothesis 3 are the norm-one ideles `𝔸_L¹` of the field
`L = F[X]/(P)`: the centralizer of `r` in `M_n(𝔸_F)` is `𝔸_F ⊗_F F[r]`, that of `r'` in
`𝔸_F ⊗_F A` is `𝔸_F ⊗_F F[r']`, and the determinant and the reduced norm restrict to the norm
`N_{L/F}`. The isomorphism `F[r] ≅ F[r']`, `r ↦ r'`, induces an isomorphism `e` of the two
centralizers which maps rational points onto rational points. Since `L^× \ 𝔸_L¹` is compact,
covolumes are finite and positive, and two Haar measures `μC`, `μD` have the same covolume
exactly when `μD = e_* μC`. Hypothesis 3 is therefore matching for associated Haar measures on
the adelic centralizers, in the norm-one normalization.

### The hypothesis on `f'`

Hypothesis 2 is stated for the average `f'¹`, not for `f'` itself. For `n ≥ 2` the condition
that `f'` vanish on every `G'(𝔸_F)`-conjugate of a rational element with inseparable reduced
characteristic polynomial does not suffice. Write `H = G'(𝔸_F)¹` and `Γ = G'(F)`, a discrete
subgroup of `H` with `Γ \ H` compact (`G'` is anisotropic modulo its centre). Multiplication
`A_{G'} × H → G'(𝔸_F)` is an isomorphism of topological groups; let
`pr : G'(𝔸_F) → H` be the second component of its inverse.

1. *A neighbourhood of `1` met by no other rational class.* Choose a compact `C ⊆ H` with
   `Γ C = H` and a compact neighbourhood `U₀` of `1` in `H`, and for `U ⊆ H` write
   `W(U) = {c u c⁻¹ : c ∈ C, u ∈ U}`. The compact set `W(U₀)` contains only finitely many
   `γ ∈ Γ`. For each `γ ≠ 1` among them the compact set `{c⁻¹ γ c : c ∈ C}` does not contain
   `1`, and `γ ∈ W(U)` exactly when `U` meets this set. So there is a neighbourhood `U ⊆ U₀` of
   `1` with `W(U) ∩ Γ = {1}`. If `x ∈ H`, `r' ∈ Γ` and `x⁻¹ r' x ∈ U`, write `x = γ c` with
   `γ ∈ Γ` and `c ∈ C`. Then `γ⁻¹ r' γ ∈ c U c⁻¹ ⊆ W(U)`, so `γ⁻¹ r' γ = 1` and `r' = 1`.
2. *The test functions.* Fix `a₀ ≠ 1` in `A_{G'}`; then `|Nrd(a₀)| ≠ 1` for the adelic
   absolute value of the reduced norm, since `A_{G'} ∩ H = {1}`. Take `f = 0` and
   `f' = φ_∞ ⊗ 1_K`, where `φ_∞ ≥ 0` is smooth with compact support in a neighbourhood `V` of
   `a₀` in `G'(F_∞)`, `φ_∞(a₀) > 0`, and `K` is a compact open subgroup of `G'(𝔸_{F,f})`.
   Since `pr(a₀, 1) = 1`, `V` and `K` can be chosen with `pr(V × K) ⊆ U` and with `|Nrd|` bounded
   away from `1` on `V × K`.
3. *The literal hypotheses hold.* `|Nrd|` is invariant under conjugation and equals `1` on
   `Γ` (product formula), so `f'` vanishes on every `G'(𝔸_F)`-conjugate of every rational
   element. Hypotheses 1 and 4 hold for `f = 0`. If `f'¹(y) ≠ 0`, then `a y ∈ V × K` for some
   `a ∈ A_{G'}`, so `y = pr(a y) ∈ U`. By step 1, `f'¹(x⁻¹ r' x) = 0` for every `x ∈ H` and
   every rational `r' ≠ 1`. A rational element with separable reduced characteristic
   polynomial is not central when `n ≥ 2`, so all regular orbital integrals of `f'¹` vanish,
   and hypothesis 3 holds with `f = 0`.
4. *The conclusion fails.* `f'¹(1) = ∫_{A_{G'}} f'(a) da > 0`, so hypothesis 2 fails at
   `r' = 1`, whose reduced characteristic polynomial `(X - 1)^n` is inseparable. In the trace
   formula for the compact quotient `Γ \ H` only the identity class contributes, so
   `tr R'(f') = vol(Γ \ H) · f'¹(1) > 0`, while `tr R_disc(0) = 0`.

Hypothesis 2 holds when `f'` vanishes at every product `a x⁻¹ r' x` with `a ∈ A_{G'}`,
`x ∈ H` and `r'` rational with inseparable reduced characteristic polynomial. This is the
case, for instance, when at some finite place `v` the function `f'` vanishes at every point
whose component at `v` has inseparable reduced characteristic polynomial: `A_{G'}` has
trivial components at the finite places, so the component of `a x⁻¹ r' x` at `v` is a
conjugate of `r'`. Hypothesis 1 needs no such change, because it concerns finite places only.

## Why it is true

1. *The division algebra side.* `A` is a division algebra, so `G'` has no proper parabolic
   subgroup over `F`: `L²([G'])` is its own cuspidal subspace and `[G']` is compact. Fix a
   compact open subgroup `K` of `G'(𝔸_{F,f})` under which `f'` is invariant on the right; as
   `f'` has compact support, `f' = Σ_i f'(·, x_i) ⊗ 1_{x_i K}` for finitely many `x_i`. So
   the average of `f'` over `A_{G'}` lies in the test space
   `C_c^∞(A_{G'} \ G'(F_∞)) ⊗ C_c^∞(G'(𝔸_{F,f}))` of Getz–Hahn, and `R'(f')` is its operator.
   By the theorem of Gelfand and Piatetski-Shapiro (Getz–Hahn, Theorem 9.1.2), `R'(f')` is
   trace class. `PositiveQuotientTraceComparisonStatement` (proved as
   `positiveQuotientTraceComparison`) passes from `R'(f')` to the operator of `f'¹` on
   `L²(G'(F) \ G'(𝔸_F)¹)`, which is then trace class with the same trace. With this input, the
   Selberg trace formula for a compact quotient applies. It is the case of trivial twist of
   `AbstractSimpleTwistedTraceFormulaStatement`, proved as `abstractSimpleTwistedTraceFormula`,
   which assumes trace class. It gives `tr R'(f')` as a finite sum, over the conjugacy classes
   of `G'(F)`, of covolumes times orbital integrals of `f'¹`. Every element of `A` is
   semisimple. By hypothesis 2, only the classes with separable reduced characteristic
   polynomial contribute.
2. *The `GL_n` side: trace class.* `R_disc(f)` is the operator of the `A_G`-average of `f`, a
   function in `C_c^∞(A_G \ G(𝔸_F))` as in step 1, on the discrete spectrum. It is trace class
   by Getz–Hahn, Theorem 9.1.4. That theorem is due to Müller for `K_∞`-finite functions, and
   to Ji and Müller in general. Under the identification of `L²([G])` with
   `L²(G(F) \ G(𝔸_F)¹)`, `R_disc(f)` is the operator of `f¹` on the discrete spectrum.
3. *The `GL_n` side: the simple trace formula.* Arthur's Corollary 7.5 states, for `GL(n)` and
   a function `h` of the Hecke algebra (finite sums of factorizable, `K`-finite, smooth
   compactly supported functions) that is cuspidal at two places,

   `Σ_{γ ∈ {G(F)_ell}} vol(G(F, γ) A_{G,∞} \ G(𝔸, γ)) ∫_{G(𝔸, γ) \ G(𝔸)} h(x⁻¹ γ x) dx
     = Σ_{t ≥ 0} tr R_disc,t(h)`,

   where `A_{G,∞}` is `A_G` and `R_disc,t` acts on `L²_disc,t(G(F) A_{G,∞} \ G(𝔸))`. Its terms
   depend only on the restriction of `h` to `G(𝔸_F)¹` (p. 504). So for a function
   restricting to `f¹` this is an identity between norm-one covolumes and orbital integrals of
   `f¹` and the trace of `f¹` on the discrete spectrum. The spaces `L²_disc,t` are orthogonal
   invariant summands of `L²_disc`, so the sum over `t` is the trace of the trace-class
   operator of step 2. Arthur calls a function cuspidal at `v` (p. 538) if it is a finite sum
   of factorizable functions whose components at `v` satisfy `f_{v,M} = 0` for every proper
   Levi subgroup `M`. This is implied by the vanishing of the orbital integrals of these
   components at the regular elements of `G(F_v)` that are not elliptic. That vanishing holds
   when the components at `v` are supported in the regular elliptic set, which is open,
   invariant under conjugation, and contains no non-elliptic element.

   To reach `f¹`, choose `ψ ∈ C_c^∞(A_G)` with `ψ(1) = 1` and put `h(a y) = ψ(a) f¹(y)` for
   `a ∈ A_G` and `y ∈ G(𝔸_F)¹`. Then `h` is smooth with compact support and restricts to `f¹`
   on `G(𝔸_F)¹`. The support of `f¹` lies in the image of `tsupport f` under the projection
   `G(𝔸_F) → G(𝔸_F)¹`, a compact set. Since `A_G` has trivial components at the finite
   places, neither this projection nor multiplication by `A_G` changes the components there.
   So every point of the support of `h` has regular elliptic components at `p₁` and `p₂`.

   Fix a compact open subgroup `K_f = Π_v K_v` of `G(𝔸_{F,f})` under which `f`, hence `h`, is
   invariant on both sides. As `h` has compact support, `h = Σ_i h(·, x_i) ⊗ 1_{x_i K_f}` for
   finitely many `x_i ∈ G(𝔸_{F,f})`. Each nonzero summand has support in that of `h`, so its
   components at `p₁` and `p₂` are indicator functions of cosets contained in the regular
   elliptic set. The archimedean factors are smooth but need not be `K_∞`-finite. Replace `h`
   by `h_N = Σ_{σ, τ ∈ S_N} e_σ * h * e_τ`, where `S_N` are finite sets of irreducible
   representations of `K_∞` increasing to all of them and `e_σ` is the idempotent of `σ`, and
   let `f_N` be the restriction of `h_N` to `G(𝔸_F)¹`. These functions are `K_∞`-finite and
   have the same finite-place components, so the support conditions at `p₁` and `p₂` are
   preserved. The supports of the `f_N` lie in the fixed compact set `K_∞ · supp f¹ · K_∞`,
   and the `f_N` converge to `f¹` uniformly.

   On the geometric side, only finitely many rational semisimple classes meet a fixed compact
   set, because their characteristic polynomials are rational points of a compact subset of
   `𝔸_F^n`. Each elliptic orbit is closed, so at each of these finitely many classes the
   orbital integrals of the `f_N` tend to that of `f¹`. On the spectral side,
   `R_disc(f_N) = P_N R_disc(f¹) P_N` with orthogonal projections `P_N` onto sums of
   `K_∞`-isotypic subspaces, converging strongly to the identity. Since `R_disc(f¹)` is trace
   class, `R_disc(f_N) → R_disc(f¹)` in trace norm. The result is that `tr R_disc(f)` is the
   sum, over the rational classes regular elliptic at `p₁` and `p₂`, of covolumes times
   orbital integrals of `f¹`.
4. *Matching.* A field `L` of degree `n` over `F` embeds in `A` exactly when it splits `A`.
   Two elements of `A` (or of `GL_n(F)`) with the same separable irreducible characteristic
   polynomial are conjugate (Skolem–Noether, rational canonical form). So the regular classes
   of `G'(F)` correspond bijectively to the regular elliptic classes of `GL_n(F)` whose
   characteristic polynomial is a reduced characteristic polynomial of `A`. Hypothesis 3
   matches the corresponding terms (the covolumes agree for associated measures), and
   hypothesis 4 removes the other regular elliptic classes of `GL_n(F)`. A regular class of
   `G'(F)` whose partner is not regular elliptic at `p₁` contributes `0`: by hypothesis 3 its
   orbital integral equals that of `f¹` at the partner, which vanishes by hypothesis 1.

## Sources and provenance

- Deligne–Kazhdan–Vignéras, *Représentations des algèbres centrales simples `p`-adiques*, in
  Bernstein–Deligne–Kazhdan–Vignéras, *Représentations des groupes réductifs sur un corps
  local* (1984), registered `bdkv-1984-representations-local-field`. §A.1, printed pp. 41–43:
  the simple version of the trace formula, with a fixed unitary central character `ω`,
  `L²(G, ω)`, test functions that are products of local functions, a supercuspidal condition
  and support in the regular elliptic set at one place. §B.1.a, printed p. 78: for
  `G = GL(n, F)` and `G' = GL(m, D)` with local components equal outside the ramified places,
  a supercuspidal component at one place, support in the regular elliptic elements at another,
  and orbital integrals of `φ` equal to the extension by `0` of those of `φ'` for compatible
  measures on the centralizers, one gets `trace ρ(φ) = trace ρ'(φ')`. §C.1, printed pp. 90–91:
  Théorème (?) (the simple form of `trace ρ_d(φ)` on the discrete part `L²_d(G, ω)` when, at
  every non-elliptic `γ ∈ G(F)`, two local components of `φ` have vanishing orbital integrals),
  and the resulting comparison `trace ρ_d(φ) = trace ρ'(φ')` in C.1.c.
- Arthur, *The invariant trace formula II. Global theory* (1988), registered
  `arthur-1988-invariant-trace-formula-II`. Printed p. 504: the terms of the trace formula
  depend only on the restriction of the test function to `G(𝔸)¹`. Printed p. 538: functions
  cuspidal at a place. Corollary 7.5, printed p. 541: the simple trace formula for `GL(n)` and
  a function cuspidal at two places, equating the elliptic geometric terms with
  `Σ_t tr R_disc,t(f)` on `L²_disc,t(G(F) A_{G,∞} \ G(𝔸))`.
- Arthur–Clozel, *Simple algebras, base change, and the advanced theory of the trace formula*
  (1989), registered `arthur-clozel-1989-base-change`, Chapter 2, §5, Theorem A (printed
  p. 108) and §9, Theorem B (printed p. 134): the term-by-term identification of the geometric
  and spectral sides of the full invariant trace formulas of `GL(n)` and of an inner form,
  with representations of the norm-one groups `M(𝔸)¹`.
- Clozel, *Représentations galoisiennes associées aux représentations automorphes autoduales de
  `GL(n)`* (1991), registered `clozel-1991-selfdual-galois`, printed p. 107 and Théorème 3.3,
  printed p. 108: the global correspondence between `D^×` and `GL(n)` deduced from the trace
  formula comparison of Arthur–Clozel, Theorem B.
- Getz–Hahn, *An introduction to automorphic representations* (2024), registered
  `getz-hahn-2024-automorphic-representations`. §18.4, Corollary 18.4.1 and (18.25)–(18.28),
  printed p. 485: the simple trace formula on `A_G \ G(𝔸_F)`, with orbital integrals
  `O_γ(f)` and volumes `τ(C_γ) = vol(A_G C_γ(F) \ C_γ(𝔸_F))`. §9.1, Theorem 9.1.2, printed
  p. 241: `R_cusp(f)` is trace class for `f ∈ C_c^∞(A_G \ G(𝔸_F))` (Gelfand and
  Piatetski-Shapiro). Theorem 9.1.4, printed p. 242: over a number field the restriction of
  `R(f)` to the discrete spectrum is trace class (Müller; Ji and Müller).

This is derived content. The proposition isolates the global comparison of the two simple trace
formulas for the Library's group schemes `Aˣ` and `GL_n`, over every number field, for every
central division algebra and every pair of distinct finite places. It relates to the sources
as follows.

- *Normalization.* The comparison of Deligne–Kazhdan–Vignéras fixes a unitary character `ω`
  of `Z(F) \ Z(𝔸_F)` and works in `L²(G, ω)`, with test functions compactly supported modulo
  the centre. This statement instead uses the canonical quotient `A_G G(F) \ G(𝔸_F)` by the
  positive real points of the split centre, the quotient of Getz–Hahn (§9.1, §18.4). The
  norm-one averages `f¹`, `f'¹` and the orbital integrals and covolumes on `G(𝔸_F)¹` match
  Arthur's Corollary 7.5, whose terms depend only on the restriction to `G(𝔸)¹`, and the
  norm-one representations of Arthur–Clozel, Theorem B.
- *Test functions and matching.* Deligne–Kazhdan–Vignéras take factorizable test functions
  with associated local components: local matching of orbital integrals at every place, by
  extension by `0` from `G'`, for compatible centralizer measures. This statement instead takes
  as hypotheses the global matching and vanishing of the normalized adelic orbital integrals
  (hypotheses 3 and 4). The association of centralizer measures is expressed by equal
  covolumes of the rational points.
- *The simple form.* Deligne–Kazhdan–Vignéras §A.1 and §B.1 use a supercuspidal component at
  one place and regular elliptic support at another. Their §C.1 asks instead that, at every
  non-elliptic rational class, the orbital integrals of two local components vanish. Regular
  elliptic support of `f` at two fixed finite places `p₁`, `p₂` is a sufficient condition for
  these two vanishings. It is also sufficient for cuspidality at two places in Arthur's
  Corollary 7.5, whose conclusion concerns the whole discrete spectrum, as here.
- The condition on `f'` at inseparable classes is imposed on the average `f'¹`, for the reason
  explained above.
