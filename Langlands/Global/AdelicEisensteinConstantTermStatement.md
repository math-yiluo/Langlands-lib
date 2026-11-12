# Constant terms of Eisenstein series

Module `Langlands.Global.AdelicEisensteinConstantTermStatement` states
`Langlands.Global.EisensteinConstantTermStatement` as a proposition
definition. It supplies no proof. The statement expresses the constant term of
an Eisenstein series along a parabolic `Q` as a sum, over representatives `w`
of `Q(F) \ G(F) / P(F)`, of Eisenstein-type sums over `Q_w(F) \ Q(F)` of
intertwining integrals of constant terms of `φ`. This is the formula (6.17)
of the geometric lemma of Bernstein–Lapid. The module also defines six
helpers in namespace `Langlands.Global.AdelicGroupPoints`.

## Sources

- J. Bernstein and E. Lapid, *On the meromorphic continuation of Eisenstein
  series*, J. Amer. Math. Soc. 37 (2024), registered as
  `bernstein-lapid-2024-meromorphic-continuation-eisenstein`.
  - §6.10, Geometric lemma, journal p.208 (PDF page 22), formula (6.17):
    for `φ ∈ 𝒜_P`, `λ` with `⟨Re λ, α^∨⟩ ≫ 0` for all `α ∈ Δ_P` (fixed at
    the start of §6.9, p.207, PDF page 21), `ψ = E(φ, λ)` and every standard parabolic `Q`,
    `C_{G,Q} ψ = ∑_{w ∈ _QW_P} E^Q(M(w, λ)(C_{P,P_w} φ), wλ)`, where `E^Q`
    sums over `Q_w(F) \ Q(F)` instead of `P(F) \ G(F)`. BL add that the
    intertwining operator (from `𝒜_{P_w}` to `𝒜_{Q_w}`) and the Eisenstein
    series (from `𝒜_{Q_w}` to `𝒜_Q`) are taken in their range of
    convergence. The proof, pp.208–209 (PDF pages 22–23), unfolds
    `ψ(g) = ∑_w ∑_{γ ∈ (Q ∩ wPw⁻¹)(F) \ Q(F)} φ_λ(w⁻¹ γ g)` by the Bruhat
    decomposition, integrates over `U_Q(F) \ U_Q(𝔸)` and identifies the inner
    integral with `[M(w, λ) C_{P,P_w} φ]_{wλ}(γ g)`, using
    `M(w, λ)φ'_λ(g) = ∫_{(U_Q ∩ wU_{P_w}w⁻¹)(𝔸) \ U_Q(𝔸)} φ'_λ(w⁻¹ u g) du`
    for `φ' ∈ 𝒜_{P_w}`.
  - §6.7, Bruhat decomposition, pp.206–207 (PDF pages 20–21): `_QW_P` is a
    set of representatives of `Q(F) \ G(F) / P(F)`; for `w ∈ _QW_P`,
    `M_P ∩ w⁻¹M_Q w` and `M_Q ∩ wM_P w⁻¹` are the Levi subgroups of standard
    parabolics `P_w ⊆ P` and `Q_w ⊆ Q`; `Q ∩ wPw⁻¹ ⊆ Q_w`,
    `U_Q ∩ wPw⁻¹ = U_Q ∩ wU_{P_w}w⁻¹` and
    `U_{Q_w} = (M_Q ∩ wU_P w⁻¹) ⋉ U_Q = (U_{Q_w} ∩ wU_{P_w}w⁻¹) U_Q`.
  - §6.2, p.201 (PDF page 15): for `Q ⊆ P`,
    `C_{P,Q} φ(g) = ∫_{U_Q(F) \ U_Q(𝔸)} φ(u g) du`.
  - §2.2, p.191 (PDF page 5), footnote: the Haar measure on `V(𝔸)` is
    normalized by `vol(V(F) \ V(𝔸)) = 1` for every unipotent `V`.
- C. Mœglin and J.-L. Waldspurger, *Spectral decomposition and Eisenstein
  series*, 1995, registered as `moeglin-waldspurger-1995-spectral-decomposition`,
  chapter file `06.1_pp_78_100_Definitions.pdf`, II.1.7, printed pp.91–93
  (PDF pages 14–16). For cuspidal `φ` and `⟨Re π, α^∨⟩ > ⟨ρ_P, α^∨⟩`, the
  Proposition gives the constant term of `E(φ, π)` along a standard
  parabolic `P'`. The proof rests on the Bruhat decomposition
  `G(k) = ⊔_w P(k) w⁻¹ P'(k)`. It exchanges sum and integral by absolute
  convergence: formula (4) bounds the same unfolded expression with `|φ|`.
  Cuspidality is used only after this unfolding. Bernstein–Lapid call their
  lemma a straightforward generalization of this computation.

## Helpers

All in namespace `Langlands.Global.AdelicGroupPoints`.

- `rationalImage F j`, for `j : H → G`: the image of `H(F)` in `G(𝔸)`,
  namely the range of `map F H G j` composed with the principal map
  `rational F H`. For `j = l ≫ p` it is the published
  `parabolicLeviRationalImage F p l`, by the same formula.
- `RelativeRationalCosets F j' j`, for `j' : H' → G` and `j : H → G`: the
  quotient of `rationalImage F j` by the right-coset relation of
  `(rationalImage F j').subgroupOf (rationalImage F j)`, that is
  `H'(F) \ H(F)` when `H'(F) ⊆ H(F)`.
- `subgroupConstantTerm F j f g`, for a closed immersion `j : H → G` of an
  affine `H`, a function `f : G(𝔸) → ℂ` and `g ∈ G(𝔸)`: the Bochner integral
  of `x ↦ f(h_x g)` over `H(F) \ H(𝔸)`, where `h_x` is the chosen
  representative `Quotient.out x`. The measure is
  `AdelicSubgroupPoints.normalizedRationalQuotientHaarMeasure` for the
  subgroup functor `SubgroupFunctor.range j`. Closedness of `H(𝔸)`
  (`isClosed_adelicPoints_range`) is what constructing the Haar measure of
  `H(𝔸)` and the quotient Haar measure `μ` of `H(F) \ H(𝔸)` needs. The
  normalized measure is `μ(univ)⁻¹ • μ`, a totalized normalization:
  - it has total mass one when `μ` is finite, in particular when
    `H(F) \ H(𝔸)` is compact (Library theorem
    `normalizedRationalQuotientHaarMeasure_isProbabilityMeasure`);
  - when `μ` has infinite mass it is the zero measure, and then
    `subgroupConstantTerm` is `0` for every `f`. For example, for
    `H = G = G_m` and `j = 𝟙` the idele class group has infinite volume.

  Closedness alone does not give finite volume. In this module the helper is
  only applied to unipotent radicals `H`. For those, `H(F) \ H(𝔸)` is compact,
  so the measure has mass one: BL's normalization (§2.2, footnote 1). The
  integral is `0` where the integrand is not integrable. For `f` left
  `H(F)`-invariant the integrand does not depend
  on the representatives. For `f` continuous and left `G(F)`-invariant it
  coincides with the published
  `Langlands.Automorphic.GroupSchemeFunctions.constantTerm` for this
  measure: the two integrands agree pointwise. That remark is explanatory
  and not proved here.
- `parameterRestrict f`, for `f : H' → H`: the `ℂ`-linear map
  `X^*(H) ⊗ ℂ → X^*(H') ⊗ ℂ` induced by `characterRestrict f`, that is
  `χ ↦ χ ∘ f` on characters. It has the same form as `weylParameter`.
- `IsDoubleCosetRepresentatives F q p w`, for `q : Q → G`, `p : P → G` and a
  family `w : I → (points of G over the base)`: every `z ∈ G(F)` (the
  published `rationalSubgroup F G`) can be written as `x w_i y` with
  `x ∈ rationalImage F q`, `y ∈ rationalImage F p` for exactly one index
  `i`. Here `w_i` is `innerAdelicPoint F G (w i)`, which is a rational point
  (`innerAdelicPoint_eq_rational`). Uniqueness of `i` makes the `w_i` a
  system of representatives of `Q(F) \ G(F) / P(F)` without repetitions.
- `IsGeometricLemmaDatum p iU q iV f g' w`, for `p : P → G` with
  `iU : U → P`, `q : Q → G` with `iV : V → Q`, `f : P' → P`, `g' : Q' → Q`
  and a point `w`. It has two fields:
  - `rationalImage_left`:
    `rationalImage F (f ≫ p) = (rationalImage F p ⊓ w⁻¹ (rationalImage F q) w) ⊔ rationalImage F (iU ≫ p)`;
  - `rationalImage_right`:
    `rationalImage F (g' ≫ q) = (rationalImage F q ⊓ w (rationalImage F p) w⁻¹) ⊔ rationalImage F (iV ≫ q)`.

  Here conjugates are images under `MulAut.conj`, `⊓` and `⊔` are taken in
  the subgroup lattice of `G(𝔸)`, and `w` stands for `innerAdelicPoint F G w`.
  So `P'(F) = (P(F) ∩ w⁻¹ Q(F) w) U(F)` and `Q'(F) = (Q(F) ∩ w P(F) w⁻¹) V(F)`.
  The join is the product set because `U(F)` and `V(F)` are normal in
  `P(F)` and `Q(F)`.

## Existing objects used

- `IsIwasawaCompact`, `hK.parameterTwist` and `hK.eisensteinSeries`
  (modules `Langlands.Global.AdelicIwasawaHeight` and
  `Langlands.Global.AdelicEisensteinSeries`): `φ_λ(g) = φ(g) m_P(g)^λ` and
  `E(g, φ, λ) = ∑_{γ ∈ P(F) \ G(F)} φ_λ(γ g)`, totalized.
- `hK.intertwiningIntegrand`, `hK.intertwiningIntegral` and
  `intertwiningMeasure` (module `Langlands.Global.AdelicIntertwiningOperator`):
  for a parabolic `P_i` with unipotent radical `U_i`, a closed subgroup
  `j : V_i → G` and a point `w`, the integral
  `∫_{(V_i(F) ∩ w U_i(𝔸) w⁻¹) \ V_i(𝔸)} φ'_λ(w⁻¹ v g) dv`. The Haar measure
  of `V_i(𝔸)` is the Library's `AdelicSubgroupPoints.normalizedHaarMeasure`.
  This is Haar measure scaled by `μ(univ)⁻¹`, where `μ` is the quotient Haar
  measure of `V_i(F) \ V_i(𝔸)`, with the same totalized normalization as
  `subgroupConstantTerm` (zero if `μ` has infinite mass). Here `V_i` is
  always a unipotent radical, so `V_i(F) \ V_i(𝔸)` is compact. The
  normalization is then `vol(V_i(F) \ V_i(𝔸)) = 1`, as in BL §2.2. For `V_i` the
  unipotent radical of `Q_i` this is `[M(w, λ)φ']_{wλ}(g)`.
- The binders and hypotheses of
  `Langlands.Global.EisensteinAbsoluteConvergenceStatement` and
  `Langlands.Global.IntertwiningAbsoluteConvergenceStatement`, including
  `ParabolicRootPresentation.IsRegularParameter` (module
  `Langlands.Global.AdelicEisensteinConvergenceStatement`).

## Statement

The data for `G`, `P`, `M`, `U`, `A`, `p`, `iU`, `l`, `a`, `r`, `hA`, `hT`,
`K`, `hK`, `rho`, `hsmooth`, `hcalc` and `φ` are those of
`EisensteinAbsoluteConvergenceStatement`, with the same hypotheses: `G`
connected reductive, `iU` a geometric unipotent radical of `P`, `K` maximal
compact with `P(𝔸)K = G(𝔸)`, `rho` a closed embedding, and `φ` an
automorphic form on `U(𝔸)M(F) \ G(𝔸)` for the archimedean part of `K`. As
in `IntertwiningAbsoluteConvergenceStatement`, `q : Q → G` is a parabolic
with geometric unipotent radical `iV : V → Q`, `V` affine and `iV ≫ q` a
closed immersion. In addition the statement quantifies:

- a finite type `I` (in universe `u`) and points `w : I → (Spec F → G)` with
  `IsDoubleCosetRepresentatives F q p w`;
- for each `i`, affine group schemes `P' i`, `U' i`, `V' i` and a group
  scheme `Q' i`, with maps `f i : P' i → P`, `iU' i : U' i → P' i`,
  `g' i : Q' i → Q` and `iV' i : V' i → Q' i`; the maps `f i ≫ p`,
  `iU' i ≫ f i ≫ p` and `iV' i ≫ g' i ≫ q` are closed immersions;
- hypotheses: `f i ≫ p` and `g' i ≫ q` are parabolic subgroups of `G`;
  `iU' i` and `iV' i` are geometric unipotent radicals;
  `IsGeometricLemmaDatum p iU q iV (f i) (g' i) (w i)`, so `P' i` is
  `P_{w_i}` and `Q' i` is `Q_{w_i}`;
- `hK' : ∀ i, IsIwasawaCompact (f i ≫ p) K`, that is `P_{w_i}(𝔸)K = G(𝔸)`.

Conclusion: there is a real `R` such that for every `λ ∈ X^*(P) ⊗ ℂ` with
`r.IsRegularParameter hA hT R λ` and every `g ∈ G(𝔸)`, writing
`φ_i = subgroupConstantTerm F (iU' i ≫ f i ≫ p) φ` (the constant term
`C_{P,P_{w_i}} φ`), `λ_i = parameterRestrict (f i) λ`,
`j_i = iV' i ≫ g' i ≫ q`, and `γ_c` for the chosen representative in `Q(F)`
of a class `c ∈ RelativeRationalCosets F (g' i ≫ q) q`, that is of
`Q_{w_i}(F) \ Q(F)`:

1. for every `i` and `c`, the integrand
   `(hK' i).intertwiningIntegrand (iU' i) j_i (w i) φ_i λ_i (γ_c g)` is
   integrable for `intertwiningMeasure F (f i ≫ p) (iU' i) j_i w_i`;
2. for every `i`, the function
   `c ↦ (hK' i).intertwiningIntegral (iU' i) j_i (w i) φ_i λ_i (γ_c g)` is
   summable;
3. `subgroupConstantTerm F (iV ≫ q) (hK.eisensteinSeries φ λ) g` equals
   `∑ i, ∑' c, (hK' i).intertwiningIntegral (iU' i) j_i (w i) φ_i λ_i (γ_c g)`.

The twist inside the integral is `(φ_i)_{λ_i}(x) = φ_i(x) m_{P_{w_i}}(x)^{λ_i}`,
with the Iwasawa height of `P_{w_i}` given by `hK' i`.

## Correspondence with the source

- The summands. By definition
  `E^Q(ψ', μ)(g) = ∑_{γ ∈ Q_w(F) \ Q(F)} ψ'_μ(γ g)`, and for
  `φ' = C_{P,P_w} φ ∈ 𝒜_{P_w}` the function `[M(w, λ)φ']_{wλ}` is the
  intertwining integral over `(V_w(F) ∩ wU_w(𝔸)w⁻¹) \ V_w(𝔸)`, with `U_w`
  and `V_w` the unipotent radicals of `P_w` and `Q_w`. This is the published
  `intertwiningIntegral` with `j = iV' i ≫ g' i ≫ q`. So the double sum in
  conclusion 3 is BL's right side of (6.17), written out. It uses neither
  the Levi subgroups of `P_w` and `Q_w`, nor the parameter `wλ`, nor an
  Iwasawa hypothesis for `Q_w`. The parameter `wλ` disappears by
  cancellation: `E^Q` twists `M(w, λ)φ'` by `m_{Q_w}^{wλ}`, and `M(w, λ)φ'` is
  `m_{Q_w}^{-wλ}` times the integral.
- Two integration domains for `M(w, λ)`. BL write `M(w, λ)` on `𝒜_{P_w}` as
  an integral over `U_{Q_w}(𝔸)` and identify it with one over `U_Q(𝔸)`
  using Lemma 6.7 (3). The statement uses the `U_{Q_w}` form, which is the
  definition.
- Parameters. BL regard `X_P` as a subgroup of `X_{P_w}` by restriction
  (§6.10, first sentence). This is `parameterRestrict (f i)`. The equality
  `m_{P_w}(x)^{λ|_{P_w}} = m_P(x)^λ` holds when `K` is an Iwasawa subgroup
  for both. The formula also uses `C_{P,P_w}(φ_λ) = (C_{P,P_w} φ)_λ`, which
  holds because characters of `P` are trivial on `U_w(𝔸)`.
- Representatives. BL sum over the Bruhat representatives `_QW_P` and take
  `P`, `Q` standard. Here the representatives are any rational points
  forming a system of representatives of `Q(F) \ G(F) / P(F)`. The groups
  `P_w` and `Q_w` are characterized through their rational points. This
  generality follows from BL's case, for two reasons:
  1. For `w ∈ _QW_P`, BL's `P_w` and `Q_w` satisfy the datum. Lemma 6.7 (3)
     gives `Q ∩ wPw⁻¹ ⊆ Q_w` and `U_{Q_w} = (M_Q ∩ wU_Pw⁻¹) U_Q`. Hence
     `Q_w = (M_Q ∩ wM_Pw⁻¹)(M_Q ∩ wU_Pw⁻¹)U_Q ⊆ (Q ∩ wPw⁻¹)U_Q ⊆ Q_w`. The
     same holds on rational points, since `M_{Q_w}(F)` and `U_{Q_w}(F)` are
     products of the rational points of their factors. `P_w` is symmetric,
     as `P_w` for `(P, Q, w)` is `Q_{w⁻¹}` for `(Q, P, w⁻¹)`.
  2. Changing the representative of a double coset changes nothing. Let
     `w' = x w y` with `x ∈ Q(F)` and `y ∈ P(F)`. Then the groups
     `(P ∩ w'⁻¹Qw')U_P` and `(Q ∩ w'Pw'⁻¹)U_Q` are `y⁻¹ P_w y` and
     `x Q_w x⁻¹`. Substitute `v = x v₀ x⁻¹` in the intertwining integral;
     conjugation by rational points preserves the normalized Haar measures.
     The constant term satisfies
     `C_{U_{w'}}φ(y⁻¹ z) = C_{U_w}φ(z)`, since `φ` is left `P(F)`-invariant,
     and `m_P(y⁻¹ z)^λ = m_P(z)^λ` by the product formula. The bijection
     `c ↦ x⁻¹ c` from `Q_{w'}(F) \ Q(F)` to `Q_w(F) \ Q(F)` then turns the
     `w'` summand into the `w` summand.

  The rational points determine `P' i` and `Q' i`. These are parabolic
  subgroups, hence connected, smooth and unirational, so their rational
  points are Zariski dense. Both reductions are explanatory and not proved
  here.
- The parabolics `P` and `Q`. As in the convergence statements, `P` comes
  with a root presentation and `Q` is any parabolic. Write `Q = δ Q₀ δ⁻¹`
  with `Q₀` standard and `δ ∈ G(F)`. Then the constant term along `V`
  at `g` is the constant term along the unipotent radical of `Q₀` at `δ⁻¹ g`,
  since `E(φ, λ)` is left `G(F)`-invariant. The representatives `δ⁻¹ w_i`
  and the conjugated datum transform the right side in the same way. This
  is explanatory.
- Convergence. "Taken in their range of convergence" (BL) and the
  exchange of sum and integral (MW II.1.7 (4)) appear as conclusions 1 and
  2, for the same `R`-regular `λ` as the identity. They follow from the
  same unfolding applied to `|φ_λ|`. With `|C_{U_w} φ_λ| ≤ C_{U_w}|φ_λ|`,
  the sum over `i` and `c` of the integrals of the absolute values is at most
  `∫_{V(F) \ V(𝔸)} ∑_{δ ∈ P(F) \ G(F)} |φ_λ(δ u g)| du`. This is finite for
  `R` at least the bound of the absolute convergence of `E(φ, λ)`.
  Summability of complex numbers is absolute summability. The integrands
  are evaluated at chosen representatives, but they are invariant under the
  relevant discrete subgroups. So conclusion 1 is integrability of the
  descended functions.
- Region. BL fix `λ` with `⟨Re λ, α^∨⟩ ≫ 0` for `α ∈ Δ_P`, where the
  implied constant depends on `φ`. This is the existential `R` with the
  regularity predicate of the convergence statements.
- The compact subgroup `K`. BL fix `K` in good position with respect to a
  minimal Levi. Here `K` is any maximal compact subgroup with the Iwasawa
  decompositions for `P` and every `P_{w_i}`. The Markdown of the Eisenstein
  convergence statement explains the reduction to BL's case.

## Scope

The cuspidal formula (6.18) of the same lemma is not stated. It is a sum over
`W^{⊃Q}(P)` of cuspidal projections `[M(w, λ)(C^{cusp}_{P,P_w} φ)]_{wλ}`, and
the Library has no cuspidal projection `C^{cusp}` for these spaces yet. Also
not stated: the corollary on exponents in §6.10, the statement that each
summand lies in `𝒜_Q`, and the cuspidal version of MW II.1.7 (i) for
`M'` conjugate to `M`.
