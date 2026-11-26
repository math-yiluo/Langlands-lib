# Logarithmic Siegel bounds for the derivatives of weighted square-integrable forms

Module `Langlands.Global.AdelicLogSquareIntegrableSiegelDerivativeBounds`, namespace
`Langlands.Global`.

The module states one proposition, `LogSquareIntegrableSiegelDerivativeBoundsStatement`, and
does not prove it. It contains no other declaration. It is the part of Delorme's
Proposition 3.5 and Lemma 3.2 that gives Siegel-set bounds for the automorphic forms of
`TemperedWeakConstantTermVanishingStatement`. Its hypothesis on `Φ` is weighted
square-integrability of `Φ` itself. Delorme's hypothesis is weighted square-integrability of
every derivative of `Φ`.

## Sources

- P. Delorme, *On the spectral theorem of Langlands*, Adv. Math. 426 (2023) 109107,
  registered as `delorme-2023-spectral-theorem-langlands`. The published PDF in that folder
  has file SHA-256 `9b2e82af72ac45c9745357d475153d43d29ec3e1ea68bf51980acf466110e2df`. Its
  numbering and page numbers are used here; the arXiv TeX in the same folder numbers the
  results differently.
  - §2, p.7: Siegel domains (2.3) and the inclusion (2.4),
    `𝔰_P ⊆ Ω_{N_P} {exp X | X ∈ 𝔞_0^{+,P}} Ω` with `Ω` compact.
  - §2, p.8: the norm and `σ(g) = 1 + log ‖g‖`, (2.6)–(2.8), with
    `σ_{[G]} ∼ σ ∼ 1 + ‖H₀‖` on `𝔰_P`; the function `Ξ^{[G]}(x) = vol_{[G]}(xB)^{-1/2}` and
    (2.9); Lemma 2.1, (i) `Ξ^{[G]} ∼ e^{ρ(H₀)}` and (ii) `σ_{[G]} ∼ 1 + ‖H₀‖` on `𝔰_G`;
    (2.10).
  - §3.1, p.11: Lemma 3.2, for `φ ∈ 𝒜_P(G)` the equivalent conditions a)
    `|φ| ≪ Ξ^{[G]_P} σ_{[G]_P}^d`, b) on every Siegel domain, and c)
    `|φ(exp X ω)| ≪ e^{ρ(X)} (1 + ‖X‖)^d` for `ω` in every compact `Ω ⊆ G(𝔸)` and
    `X ∈ 𝔞_0^{+,P}`; Definition 3.3 (tempered forms: the form and all its derivatives by
    `U(𝔤_∞)` satisfy these conditions for some `d`); Remark 3.4 and the paragraphs after it
    (pp.11–12): Bernstein's standard measure `dm_X = (Ξ^{[G]})² dx`, and `[G]`-temperedness,
    there is `d > 0` with `(1 + σ_{[G]})^{-d} R_u φ ∈ L²([G])` for every `u ∈ U(𝔤_∞)`.
  - §3.1, p.12: Proposition 3.5, for `φ ∈ 𝒜(G)`: (i) `φ` is tempered if and only if (ii)
    `φ` is `[G]`-tempered. The proof of (ii) ⇒ (i) applies Bernstein's Key Lemma to
    `f = R_u φ`, with `ν = (Ξ^{[G]})²` and the weight `w = σ_{[G]}^d`, and obtains
    `|f(x)|² ≪ ν(x) w(x) ∫_{[G]} Q(f) w^{-1}`, where `Q(f)` is the sum of the squares of the
    derivatives of `f` of degree at most `k ≥ dim G`.
- J. Bernstein, *On the support of Plancherel measure*, J. Geom. Phys. 5 (1988) 663–710,
  registered as `bernstein-1988-support-plancherel`, file SHA-256
  `4d96d9b76127df990379dac18e578d613e1bed6c049ab8604f006a837925ea63` (printed page numbers;
  PDF page = printed page − 662): weights in §3.1; the Lemma-Definition of §3.3 (pp.683–684),
  whose proof (ii) takes the standard measure `m_X = ν_B μ_X` with
  `ν_B(x) = μ_X(Bx)^{-1}`, the inverse volume of a ball in the quotient; the Key Lemma of §3.4
  (p.686), `|f(x)|² ≤ C ∫_{Bx} Q(f) dm_X` for `f` fixed by a regular subgroup and
  `k > dim 𝔤`.
- Harish-Chandra, *Discrete series for semisimple Lie groups II*, Acta Math. 116 (1966) 1–111,
  registered as `harish-chandra-1966-discrete-series-ii`, file SHA-256
  `3ad72529bddbfe96e537bc3f49df6aa3223169c2abbe265d858c32c48545f3d9`: §8, Theorem 1
  (pp.18–19), a smooth function whose `𝔷`- and `K`-transforms span a finite-dimensional space
  satisfies `f * α = f` for a compactly supported smooth `α`, supported in any given
  neighbourhood of `1`. This source enters only the proof route described below.

## The statement

`LogSquareIntegrableSiegelDerivativeBoundsStatement` has the hypotheses of
`TemperedWeakConstantTermVanishingStatement` (module
`Langlands.Global.AdelicTemperedVanishingReduction`) up to and including the one on `Φ`, in
the same order and with the same universe:

- a number field `F : Type` and an affine group scheme `G` over `F`, locally of finite type,
  with `IsConnectedReductive G`;
- a subgroup `K ⊆ G(𝔸)` with `IsMaximalCompactSubgroup F G K`;
- a matrix representation `rho` with `IsClosedSubgroup rho`, and `hsmooth`, `hcalc`;
- a compatible family `𝓕 : StandardParabolicFamily F G` of standard parabolics with
  `IsIwasawaCompact (𝓕.p 𝓕.bot) K`, that is `P_∅(𝔸) K = G(𝔸)`;
- `Φ : G(𝔸) → ℂ` with `IsLogSquareIntegrableAutomorphicForm F G K rho hsmooth hcalc Φ`
  (module `Langlands.Global.AdelicWavePacketCompletenessReduction`). So `Φ` is an automorphic
  function on `G(F) \ G(𝔸)` (`IsAutomorphicFunctionOn`: left `G(F)`-invariant, continuous,
  smooth on the infinite slices and fixed by an open subgroup of `G(𝔸_f)`, finite under the
  archimedean part `K_∞ = K.comap (ofInfinite F G)` of `K`, `𝔷`-finite, of moderate growth),
  it has a unitary character `a ↦ a^{iν}` of `A_G`, and
  `y ↦ Φ(y.out) / σ_{[G]}(y)^{m₀}` lies in `L²([G])` for some `m₀`, for the quotient `μG` of
  Haar measure by counting measure. Here `σ_{[G]} = rationalLogHeight F G rho`.

The conclusion uses the Siegel data of the module
`Langlands.Global.AdelicWavePacketRapidDecaySiegelReduction`, with the meaning given in its
Markdown page. For every algebraic Siegel setup `(T, i, ν, T₀, j)` with
`IsSiegelAlgebraicSetup F G T i ν T₀ j`, every
`C : CompactFactors F G (Standard.unipotentScheme i ν ∅) (Standard.leviScheme i ν ∅)`, every
threshold `t : ℝ≥0ˣ` and every compact `Ω ⊆ G(𝔸)` there is `m : ℕ` such that for every word
`D : List (smoothModel F d)` there is `C_D ≥ 0` with

`‖adelicIteratedDirectionalValue hsmooth D Φ x‖ ≤ C_D · siegelModulus(a)^{1/2} · adelicLogHeight(x)^m`

whenever `IsSiegelPoint F G T i ν T₀ j C t Ω a x`. Spelled out:

- `IsSiegelPoint … C t Ω a x` says `x = z · (n m a k) · w` with `z ∈ A_G`, `n ∈ Ω_N`,
  `m ∈ Ω_M ⊆ M₀(𝔸)¹`, `a ∈ A_{T₀}` with `|β(a)| ≥ t` for every simple relative root `β`, `k`
  in the compact subgroup `K_C` of `C`, and `w ∈ Ω`. The point `x` lies in the Siegel set
  `A_G · Ω_N Ω_M A_{T₀}(t) K_C · Ω`, with torus coordinate `a`.
- `siegelModulus F G T i ν T₀ j a = ∏_{β > 0} |β(a)|^{m_β} = δ_{P₀}(a)`, so its square root
  is `e^{ρ₀(H₀(a))}`.
- `adelicLogHeight F G rho x = 1 + log max(1, ‖x‖_ρ)` is Delorme's `σ(x)` at the point `x`
  of `G(𝔸)`.
- For a word `D = [X₁, …, X_r]` of vectors of the model space `smoothModel F d` of the
  archimedean group `G_∞ = G(F ⊗ ℝ)`, `adelicIteratedDirectionalValue hsmooth D Φ` is
  `R(X₁) R(X₂) ⋯ R(X_r) Φ` (module `Langlands.Global.AdelicMaximalUnipotentDecay`; the word is
  folded from the right). Here `R(X) f (x) = adelicDirectionalValue hsmooth X f x` is the
  derivative at `1` in the tangent direction `X` of `t ↦ f(x · t)`, `t ∈ G_∞`, for the smooth
  structure `smoothChartedSpace F G hsmooth`. So `R(X)` is the right regular action of `X ∈ 𝔤_∞`
  on functions on `G(𝔸)`. Every element of `U(𝔤_∞)` is a finite linear combination of
  monomials `X₁ ⋯ X_r`, so the bounds for all words are bounds for all `R_u Φ`,
  `u ∈ U(𝔤_∞)`, as in Definition 3.3.
- The empty word gives `Φ` itself (`adelicIteratedDirectionalValue_nil`), so the statement
  contains the bound `|Φ(x)| ≤ C_∅ δ_{P₀}(a)^{1/2} σ(x)^m`.

The exponent `m` is common to all words but may depend on the setup, on `C`, `t` and `Ω`. The
constant `C_D` may depend on all the data and on `D`. Nothing is asserted about lower bounds,
uniformity in `Φ`, or the value of `m` relative to `m₀`.

## Correspondence with Delorme

*Provenance (derived).* The statement is the implication (ii) ⇒ (i) of Delorme's
Proposition 3.5, for the forms of `IsLogSquareIntegrableAutomorphicForm`, with the conclusion
in the form c) of Lemma 3.2 for `P = G` and with its weighted `L²` hypothesis weakened to the
form itself. The changes are:

1. *Siegel sets.* For `P = G`, (2.4) puts every Siegel domain inside
   `{exp X | X ∈ 𝔞_0^+} Ω` with `Ω` compact. A Siegel point `x = z n m a k w` is of the same
   kind. Write `z a = exp X` with
   `X ∈ 𝔞_G ⊕ 𝔞_0^G`. The simple roots vanish on `𝔞_G`, and `|β(a)| ≥ t` puts `X` in a
   translate of the closed positive chamber. The conjugates `a⁻¹ n a` stay in a compact set
   for such `a`, and `m` commutes with `a`. So `x = exp X · ω` with `ω` in a compact set. Since
   `ρ₀` vanishes on `𝔞_G`, `e^{ρ₀(X)} = siegelModulus(a)^{1/2}`. The factors of `C` and `Ω` are
   arbitrary compact data, and no covering condition `G(𝔸) = G(F) 𝔰_G` is imposed. This
   matches the quantification over every Siegel domain in b) and over every compact `Ω` in
   c).
2. *The modulus.* Bernstein's Key Lemma bounds `|f(x)|²` by an integral against
   `dm_X = ν μ_X`, where `ν(x) = vol_{[G]}(xB)^{-1}` is the inverse volume of a quotient ball.
   Weighted `L²` control therefore gives pointwise control by `ν(x)^{1/2} = Ξ^{[G]}(x)`. By
   Lemma 2.1 (i), `Ξ^{[G]} ∼ e^{ρ(H₀)}` on Siegel domains. In the statement this inverse
   square root is the half modulus `siegelModulus(a)^{1/2}` of the torus coordinate.
3. *The logarithmic factor.* The weight `w = σ_{[G]}^d` of the proof of Proposition 3.5 gives
   the factor `σ_{[G]}^{d/2}` in condition a). By Lemma 2.1 (ii) and (2.8),
   `σ_{[G]} ∼ σ ∼ 1 + ‖H₀‖` on Siegel domains, so the factor `(1 + ‖X‖)^d` of c) and the
   factor `σ_{[G]}^{d/2}` of a) are both represented by a power of `σ(x)`. The Library weight
   `σ_{[G]}^{-2m₀}` and the measure weight `(1 + σ_{[G]})^{-d}` of the proof of
   Proposition 3.5 are comparable for `d = 2m₀`, because `1 ≤ σ_{[G]}`
   (`one_le_rationalLogHeight`). (The definition of `[G]`-temperedness on p.12 writes
   `(1 + σ_{[G]})^{-d} φ ∈ L²([G])`, which is the measure weight `(1 + σ_{[G]})^{-2d}`; the
   value of the exponent plays no role in the statement.)
4. *The exponent.* Definition 3.3 asks for "some `d`". The proof of Proposition 3.5 uses one
   weight `w` for all derivatives, and the statement asks for one `m` for all words.
5. *The hypothesis on `Φ`.* See the next section.

## The weighted `L²` hypothesis is on `Φ` only

Delorme's condition (ii) controls every derivative `R_u Φ` in `L²([G], (1 + σ_{[G]})^{-d})`.
`IsLogSquareIntegrableAutomorphicForm` controls only `Φ`. A proof of the statement has to
supply the derivatives. One intended route (not proved here) uses Harish-Chandra's reproducing
kernel:

- `Φ` is `K_∞`-finite and `𝔷`-finite, so Harish-Chandra (1966, §8, Theorem 1) gives a
  compactly supported smooth `α` on `G_∞` with `Φ = Φ * α` on every infinite slice. The
  kernel depends only on the `K_∞`-types and the annihilating ideal of `𝔷`, so it is uniform
  in the finite-adelic variable. With an open subgroup of `G(𝔸_f)` that fixes `Φ`, it becomes
  a compactly supported smooth function on `G(𝔸)`.
- For `u ∈ U(𝔤_∞)`, `R_u Φ = Φ * α_u`, where `α_u` is a derivative of `α` under translations
  and has the same compact support `S`. So `R_u Φ = ∫ α_u(g) R(g⁻¹) Φ dg`, with
  `(R(h) Φ)(y) = Φ(y h)`.
- The height is submultiplicative up to a constant, so for `h` in the compact set `S⁻¹` there
  is `c_S` with `σ_{[G]}(y) ≤ c_S σ_{[G]}(y h⁻¹)` for all `y`. With the right invariance of `μG`
  this gives `‖(R(h) Φ) σ_{[G]}^{-m₀}‖_{L²} ≤ c_S^{m₀} ‖Φ σ_{[G]}^{-m₀}‖_{L²}`. Minkowski's
  integral inequality then puts every `R_u Φ` in `L²([G], σ_{[G]}^{-2m₀})`, with the same
  exponent.
- The proof of Proposition 3.5 then gives `|R_u Φ(x)| ≪ Ξ^{[G]}(x) σ_{[G]}(x)^{m₀}`, and the
  comparisons of items 1–3 above turn this into the stated Siegel bound.

Alternatively, the differentiated kernel can be folded directly against the weighted bound
for `Φ`: `|R_u Φ(x)|` is at most `‖α_u‖_∞ ∫_{xS} |Φ|`, and the multiplicity with which `xS`
covers `[G]` is controlled by the inverse quotient-ball volume `Ξ^{[G]}(x)²`. These steps are
part of the proof obligation of the statement.

## Quotient height and adelic height

The hypothesis weights `Φ` by the quotient height
`σ_{[G]}(G(F) g) = 1 + log max(1, inf_{γ ∈ G(F)} ‖γ g‖_ρ)` (`rationalLogHeight`). The
conclusion uses the height `σ(x) = 1 + log max(1, ‖x‖_ρ)` of the point `x` of `G(𝔸)`
(`adelicLogHeight`). The Library theorem `rationalLogHeight_mk_le` (module
`Langlands.Global.AdelicWavePacketRapidDecaySiegelReduction`) proves

`σ_{[G]}(G(F) x) ≤ σ(x)` for every `x ∈ G(𝔸)`,

since `x` is one of the rational translates in the infimum. Therefore a bound by
`σ_{[G]}(G(F) x)^m`, the form produced by Bernstein's argument with `w = σ_{[G]}^d`, implies
the stated bound with `σ(x)^m`. By (2.7)–(2.8) the two heights are comparable on Delorme's
Siegel domains, so passing to `σ(x)` loses only constants there. The conclusion is stated with
the height of the point, as in `WavePacketSiegelDecayStatement` and
`SiegelDominatedIntegrabilityStatement`.

## The compact subgroup

Delorme fixes `K` in good position with respect to the minimal Levi subgroup (§2). Here `K`
is any maximal compact subgroup with `P_∅(𝔸) K = G(𝔸)` for some compatible family `𝓕`, the
scope of `TemperedWeakConstantTermVanishingStatement`. Apart from the hypotheses that `K` is
maximal compact and satisfies this Iwasawa condition, `K` enters the statement only through the
`K_∞`-finiteness of `Φ` in `IsLogSquareIntegrableAutomorphicForm`. The family `𝓕` and the
Iwasawa condition do not appear in the conclusion. The Siegel data are independent
geometric data: the compact subgroup `K_C` of `C` is an arbitrary compact subgroup of `G(𝔸)`,
in general different from `K`, and the chamber variable is the torus coordinate `a`, not an
Iwasawa height `H₀` defined through `K`.

The following is explanatory and not proved here. A maximal compact `K` is the product of its
archimedean and finite parts, so `K_∞` is a maximal compact subgroup of `G_∞`. All maximal
compact subgroups of `G_∞` are conjugate, so `K_∞ = π K'_∞ π⁻¹` for some `π ∈ G_∞` and some
`K'_∞` in good position. Then `Ψ = R(π⁻¹) Φ`, `Ψ(g) = Φ(g π⁻¹)`, is `K'_∞`-finite, and it
satisfies the other hypotheses on `Φ` with the same `m₀`, because `σ_{[G]}(yπ)` and
`σ_{[G]}(y)` differ by a bounded amount and `μG` is right invariant. The conclusion for all
compact `Ω` and all words passes from `Ψ` back to `Φ(x) = Ψ(x π)`: a Siegel point for `Ω` is
moved to a Siegel point for the compact set `Ω π`, `R(X) Φ(x) = R(Ad(π⁻¹) X) Ψ(x π)`, so a
word is replaced by its image under `Ad(π⁻¹)`, and `σ(x π) ≤ σ(x) + c_π`. The finite part of `K` plays no role, since smoothness at the
finite places is right invariance under some open subgroup of `G(𝔸_f)`.
