# Local selection tests at a finite place for the globalization of `GL_n`

Module `Langlands.TraceFormula.GeneralLinearLocalSelectionTestStatement` contains two proposition
definitions and no proof:

- `Langlands.TraceFormula.GeneralLinearDiscreteSeriesSelectionTestStatement.{u, uV, uW} : Prop`;
- `Langlands.TraceFormula.GeneralLinearSupercuspidalSelectionTestStatement.{u, uW} : Prop`.

Both concern one compactly supported, locally constant test function `φ` on `GL_{r+1}(K_v)`, for a
finite place `v` of a number field `K`. Each asks for two properties of `φ`.

- Selection: the character vanishes at `φ` for every representation outside a prescribed class,
  among a tested family of irreducible admissible representations, whatever their central
  characters. For the discrete-series test the tested family is the generic unitarizable
  irreducible admissible representations. For the supercuspidal test it is all irreducible
  admissible representations.
- Orbital nonvanishing: on some nonempty open subset of `GL_{r+1}(K_v)`, every orbital integral
  of `φ` is nonzero.

These are the local inputs of the trace-formula globalization of square-integrable representations
in Arthur–Clozel, Chapter 1, Lemma 6.5, and Henniart–Lemaire, II.6.7–II.6.9. The formulation fits
the Library's simple trace formula, which is on all of `L²([G])`. See "Why every central character"
below.

## Common setting

Let `K : Type u` be a number field, `v : Langlands.Global.FinitePlace K` and `r : ℕ`. Write `K_v`
for `v.adicCompletion K`. It carries its completion topology, the Mathlib instance. Its valuative
relation is `(CompletionPadic.topologicalData v).valuativeRel` and its nonarchimedean local-field
structure is `(CompletionPadic.topologicalData v).localField`. These are the conventions of
`GeneralLinearDiscreteSeriesGlobalizationStatement`. The group `GL_{r+1}(K_v)` has the matrix
topology and its Borel σ-algebra. Its Hausdorff, locally compact and totally disconnected
structures are `LocalFieldTopology.generalLinear_t2Space`,
`LocalFieldTopology.generalLinear_locallyCompactSpace` and
`LocalFieldTopology.generalLinear_totallyDisconnectedSpace`.

- A test function is an element of `HarmonicAnalysis.SchwartzBruhat (GL_{r+1}(K_v))`: a locally
  constant, compactly supported function `GL_{r+1}(K_v) → ℂ`.
- For a Haar measure `μ` and an admissible representation `π` with admissibility proof `hπ`,
  `Character.distribution μ π hπ φ` is the trace of the finite-rank operator
  `π(φ) = ∫ φ(g) π(g) dμ(g)`.
- `orbitalIntegral γ νγ φ` is the integral of `x ↦ φ(x⁻¹ γ x)` over `glCentralizer γ \ GL_{r+1}(K_v)`
  for the supplied quotient measure `νγ`. The statements quantify over every Haar measure `μ`,
  every right-invariant Haar measure `μγ` on the centralizer `glCentralizer γ` and every quotient
  measure `νγ` with `IsCompatible (glCentralizer γ) μ μγ νγ`. Left coset spaces carry their Borel
  σ-algebra (`leftQuotientMeasurableSpace`).

## `GeneralLinearDiscreteSeriesSelectionTestStatement`

Let `ρ : Representation ℂ (GL_{r+1}(K_v)) V`, with `V : Type uV`, be admissible, irreducible and
square-integrable modulo the centre (`JacquetLanglands.IsSquareIntegrable ρ`). Then there is a test
function `φ` such that:

1. Let `π : Representation ℂ (GL_{r+1}(K_v)) W`, with `W : Type uW`, be irreducible, admissible and
   unitarizable (`IsUnitarizable π`: there is an invariant positive definite Hermitian form). Let
   `π` be generic for some unitary additive character `ψ` of `K_v`
   (`Whittaker.IsGeneric ψ r π`). Let `μ` be a Haar measure on `GL_{r+1}(K_v)`. If
   `Character.distribution μ π hπ φ ≠ 0`, then there is `χ : K_vˣ →* ℂˣ` with `χ t = 1` whenever
   `Valued.v (t : K_v) = 1`, that is, on the units of the completed valuation ring, and `‖χ t‖ = 1`
   for all `t`, such that
   `twist (χ.comp GeneralLinear.determinant) ρ` is equivalent to `π`.
2. There is a nonempty open set `U ⊆ GL_{r+1}(K_v)` such that `orbitalIntegral γ νγ φ ≠ 0` for every
   `γ ∈ U` and all measures as above.

The character `χ` in clause 1 is unramified and unitary. The conclusion is that of condition 4
of `GeneralLinearDiscreteSeriesGlobalizationStatement`.

## `GeneralLinearSupercuspidalSelectionTestStatement`

There is a test function `φ` such that:

1. `HasVanishingConstantTerms φ` (module `Langlands.BaseChange.CuspForm`): for every standard
   block shape with at least two blocks, every Haar measure on its unipotent subgroup `N` and all
   `x, y`, the function `u ↦ φ(x u y)` is integrable on `N` and its integral vanishes.
2. Every irreducible admissible `π : Representation ℂ (GL_{r+1}(K_v)) W`, with `W : Type uW`, with
   `Character.distribution μ π hπ φ ≠ 0` for some Haar measure `μ` is supercuspidal
   (`GeneralLinear.IsSupercuspidal π`: admissible, with zero Jacquet quotients for the
   conjugates of all proper block parabolic subgroups).
3. There is a nonempty open set `U ⊆ GL_{r+1}(K_v)` such that `orbitalIntegral γ νγ φ ≠ 0` for every
   `γ ∈ U` and all measures as above.

## Why every central character

The Library's simple trace formula, `GeneralLinearSimpleTraceFormulaStatement` and its tensor form
`GeneralLinearTensorSimpleTraceFormulaStatement`, computes the trace of `R(f)` on `L²` of the
quotient of `GL_n(𝔸_K)` by `GL_n(K)` and the positive real points `A⁺` of the centre. Each cuspidal
summand of that space has as central character a unitary idele class character trivial on `K^×`
and `A⁺`, and different summands can have different central characters. The local components at
`v` of the summands therefore have various unitary central characters: the local restrictions of
these idele class characters. They need not exhaust the unitary characters of `K_vˣ` (for
`K = ℚ` such a character takes the uniformizer to a root of unity). The trace formula does not
fix one of them, so the test at `v` must control all of them at once. Both selection conditions
are uniform in the central character: clause 1 for the discrete-series test and clause 2 for the
supercuspidal test. Arthur–Clozel (Lemma 2.4) and Henniart–Lemaire (II.6.9) instead take the trace
on a space with one fixed central character, and use a pseudo-coefficient with that central
character.

`Langlands.BaseChange.CuspidalPseudoCoefficientExistenceStatement` and
`Langlands.BaseChange.SupercuspidalCuspFormStatement` state local results with a fixed central
character `χ`. Their selection among irreducible representations (irreducible tempered ones for
the pseudo-coefficient, all irreducible admissible ones for the supercuspidal cusp form) is
restricted to representations with central character `χ`. The induced-trace clause (b) of
`CuspidalPseudoCoefficientExistenceStatement` puts no central-character condition on the
inducing representation. The test functions of the present statements are obtained from
fixed-central-character functions by restricting to `|det| = 1`, as explained next.

## Derivation from the sources

Write `G = GL_n(K_v)` with `n = r + 1`, `Z ≅ K_vˣ` for its centre, `𝒪ˣ` for the units of `K_v`,
`ϖ` for a uniformizer and `G¹ = {g : |det g| = 1}`. For `ζ^n = 1` put `η_ζ(t) = ζ^{ord t}`.

**Truncation.** Let `ω` be a unitary character of `Z`. Let `h` be locally constant on `G`,
compactly supported modulo `Z`, with `h(zg) = ω(z)⁻¹ h(g)`. Put `φ = 1_{G¹} · h`. Its support lies
in `G¹ ∩ CZ` for a compact `C`, which is compact, so `φ` is a test function. For an admissible `π`
with central character `ω_π`:

- (T1) `π(φ) = (π ⊗ (η ∘ det))(φ)` for every unramified `η`, since `η ∘ det = 1` on `G¹`.
- (T2) `π(φ) = 0` unless `ω_π = ω` on `𝒪ˣ`: for a unit scalar `u`, `φ(ug) = ω(u)⁻¹ φ(g)`.
- (T3) If `ω_π = ω`, then `π(φ) = (c/n) ∑_{ζ^n = 1} (π ⊗ (η_ζ ∘ det))(h)`, with `c > 0` the volume
  of `𝒪ˣ` and `π'(h) = ∫_{G/Z} h(g) π'(g) dġ`. Indeed `G¹` maps onto `ZG¹/Z` with fibres `𝒪ˣ`,
  and `n · 1_{ZG¹} = ∑_ζ η_ζ ∘ det`.

If `ω_π = ω` on `𝒪ˣ`, an unramified `η` with `η(ϖ)^n = ω(ϖ) ω_π(ϖ)⁻¹` gives `ω_{π ⊗ η} = ω`. If
`ω_π` and `ω` are unitary, `η` is unitary. So by (T1)–(T3), `π(φ) ≠ 0` implies `π'(h) ≠ 0` for some
twist `π' = π ⊗ (η η_ζ ∘ det)` of central character `ω`.

**Discrete series.** Let `ω` be the central character of `ρ`; it is unitary. Henniart–Lemaire,
II.5.13, Proposition, with `E = F` and `σ = 1`, gives a pseudo-coefficient `h` of `ρ`, compactly
supported modulo `Z` with `h(zg) = ω(z)⁻¹ h(g)`. Thus
`tr π'(h) = 1` if `π' ≅ ρ` and `0` for the other irreducible tempered `π'` of central character
`ω`. By Henniart–Lemaire, II.5.14, Proposition 2, `tr π'(h) = 0` for every representation
parabolically induced from an irreducible representation of a proper standard Levi subgroup with
central character extending `ω`, and the orbital integrals of `h` vanish at the regular
non-elliptic elements. Put `φ = 1_{G¹} h`.

- Clause 1. Let `π` be irreducible, admissible, generic and unitarizable with `tr π(φ) ≠ 0`. Its
  central character is unitary. The truncation step gives a twist `π' = π ⊗ (η' ∘ det)`, `η'`
  unramified and unitary, of central character `ω`, with `tr π'(h) ≠ 0`. `π'` is irreducible,
  generic and unitarizable. By the Bernstein classification recalled in Henniart–Lemaire, II.3.3,
  `π'` is a discrete series or is irreducibly induced from a proper standard Levi subgroup. Here
  "discrete series" is meant up to the central character, which is unitary. In the induced case
  `tr π'(h) = 0`. A discrete series is tempered, so `π' ≅ ρ`, and `π ≅ ρ ⊗ (η'⁻¹ ∘ det)`.
- Clause 2. `h` is elliptic. By the local simple trace formula (Henniart–Lemaire, II.4.10,
  Lemma 1), `Λ(h, γ) = \overline{Θ_ρ(γ)}` at every regular elliptic `γ`. Here `Λ` is the orbital
  integral over `Z \ G`, with the normalization of II.4.10. By the Jacquet–Langlands
  correspondence, as used in Henniart–Lemaire, II.6.7, `Θ_ρ` is a nonzero constant on the regular
  elliptic elements near `1`, and so is its complex conjugate. Let `U` be the set of regular
  elliptic elements in a small neighbourhood of `1` contained in `G¹`. It is open: the Library
  proves `Langlands.BaseChange.isOpen_regularElliptic` for nonarchimedean local fields of
  characteristic zero. It is nonempty: let `E/K_v` be unramified of degree `n`, embedded in the
  matrix algebra by its multiplication action on a basis, and let `a` be an integral generator of
  `E` over `K_v`. Then `1 + ϖ^m a` generates `E` and is regular elliptic, and it tends to `1` as
  `m → ∞`. For `γ ∈ U` the centralizer is an elliptic torus `T` with `T/Z` compact. So
  `orbitalIntegral γ νγ φ` is a positive multiple of `Λ(h, γ) ≠ 0`, for every compatible choice of
  measures.

**Supercuspidal.** Fix an irreducible supercuspidal representation `σ` of `G` with unitary central
character `ω`. Twisting any supercuspidal representation by an unramified character makes its
central character unitary. Fix an invariant inner product `⟨·, ·⟩`, linear in the first variable,
and a unit vector `w`, and put
`h(g) = d(σ) \overline{⟨σ(g) w, w⟩}` with `d(σ)` the formal degree. Then `h(zg) = ω(z)⁻¹ h(g)`
and `h` is compactly supported modulo `Z`. Put `φ = 1_{G¹} h`.

- Clause 1. The coefficients of `σ` integrate to zero along the unipotent radicals `N` of proper
  parabolic subgroups, after any translation, because the Jacquet modules of `σ` vanish. Since
  `1_{G¹}(x m y) = 1_{G¹}(x y)` for `m ∈ N`, `φ` has the same property.
- Clause 2. Let `π'` be irreducible admissible with central character `ω` and `π'(h) ≠ 0`. Pick `e`
  with `π'(h) e ≠ 0`. Then `x ↦ ∫_{G/Z} ⟨x, σ(g) w⟩ π'(g) e dġ` is a nonzero `G`-map from `σ` to `π'`,
  so `π' ≅ σ`. With the truncation step, every irreducible admissible `π` with `tr π(φ) ≠ 0` is an
  unramified twist of `σ`. Unramified twists of a supercuspidal representation are
  supercuspidal. Here `η` need not be unitary.
- Clause 3. `h` is a pseudo-coefficient of the discrete series `σ` and is elliptic, so the argument
  of clause 2 of the discrete-series statement applies.

## Sources

- Guy Henniart and Bertrand Lemaire, *Changement de base et induction automorphe pour `GL_n` en
  caractéristique non nulle*, Mém. Soc. Math. Fr. 124 (2011). Retained source
  `provided-a0a5445aba86b871bcd83f08813de3234fddb463ff9bb3c9dfd60d2d2fcdae61`, SHA-256
  `7af2940c75a75937c1bf9096eb329931d4245cf592e3572db0ff93ec6e76c5e0` (PDF page = printed
  page + 8).
  - II.3.2–II.3.3, printed p. 79: generic irreducible representations as irreducible products of
    essentially square-integrable representations, and the Bernstein classification of the
    generic unitary representations.
  - II.4.10, Lemma 1, printed p. 93: the local simple trace formula for elliptic functions with a
    unitary central character.
  - II.5.13, Définition and Proposition, printed p. 113: existence of pseudo-coefficients of
    discrete series, compactly supported modulo the centre with a fixed central character.
  - II.5.14, Propositions 1 and 2, printed pp. 114–115: vanishing on properly induced
    representations and ellipticity of pseudo-coefficients.
  - II.6.7, printed pp. 123–124: the pseudo-coefficient test at the distinguished place, the
    constant nonzero character near `1` by the Jacquet–Langlands correspondence, and local
    constancy of orbital integrals on the regular set.
  - II.6.9, printed p. 125: the local component at the distinguished place is generic and
    unitary, hence properly induced or a discrete series, and the pseudo-coefficient kills
    the induced case.
- James Arthur and Laurent Clozel, *Simple Algebras, Base Change, and the Advanced Theory of the
  Trace Formula*, Annals of Mathematics Studies 120 (1989). Retained source
  `arthur-clozel-1989-base-change`, SHA-256
  `c2e47ee562810367ebcacd3f1c242eda40b9e78b271668e36d99ce31001f9a19`. Chapter 1, Lemma 6.5 and
  its proof, printed pp. 54–55 (PDF pp. 68–69): pseudo-coefficients at the distinguished place,
  a supercuspidal coefficient at an auxiliary place, and the simple trace formula of Lemma 2.4.
- David Kazhdan, *Cuspidal geometry of p-adic groups*, J. Analyse Math. 47 (1986), Theorem K:
  existence of pseudo-coefficients for groups with compact centre, cited by Arthur–Clozel in the
  proof of Lemma 6.5 (printed p. 55). Henniart–Lemaire give their own construction in II.5.13,
  with a fixed central character, which is the form used above.

The two propositions are derived from these sources. They depart from them in two ways. The
selection is required for every central character. The test is restricted to `|det| = 1`, so the
discrete series is selected only up to unramified unitary twists.
