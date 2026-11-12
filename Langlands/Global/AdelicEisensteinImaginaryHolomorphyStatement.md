# Holomorphy of Eisenstein series on the imaginary axis

Module `Langlands.Global.AdelicEisensteinImaginaryHolomorphyStatement` states
`Langlands.Global.EisensteinImaginaryAxisHolomorphyStatement` as a
proposition definition. It supplies no proof.

## Source

E. Lapid, *On Arthur's asymptotic inner product formula of truncated
Eisenstein series*, in: On Certain L-Functions, Clay Math. Proc. 13 (2011),
pp. 309–331, registered as
`lapid-2011-asymptotic-inner-product-truncated-eisenstein` (volume PDF; PDF
page = printed page + 9).

- Proposition 6, p.329 (PDF page 338): for any `φ ∈ A^2_P` the Eisenstein
  series `E_P(·, φ, λ)` is holomorphic for `λ ∈ i𝔞_P^*`.
- The proof, pp.329–330, uses Lemma 10 (the bound (19)
  `‖Θ_φ‖² ≤ |Ω| ‖φ‖²_*` for wave packets, a sharpening of Proposition 2) and
  the fact that near any point the singularities of `E_P(·, φ, λ)` lie along
  finitely many root hyperplanes `⟨λ − λ₀, α^∨⟩ = 0`.
- §2, p.312 (the Working hypothesis): the meromorphic continuation of
  `E(·, φ, λ)` as a function with values in a Fréchet space of functions of
  moderate growth. It is proved by Bernstein–Lapid (J. Amer. Math. Soc. 37
  (2024), registered as
  `bernstein-lapid-2024-meromorphic-continuation-eisenstein`), Theorem 2.3
  and Corollary 8.6.

Lapid's `E_P(g, φ, λ) = ∑_{γ ∈ P \ G} φ_λ(γ g)` with
`φ_λ(g) = φ(g) e^{⟨λ, H_P(g)⟩}` (§2, p.311), the convention of the Library's
`IsIwasawaCompact.eisensteinSeries` (module
`Langlands.Global.AdelicEisensteinSeries`). Since `φ ∈ A^n_P` already carries
the factor `δ_P^{1/2}`, the unitary axis is `λ ∈ i𝔞_P^*`.

## Statement

The data are those of `EisensteinMeromorphicContinuationStatement` (module
`Langlands.Global.AdelicEisensteinContinuationStatement`), for a number field
`F : Type`:

- `G` connected reductive, affine and locally of finite type;
- `P = MU` with presentation `r : ParabolicRootPresentation p l a`, `p` a
  closed immersion, `P` and `M` affine, `M` locally of finite type, `iU` a
  geometric unipotent radical of `P`. `P` is locally of finite type as a
  closed subgroup of `G` (`IsClosedSubgroup.locallyOfFiniteType`, supplied by
  `haveI`);
- `K` maximal compact in `G(𝔸)` with `P(𝔸)K = G(𝔸)` (`hK`), a closed
  matrix embedding `rho`, and the smooth-structure data `hsmooth`, `hcalc`;
- `φ ∈ A^2_P`: `IsSquareIntegrableInducedForm K hK.isCompact rho hsmooth
  hcalc p iU l φ` (module `Langlands.Global.AdelicSquareIntegrableInducedForms`).

The statement is universal in the continuation. It quantifies
`E : X^*(P) ⊗ ℂ → (G(𝔸) → ℂ)` and `D` such that

1. for every `g`, `λ ↦ E λ g` is meromorphic with domain of holomorphy `D`
   (`IsMeromorphicInCoordinatesOn`, module
   `Langlands.Analysis.Meromorphic.LinearCoordinates`);
2. for some `R`, `E λ = hK.eisensteinSeries φ λ` whenever
   `r.IsRegularParameter hA hT R λ`.

The conclusion: there are `E'` and `D'` with

- `imaginaryParameter F P μ ∈ D'` for every `μ ∈ X^*(P) ⊗ ℝ`, that is,
  `i𝔞_P^* ⊆ D'`;
- for every `g`, `λ ↦ E' λ g` is meromorphic with domain of holomorphy `D'`;
- `E' λ = E λ` for every `λ ∈ D ∩ D'`.

## Correspondence with the source

- Meaning of the conclusion. `IsMeromorphicInCoordinatesOn` requires `D'` to
  be open and dense and `E'(·, g)` to be holomorphic on `D'`, in every
  complex linear coordinate system. So `E'(·, g)` is holomorphic on a
  neighbourhood of `i𝔞_P^*`, and it agrees with `E(·, g)` on the dense open
  set `D ∩ D'`. Hence `E'` is the same meromorphic function as `E`, with its
  singularities along `i𝔞_P^*` removed: this is Lapid's assertion that the
  meromorphic continuation is holomorphic there.
- Why `E'` and not `E`. The domain `D` in the hypothesis is not canonical:
  a meromorphic function stays meromorphic with any smaller open dense
  domain, and its values off `D` are unconstrained. So the statement cannot
  ask for `i𝔞_P^* ⊆ D`; it asks for a representative `E'` of the same
  meromorphic function whose domain contains `i𝔞_P^*`.
- Universal form. Data `(E, D)` exist by Bernstein–Lapid 2.3 (1)
  (`EisensteinMeromorphicContinuationStatement`): evaluating the
  `𝔉_umg`-valued continuation at `g` is continuous, so it gives scalar
  meromorphic functions. Any two choices agree on the intersection of their
  domains: their difference is holomorphic there, locally a quotient `h/g`
  with `g ≢ 0` on a connected open set, and vanishes on the nonempty open
  regular region; the set of points near which it vanishes is open and
  closed in `ℂⁿ`. So the conclusion does not depend on the choice. This is
  explanatory and not proved here.
- One domain for all `g`. Lapid's Working hypothesis and BL Corollary 8.6
  make `E(·, φ, λ)` a meromorphic function with values in a Fréchet space,
  whose singularities near any point lie on finitely many root hyperplanes
  (BL 2.3 (6), `RootHyperplaneSingularitiesStatement`). Lapid's proof shows
  that no singular hyperplane passes through a point of `i𝔞_P^*`; then the
  open set `D'` where the Fréchet-valued function is holomorphic contains
  `i𝔞_P^*` and works for every `g`. This is explanatory and not proved
  here.
- Regions. "`Re λ` sufficiently regular in the positive Weyl chamber" is
  `r.IsRegularParameter hA hT R λ` for some `R`, as in the Markdown of
  `EisensteinAbsoluteConvergenceStatement`. Lapid takes `P` standard with
  respect to a fixed minimal parabolic; here the presentation `r` supplies
  the minimal parabolic and maximal split torus for which `P` is standard.
- `A^2_P`. The predicate `IsSquareIntegrableInducedForm` is Lapid's `A^2_P`
  (see the Markdown of `Langlands.Global.AdelicSquareIntegrableInducedForms`),
  with `A_M` the Library's canonical split component of `M(𝔸)` and the
  archimedean `K`-finiteness taken for the given `K`.
- The compact subgroup. Lapid (§2) fixes `K` in good position with respect to
  a minimal Levi `M₀`. Here `K` is any maximal compact subgroup with
  `P(𝔸)K = G(𝔸)`. The reduction is the one in the Markdown of
  `EisensteinAbsoluteConvergenceStatement`: with `K₀` in good position and
  `K_∞ = nK₀,∞n⁻¹`, the Eisenstein series for `K` is a finite sum
  `∑ j, exp⟨λ, c_j⟩ · E^{K₀}(φ_j, λ)(· n)` with coefficients entire in `λ`.
  Each `φ_j`, the product of `φ(· n⁻¹)` with the indicator of a left
  `P(𝔸_f)`-invariant open and closed set, is again in `A^2_P` (for `K₀`):
  the indicator depends only on the finite component, so it is
  `A_M`-invariant, and `|φ_j| ≤ |φ(· n⁻¹)|`. So holomorphy on `i𝔞_P^*` for
  `K₀` gives it for `K`. This is explanatory and not proved here.
- Universe. The canonical split component `A_M` is defined for `F : Type`,
  so the statement quantifies over number fields in universe `0`.

## Scope

Lapid's Propositions 1 and 2, Lemma 10, Theorem 1 and Theorem 2 are not
stated here. The statement is pointwise in `g`, with one domain of
holomorphy for all `g`. Holomorphy as a function with values in a Fréchet
space of functions is not asserted here.
