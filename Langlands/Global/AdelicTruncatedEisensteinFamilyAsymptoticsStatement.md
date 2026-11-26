# Lapid's Proposition 1 for holomorphic families of inducing vectors, with Arthur's projection property

Module `Langlands.Global.AdelicTruncatedEisensteinFamilyAsymptoticsStatement`
states one proposition,
`Langlands.Global.LocalTruncatedEisensteinFamilyInnerProductStatement`, and does
not prove it. It is a variant of
`Langlands.Global.LocalTruncatedEisensteinInnerProductStatement` (module
`Langlands.Global.AdelicTruncatedEisensteinAsymptoticsStatement`), from which it
takes the setting, the normalizations, the conclusion and the auxiliary
definitions `parameterConj`, `corootVector`, `StandardIndex`,
`IsStandardRegularParameter` and `corootCovolume`. The Markdown of that module
gives the correspondence with Lapid's notation in detail; this page describes
the two changes.

## Sources

- E. Lapid, *On Arthur's asymptotic inner product formula of truncated
  Eisenstein series*, in: On Certain L-Functions, Clay Math. Proc. 13 (2011),
  pp. 309–331, registered as
  `lapid-2011-asymptotic-inner-product-truncated-eisenstein` (volume PDF; PDF
  page = printed page + 9).
  - §2, p.311: "a maximal compact `K` of `G(𝔸)` which is in good position with
    respect to `M_0`", fixed throughout; p.312: the truncation operators `Λ^T`
    and `Λ^{T,P}`.
  - §3, p.313: Proposition 1 and formula (2): "Let `φ` be a smooth map from
    `i(𝔞_P^G)^*` to a finite-dimensional subspace of `A^2_P`; similarly for
    `φ'`. Assume that `E_P(·, φ(λ), λ)` is smooth on `i(𝔞_P^G)^*`; similarly
    for `E_{P'}(·, φ'(λ'), λ')`. …"
  - §§5–7, pp.317–325: the identity (8), Lemma 5, the regularized integrals,
    the constant terms of Eisenstein series (Proposition 4), and the proof of
    Proposition 1.
  - Proposition 6, p.329: holomorphy of `E_P(·, φ, λ)` on `i𝔞_P^*` for every
    `φ ∈ A^2_P`, deduced from Proposition 2.
- J. Arthur, *An introduction to the trace formula* (2005), in
  `arthur-ellwood-kottwitz-2005-harmonic-analysis-shimura`: §4, p.24, a
  suitable maximal compact `K` with `G(𝔸) = P_0(𝔸)K`, citing Arthur 1981,
  p.9; §13, Proposition 13.1 and the paragraph after its proof,
  pp. 68–69: for this `K`, `Λ^T` is an orthogonal projection on `L²`.
- J. Arthur, *A trace formula for reductive groups II: applications of a
  truncation operator*, Compositio Math. 40 (1980), 87–121, registered as
  `arthur-1980-trace-formula-reductive-groups-II` (PDF page = printed page −
  85): Lemma 1.5, p.97, the identity behind Lapid's (8).
- J. Arthur, *The trace formula in invariant form*, Ann. of Math. 114 (1981),
  1–74, registered as `arthur-1981-trace-formula-invariant-form`: §1, p.9,
  maximal compact subgroups admissible relative to `M_0` and their properties
  (i)–(iii).

## First change: one compact subgroup with both properties

`LocalTruncatedEisensteinInnerProductStatement` asserts that **some** maximal
compact `K` with the listed properties satisfies the conclusion of
Proposition 1, and `ArthurTruncation.TruncationOrthogonalProjectionStatement`
asserts that **some** `K` has the projection property. The two existential
statements do not combine: nothing says that one compact subgroup has both
properties, and Lapid's §8 uses truncation and Proposition 1 for the same `K`.

The proposition here asserts both for one `K : Subgroup (AdelicGroupPoints F G)`.
For every `F`, `G`, `T`, `i`, `ν` with `hG`, `hi` and a generic `ν` there is `K`
with:

- `IsMaximalCompactSubgroup F G K`;
- `IsIwasawaCompact (Standard.parabolicHom i ν ∅) K` and
  `IsIwasawaCompact (Standard.parabolicHom i ν S.roots) K` for every standard
  index `S` (`P_0(𝔸)K = Q(𝔸)K = G(𝔸)`);
- `P_0(𝔸) ∩ K` commuting with the positive torus of every Siegel setup
  (`AdelicSiegelFactors.IsPositiveTorusCompatible`);
- for all reflection data `D` and comparisons `hρ`: some `C` such that for
  every `T` with `β(T) > C` for all simple roots `β`, both
  `normOneTruncation hG hi D hK₀ hρ T` (on `G(F) \ G(𝔸)¹`, for
  `normOneRationalQuotientHaarMeasure F G`) and `truncation hG hi D hK₀ hρ T`
  (on `G(F) \ G(𝔸)`, for `rationalQuotientHaarMeasure F G`) satisfy
  `IsOrthogonalL2Extension`, **and** the asymptotic formula of
  `LocalTruncatedEisensteinInnerProductStatement`, in the family form below,
  for all data with respect to `K`.

The first three items are those of `LocalTruncatedEisensteinInnerProductStatement`;
the first, the second for `P_0`, the third and the projections are those of
`TruncationOrthogonalProjectionStatement`. As in those statements, the proofs
`hK₀`, `hK` are quantified again after the existential.

**Why the sources give one `K` with both properties.** Lapid proves
Proposition 1 for a maximal compact `K` in good position with respect to `M_0`
(p.311), following Arthur's conventions. Arthur 2005, §4, p.24, chooses a
suitable maximal compact `K = ∏_v K_v` with `G(𝔸) = P_0(𝔸)K`, citing
Arthur 1981, p.9, where such subgroups are called admissible relative to
`M_0`: at archimedean places the Lie algebras of `A_{M_0}` and `K_v` are
orthogonal for the Killing form, at the other places `K_v` belongs to a special
vertex of the apartment of a maximal split torus of `M_0`, and `K_v` is the
standard compact subgroup for almost all `v`. Arthur proves Proposition 13.1
and the projection property for this `K`. We read Lapid's good position as
this admissibility, so a `K` admissible relative to `M_0` has both properties.
It also has the other listed properties. By Arthur 1981, p.9, (i) and (iii),
`G(𝔸) = Q(𝔸)K` for every standard `Q` and
`K_v ∩ P_0(F_v) = (N_0(F_v) ∩ K_v)(M_0(F_v) ∩ K_v)`. At an archimedean place
`N_0(F_v)` has no nontrivial compact subgroup, so the archimedean part of
`P_0(𝔸) ∩ K` lies in `M_0(F_∞)`, which centralizes the maximal split torus.
The positive torus consists of points of the maximal split torus with trivial
finite components (its characters take values in
`PositiveRealIdeles.full`), so `P_0(𝔸) ∩ K` commutes with it. The proposition
claims nothing for other compact subgroups.

## The identity (8)

Lapid's regularized integrals (§5) rest on the identity (8), p.317, which
expresses a function `φ` on `G(F) \ G(𝔸)` through the relative truncations
`Λ^{T,P}φ`. It is Arthur 1980, Lemma 1.5, p.97, for the parabolic `G`:

`φ(g) = ∑_P ∑_{γ ∈ P(F) \ G(F)} Λ^{T,P}φ(γg) τ_P(H_P(γg) − T)`.

Arthur's lemma evaluates the height at the translated point `δx`, in the
characteristic function as well as in the truncated function. The printed (8)
has `τ_P(H_P(g) − T)`; this is a slip, since with the height at `g` the sum for
the constant function `1` on `SL_2` is infinite at every `g` with
`τ_B(H_B(g) − T) = 1` (`B(F) \ SL_2(F)` is infinite). The proposition does not
involve (8); it enters only through Lapid's proof.

## Second change: holomorphic families of inducing vectors

Lapid's `φ(λ)` is a smooth map into a finite-dimensional subspace of `A^2_P`,
and only `E_P(·, φ(λ), λ)` is assumed smooth: nothing is assumed about the
Eisenstein series of a basis of the subspace. (Their holomorphy on `i𝔞_P^*` is
Lapid's Proposition 6, p.329, which he deduces from Proposition 2 and so after
Proposition 1.) The fixed-vector form `LocalTruncatedEisensteinInnerProductStatement`
asks for the regularity of each vector's series (see "Smooth families" in the Markdown of
`AdelicTruncatedEisensteinAsymptoticsStatement`). Here:

| Lapid | Lean |
|---|---|
| `φ(λ) = ∑_l b_l(λ) v_l` | `q : ℕ`, `v : Fin q → G(𝔸) → ℂ` with every `v l ∈ A^2_P` (`IsSquareIntegrableInducedForm`), and `b : Fin q → X^*(P) ⊗ ℂ → ℂ` with `IsMeromorphicInCoordinatesOn (b l) Set.univ` (entire) |
| `E_P(·, φ(λ), λ)` | `E` meromorphic in coordinates with domain of holomorphy `DE`, and `E λ g = ∑_l b l λ · (hK J).eisensteinSeries (v l) λ g` for `IsStandardRegularParameter D J.roots R λ`, some `R` |
| `M(w, λ)φ(λ) ∈ A^2_Q` | `∑_l b l λ · (hK J).intertwiningOperator … (v l) λ g = ∑_a coeff S t a λ · ψ S t a g` for sufficiently regular `λ` |
| `φ'(λ')` | `q'`, `v'`, `b'`, `E'`, `DE'` in the same way, with expansions `coeff'`, `ψ'` |

For `q = 1` and `b = 1` the data are those of
`LocalTruncatedEisensteinInnerProductStatement`. The coefficients are entire
rather than smooth on `i(𝔞_P^G)^*`, because `E` is tied to the convergent series
on the regular region. Families with exponential coefficients `e^{⟨λ, u⟩}` arise
when the compact subgroup is changed (`eisensteinFiniteCompactChange` writes the
twist for one compact subgroup as such a sum of twists for another with the same
archimedean projection). The continuation of the original series gives the
regularity of such a sum near the parameters considered; the regularity of the
series of the separate pieces would require another argument.

The main term is unchanged: in it, `coeff` and `coeff'` are the coefficients of
`M(w, λ)φ(λ)` and `M(w', λ')φ'(λ')`, so `∑_{a,b} coeff · conj(coeff') · (ψ, ψ')_Q`
is `(M(w, λ)φ(λ), M(w', λ')φ'(λ'))_Q`, as in (2).

## Scope

The module states the proposition and does not prove it. Like
`LocalTruncatedEisensteinInnerProductStatement`, it does not assert the
holomorphy of Eisenstein series on `i𝔞_P^*` (Lapid's Proposition 6), Theorem 1,
the value of (2) on the singular hyperplanes, or any statement for non-standard
parabolic subgroups.
