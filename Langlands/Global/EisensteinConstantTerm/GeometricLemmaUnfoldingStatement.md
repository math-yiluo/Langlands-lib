# The integration identity of the geometric lemma (statement)

Module `Langlands.Global.EisensteinConstantTerm.GeometricLemmaUnfoldingStatement`. It states
`Langlands.Global.GeometricLemmaUnfoldingStatement` as a proposition definition and proves
nothing about it. It also defines two helpers in namespace `Langlands.Global.AdelicGroupPoints`.
The statement is one of the two premises of the reduction
`Langlands.Global.eisensteinConstantTerm_of_convergence_of_unfolding` (module
`EisensteinConstantTerm.Reduction`).

## Source

J. Bernstein and E. Lapid, *On the meromorphic continuation of Eisenstein series*, J. Amer.
Math. Soc. 37 (2024), registered as `bernstein-lapid-2024-meromorphic-continuation-eisenstein`.

- Proof of Lemma 6.10, journal pp. 208–209 (PDF pages 22–23). After unfolding, BL reach
  `∫_{(U_Q ∩ wU_{P_w}w⁻¹)(F) \ U_Q(A)} φ_λ(w⁻¹ u γ g) du`. They write this as the integral over
  `u ∈ (U_Q ∩ wU_{P_w}w⁻¹)(A) \ U_Q(A)` of
  `∫_{(U_Q ∩ wU_{P_w}w⁻¹)(F) \ (U_Q ∩ wU_{P_w}w⁻¹)(A)} φ_λ(w⁻¹ v u γ g) dv`.
  The inner integral equals `∫_{(U_{P_w} ∩ w⁻¹U_Qw)(F) \ (U_{P_w} ∩ w⁻¹U_Qw)(A)} φ_λ(v w⁻¹ u γ g) dv`,
  which in turn equals `C_{P,P_w} φ_λ(w⁻¹ u γ g)`. Then BL use
  `M(w, λ)φ'_λ(g) = ∫_{(U_{Q_w} ∩ wU_{P_w}w⁻¹)(A) \ U_{Q_w}(A)} φ'_λ(w⁻¹ u g) du`
  `= ∫_{(U_Q ∩ wU_{P_w}w⁻¹)(A) \ U_Q(A)} φ'_λ(w⁻¹ u g) du`.
- Lemma 6.7 (3), journal p. 207 (PDF page 21): `U_Q ∩ wPw⁻¹ = U_Q ∩ wU_{P_w}w⁻¹` and
  `U_{Q_w} = (U_{Q_w} ∩ wU_{P_w}w⁻¹) U_Q`.

C. Mœglin and J.-L. Waldspurger, *Spectral decomposition and Eisenstein series* (1995),
registered as `moeglin-waldspurger-1995-spectral-decomposition`, chapter file
`06.1_pp_78_100_Definitions.pdf`, II.1.7, printed p. 93 (PDF page 16), formula (4). The unfolded
integral there runs over `U'(k) ∩ wP(k)w⁻¹ \ U'(A)`. This is the discrete group of the left
side below. MW (6) records `U'(k) ∩ wP(k)w⁻¹ = U'(k) ∩ wU(k)w⁻¹`.

The statement isolates this chain of equalities, from the integral over
`(U_Q ∩ wPw⁻¹)(F) \ U_Q(A)` to the intertwining integral over `U_{Q_w}`. It is stated for a
general function `h` in place of `φ_λ`, with the invariance properties of `φ_λ` that the chain
uses.

## Helpers

- `stabilizerRationalSubgroup F p j w`, for `p : P → G`, `j : V → G` and `w ∈ G(𝔸)`: the
  subgroup `V(F) ∩ w P(F) w⁻¹` of `V(𝔸)`. Here `V(𝔸)` is the adelic points of
  `SubgroupFunctor.range j`, `V(F)` is its principal subgroup, and `P(F)` is `rationalImage F p`.
  `mem_stabilizerRationalSubgroup_iff` unfolds membership. `isDiscrete_stabilizerRationalSubgroup`
  shows the subgroup is discrete, as a subgroup of the discrete `V(F)`.
- `stabilizerMeasure F p j w`: the measure on `(V(F) ∩ wP(F)w⁻¹) \ V(𝔸)` induced by the Library's
  `normalizedHaarMeasure` of `V(𝔸)`. The construction is `LeftCosetSpace.discreteQuotientMeasure`,
  exactly as the Library's `intertwiningMeasure` with `rationalImage F p` in place of `U(𝔸)`.
  The Library's `normalizedHaarMeasure` is Haar measure on `V(𝔸)` multiplied by the reciprocal
  of the total mass of the unrestricted rational quotient `V(F) \ V(𝔸)` (`quotientMassNormalizer`).
  That mass is never zero. If it is finite (finite positive covolume), the normalized Haar
  measure gives `V(F) \ V(𝔸)` mass one. If it is infinite, the factor is `0`, and the
  normalized Haar measure and `stabilizerMeasure` are both zero. Mathematically this is the
  case for `V = G_m` over `ℚ`, whose idèle class group has infinite Haar measure (the review of
  the first version of this candidate gave this example). For a general closed subgroup `j`,
  the helper therefore promises no normalization by mass one.
- In `GeometricLemmaUnfoldingStatement`, the helper is applied with `j = iV ≫ q`, the unipotent
  radical of a parabolic. Its rational quotient `V(F) \ V(𝔸)` is compact
  (`AdelicSubgroupPoints.compactSpace_rationalQuotient_range_unipotent`), so there the
  normalization is `vol(V(F) \ V(𝔸)) = 1`. This is BL's convention for unipotent groups (§2.2,
  p. 191, footnote 1). The same holds for the Library's `intertwiningMeasure` on the unipotent
  radical `V'` and for the measure on `U'(F) \ U'(𝔸)` in `subgroupConstantTerm`.

## Statement

The data are a number field `F` and connected reductive `G`, with the following.

- Parabolics `p : P → G` and `q : Q → G` with geometric unipotent radicals `iU : U → P` and
  `iV : V → Q`.
- A point `w` of `G` over the base, acting through `innerAdelicPoint F G w`.
- Parabolics `f ≫ p : P' → G` and `g' ≫ q : Q' → G`, with `f : P' → P` and `g' : Q' → Q`, and
  geometric unipotent radicals `iU' : U' → P'` and `iV' : V' → Q'`.
- `IsGeometricLemmaDatum p iU q iV f g' w`, so `P'(F) = (P(F) ∩ w⁻¹Q(F)w)U(F)` and
  `Q'(F) = (Q(F) ∩ wP(F)w⁻¹)V(F)`.
- The affineness and closed-immersion instances needed to form the objects below. They are the
  same as in `EisensteinConstantTermStatement`.

For every measurable `h : G(𝔸) → ℂ` with `h(u x) = h(x)` for `u ∈ U(𝔸)`
(`parabolicUnipotentImage F p iU`) and `h(z x) = h(x)` for `z ∈ P(F)` (`rationalImage F p`), and
every `y ∈ G(𝔸)`, suppose
`∫⁻ ‖h(w⁻¹ v̄ y)‖ₑ` over `(V(F) ∩ wP(F)w⁻¹) \ V(𝔸)` for `stabilizerMeasure` is finite. Then:

1. the function `x ↦ C_{U'} h(w⁻¹ x̄ y)` is integrable on `(V'(F) ∩ wU'(𝔸)w⁻¹) \ V'(𝔸)` for
   the Library's `intertwiningMeasure F (f ≫ p) iU' (iV' ≫ g' ≫ q) w`;
2. its integral equals `∫ h(w⁻¹ v̄ y)` over `(V(F) ∩ wP(F)w⁻¹) \ V(𝔸)`.

Here `C_{U'} = subgroupConstantTerm F (iU' ≫ f ≫ p)` is the constant term along `U'` with the
mass-normalized measure on `U'(F) \ U'(𝔸)`. This measure has mass one because `U'` is a unipotent
radical, so its rational quotient is compact. Bars denote the chosen representatives `Quotient.out`.
The integrands do not depend on these choices: `h` is left `P(F)`-invariant and
`w⁻¹(V(F) ∩ wP(F)w⁻¹)w ⊆ P(F)`; and `C_{U'}h` is left `U'(𝔸)`-invariant, because the quotient
measure on `U'(F) \ U'(𝔸)` is invariant under right translation.

## Correspondence with the source

- `h` plays the role of `φ_λ`, left invariant under `U_P(A)` and `P(F)`. The twist is not part
  of the statement. The reduction applies the statement to `h = φ_λ` and matches
  `C_{U'}(φ_λ) = (C_{U'} φ)_{λ|}` separately (`Height.lean`).
- The left side is BL's `∫_{(U_Q ∩ wU_{P_w}w⁻¹)(F) \ U_Q(A)} φ_λ(w⁻¹ u γ g) du` at `y = γ g`,
  with the discrete group written as `V(F) ∩ wP(F)w⁻¹`. By BL Lemma 6.7 (3) this is
  `(U_Q ∩ wPw⁻¹)(F) = (U_Q ∩ wU_{P_w}w⁻¹)(F)`.
- The right side is `[M(w, λ) C_{P,P_w} φ]_{wλ}(γ g)` in the form of the Library's
  `intertwiningIntegral`. That is an integral over `(V'(F) ∩ wU'(𝔸)w⁻¹) \ V'(𝔸)` for the
  normalized Haar measure of `V'(𝔸)`. The integrand `C_{U'}h(w⁻¹ v y)` is left invariant under
  `(V' ∩ wU'w⁻¹)(𝔸)`, so this agrees with BL's integral over
  `(U_{Q_w} ∩ wU_{P_w}w⁻¹)(A) \ U_{Q_w}(A)`.
- The integrability hypothesis and conclusion 1 express the absolute convergence that BL leave
  implicit ("taken in their range of convergence").

## Why the statement is expected to hold

The statement does not follow formally from the Library's definitions. It needs the structure
of the groups on adelic points, which the hypotheses fix only through rational points. This is
the reason it is a separate premise. The expected proof follows BL. The groups `P'` and `Q'`
are connected and smooth over a field of characteristic zero, so their rational points are
Zariski dense and determine them. Hence `P' = P_w` and `Q' = Q_w` in BL's sense, for the parabolics
`P`, `Q` and the point `w`. After conjugation to standard position, BL Lemma 6.7 (3) gives the
decompositions:

- `V ∩ wPw⁻¹ = V ∩ wU'w⁻¹ =: N`;
- `V' = (V' ∩ wU'w⁻¹) V`, with intersection `N`;
- `U' = (U' ∩ w⁻¹Vw) U`.

These hold for the unipotent groups and for their rational and adelic points, since Galois
cohomology of unipotent groups vanishes. Weil's integration formula for the unipotent groups
`N ⊆ V`, `N' = V' ∩ wU'w⁻¹ ⊆ V'` and `U' ∩ w⁻¹Vw ⊆ U'` then finishes the proof. All Haar measures
are normalized by mass one on the rational quotients (compact, since the groups are unipotent),
and conjugation by the rational point `w`
preserves these measures. With these, both sides become
`∫_{N(𝔸) \ V(𝔸)} C_{U'}h(w⁻¹ v y) dv`. This sketch is explanatory. Nothing is proved here.

## Scope

The statement covers one double coset representative. Sums over representatives, the
Eisenstein series, and the twist by `λ` are handled in the reduction.
