# The elliptic case of Harish-Chandra's Theorem 1.1

The module `Langlands.HarmonicAnalysis.UnitConjugation.EllipticRegularOrbitalFourierRegularityStatement`
states, as the proposition
`Langlands.HarmonicAnalysis.EllipticRegularOrbitalFourierRegularityStatement.{u, v}`, the
local summability part of Harish-Chandra's Theorem 1.1 for the elliptic regular elements of the
Lie algebra `A` of the unit group `Aˣ` of a finite-dimensional semisimple algebra over a
nonarchimedean local field of characteristic zero. The statement is **not** proved here.

## Statement

`EllipticRegularOrbitalFourierRegularityStatement.{u, v}` has exactly the binders, hypotheses
and conclusion of `RegularOrbitalFourierRegularityStatement.{u, v}`
(`Langlands.HarmonicAnalysis.UnitConjugation.RegularOrbitalFourierRegularityStatement`), with
one more hypothesis on the regular element `X ∈ regularSet F A`: `IsEllipticElement X`
(`Langlands.HarmonicAnalysis.UnitConjugation.EllipticElement`), every idempotent of `A`
commuting with `X` is central. It quantifies over

- a nonarchimedean local field `F : Type u` of characteristic zero; a finite-dimensional
  semisimple `F`-algebra `A : Type v` with its module topology and Borel σ-algebras on `A` and
  on `Aˣ`; `ψ : UnitaryAdditiveCharacter F`; `B : LinearMap.BilinForm F A` with
  `hB : IsInvariantPairing B`; `μ : AdditiveHaarMeasure A`;
- `X ∈ regularSet F A` with `IsEllipticElement X`;
- a Borel σ-algebra on `LeftQuotient (conjugationCentralizer X)`, a Haar measure `μG` on `Aˣ`,
  a right-invariant Haar measure `μH` on the centralizer `C = conjugationCentralizer X`, and a
  quotient measure `ν` on `C \ Aˣ` with `QuotientIntegration.IsCompatible C μG μH ν`;
- `hconv : OrbitalIntegralConverges X ν`.

The claim: there is `Θ : A → ℂ` with `LocallyIntegrable Θ μ.measure` and

`distributionFourier ψ hB.isSymm hB.nondegenerate μ (orbitalDistribution X ν hconv) f =
  ∫ Y, Θ Y * f Y ∂μ.measure`

for every Schwartz–Bruhat function `f`: `μ̂_X(f) = μ_X(f̂) = ∫ Θ f dμ`.

## Source

Harish-Chandra, *Admissible invariant distributions on reductive p-adic groups*, with notes by
S. DeBacker and P. J. Sally, Jr., University Lecture Series 16, AMS, 1999, source ID
`harish-chandra-1999-admissible-invariant-distributions` (PDF page = printed page + 15):

- §1, printed p. 5 (PDF p. 20): the definition of elliptic Cartan subalgebras and Theorem 1.1
  (Theorem 8): "The distribution `f ↦ φ_{f̂}(H₀)` (`f ∈ D`) is a locally summable function on
  `g` which is locally constant on `g'`", for `H₀ ∈ h'`.
- §1.4, printed pp. 10–11 (PDF pp. 25–26): the reduction of Theorem 1.1 to the case of an
  elliptic `h`, ending "So in order to complete the proof of Theorem 1.1 we may assume that `h`
  is elliptic."
- §§1.5–1.6, printed pp. 11–13 (PDF pp. 26–28): the elliptic case. For an elliptic `h`, `g_h`
  the saturation `(h')^G` and `g ∈ C_c^∞(g_h)`, Lemma 1.15 and Corollary 1.16 define the
  invariant distribution `Θ: f ↦ ∫_{G/Z} dx* ∫_g f(X) ĝ(x.X) dX`; `ĝ` is a cusp form
  (Lemma 1.17), and Theorem 1.18 (Theorem 9) says that `Θ` is a locally summable function on
  `g`, locally constant on `g'`. Lemma 1.19 (Lemma 2), whose proof uses Corollary 1.3, a
  consequence of Howe's finiteness theorem, gives for each open compact `ω` a
  `g ∈ C_c^∞(g_h)` with `Θ(f) = φ_{f̂}(H₀)` for `f ∈ C_c^∞(ω)`; "The first statement of
  Theorem 1.1 is now a consequence of Theorem 1.18 and Lemma 1.19" (printed p. 13).

The statement is the first statement of Theorem 1.1 for elliptic `h`, with `H₀ = X` and the
correspondence explained in the Markdown of `RegularOrbitalFourierRegularityStatement`: the
centralizer `h` of the regular `X` is the Cartan subalgebra containing `X`, and `X` is elliptic
in the sense of `IsEllipticElement` exactly when `h` is elliptic (see the Markdown of
`Langlands.HarmonicAnalysis.UnitConjugation.EllipticElement`). For elliptic `h` the split
component `A_h` of the Cartan subgroup `C` is the split component `Z` of the centre, `C/Z` is
compact, and `φ_{f̂}(X) = |η(X)|^{1/2} vol(C/Z) μ_X(f̂)` with a positive constant, so the local
summability of `f ↦ φ_{f̂}(X)` is that of `μ̂_X`.

Clauses not stated here: the local constancy of `Θ` on `g'` and the local boundedness of
`|η|^{1/2} Θ`.
