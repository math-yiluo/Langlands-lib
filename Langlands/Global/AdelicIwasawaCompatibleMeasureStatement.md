# Existence of Iwasawa-compatible Haar measures on `M(𝔸)`

Module `Langlands.Global.AdelicIwasawaCompatibleMeasureStatement` states one
proposition, `Langlands.Global.IwasawaCompatibleMeasureExistenceStatement`.
It proves nothing.

## Statement

The data are those of the published
`Langlands.Global.BoundedWavePacketNormBoundStatement` (Lapid's Lemma 10)
up to the measure, without the Levi projection: a number field `F`, a
connected reductive `G`, a parabolic `p : P → G` with geometric unipotent
radical `iU : U → P` and rational Levi `l : M → P`, a split component
`a : A → M` with a compatible root presentation
`ParabolicRootPresentation p l a`, and a maximal compact subgroup `K` of
`G(𝔸)` with `hK : IsIwasawaCompact p K` (`P(𝔸) K = G(𝔸)`). The instance
binders `[IsAffine U.X.left]` and `[IsClosedImmersion (iU ≫ p).hom.hom.left]`
are those that the predicate `IsIwasawaCompatibleMeasure` requires.

The conclusion: there is a Haar measure `μM` on `M(𝔸)` with
`IsIwasawaCompatibleMeasure K hK.isCompact p iU l μM`. That predicate (module
`Langlands.Global.AdelicInducedInnerProduct`) says that for every compactly
supported continuous `f : G(𝔸) → ℂ`,

`∫_{G(𝔸)} f d(haar) = ∫_K ∫_{M(𝔸)} ∫_{U(𝔸)} m^{-2ρ_P} f(u m k) du dμM(m) dk`,

where `haar` is Mathlib's Haar measure on `G(𝔸)`, `du` the Haar measure on
`U(𝔸)` with `vol(U(F) \ U(𝔸)) = 1` and `dk` the Haar probability measure on
`K`. Here `m^{-2ρ_P} = δ_P(m)⁻¹`.

## Source

C. Mœglin and J.-L. Waldspurger, *Spectral Decomposition and Eisenstein
Series*, Cambridge University Press (1995), registered as
`moeglin-waldspurger-1995-spectral-decomposition`, chapter file
`05.1_pp_1_18_Hypotheses_and_general_notation.pdf`, I.1.13, printed p.18
(PDF p.18): Haar measures on `U(𝔸)` and `M` are fixed, `K` has measure 1,
and `∫_G f(g) dg = ∫_{U(𝔸) × M × K} f(u m k) m^{-2ρ_P} dk dm du`.

## Correspondence with the source

The Markdown of `AdelicInducedInnerProduct` explains this already:
Haar measures on `M(𝔸)` are unique up to a positive scalar, and both
sides of the formula are positive functionals. So a compatible Haar measure
exists exactly when the formula holds with some positive constant for one
Haar measure on `M(𝔸)`. That is the published (unproved)
`Langlands.Global.AdelicGroupPoints.AdelicIwasawaIntegrationStatement`
(module `Langlands.Global.AdelicIwasawaIntegrationStatement`), stated for the
groups that represent a dynamic parabolic `P_G(χ)`, its Levi `Z_G(χ)` and its
unipotent radical `U_G(χ)`, with Mathlib's Haar measures on `M(𝔸)` and `U(𝔸)`.
A route from that statement:

1. A compatible root presentation gives a standard cocharacter `ζ` with
   `range p = P_G(ζ)` and `range (l ≫ p) = Z_G(ζ)` (field `realization`).
   The radical `iU ≫ p` represents `U_G(ζ)`: the Library proves
   `range (iU ≫ p) = U_G(ζ)` for a geometric unipotent radical (as used in
   `parabolicRadical_isIso_subgroupMultiplication`, module
   `Langlands.Representation.Plancherel.ParabolicRepresentedComparison`).
2. Write `du₀`, `dm₀` for Mathlib's Haar measures on `U(𝔸)` and `M(𝔸)`, and
   `I₀(f)` for the iterated integral of `AdelicIwasawaIntegrationStatement`
   with these measures, so that `∫ f dg = c · I₀(f)` with `c > 0`. The
   normalized Haar measure on `U(𝔸)` (`vol(U(F) \ U(𝔸)) = 1`) is
   `du_norm = b · du₀` for some `b > 0`, since `U(F) \ U(𝔸)` is compact
   with positive finite quotient mass.
3. `parabolicModulus` agrees with `m ↦ m^{2ρ_P}` on `M(𝔸)`.
4. Take `μM = (c / b) · dm₀`. The right side of `IsIwasawaCompatibleMeasure`
   is linear in each measure, so it equals `b · (c / b) · I₀(f) = c · I₀(f)`,
   which is `∫ f dg`.

This route is explanatory and not proved here.

The differences from MW are those recorded in the Markdown of
`AdelicIwasawaIntegrationStatement`. MW work with finite central covers and
fix the compact subgroup `K` in I.1.1 and I.1.4 (pp. 1–2 and 4). The statement
is the number-field case of the trivial cover, on the actual adelic points,
and it assumes the factorization `G(𝔸) = P(𝔸) K` for the supplied `K` directly
(`IsIwasawaCompact`). MW take `P` standard and `dg` defined by the formula for
`P₀`. Here `P` is any presented parabolic, and `dg` is Mathlib's Haar measure,
so only the measure on `M(𝔸)` is to be found.

## Provenance

Derived. MW I.1.13 fixes the measures so that the formula holds. The
statement asks for the Haar measure on `M(𝔸)` that makes it hold for
Mathlib's Haar measure on `G(𝔸)`. That is the hypothesis
`IsIwasawaCompatibleMeasure` of the published
`BoundedWavePacketNormBoundStatement` (Lapid's Lemma 10), whose
normalization of `(·,·)_P` depends on it. It is stated for Lapid's
Proposition 6 (`EisensteinImaginaryAxisHolomorphyStatement`): the reduction in
`AdelicEisensteinImaginaryHolomorphyReduction` applies Lemma 10 to the data of
that statement, where no measure on `M(𝔸)` is given.

## Scope

Only existence is stated. Uniqueness, which holds because Haar measures are
unique up to scalars and the formula fixes the scalar, is not stated.
