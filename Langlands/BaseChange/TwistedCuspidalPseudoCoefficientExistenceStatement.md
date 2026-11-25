# Existence of σ-elliptic twisted pseudo-coefficients for the σ-discrete series of `GL_n(E)`

Module `Langlands.BaseChange.TwistedCuspidalPseudoCoefficientExistenceStatement`, declaration
`Langlands.BaseChange.TwistedCuspidalPseudoCoefficientExistenceStatement.{u, v, uW} : Prop`.
This `Prop`-valued definition states the existence result without proving it.

Sources: Henniart–Lemaire, *Changement de base et induction automorphe pour GL_n en
caractéristique non nulle*, Mém. SMF 124 (2011), cited as HL: II.5.13, Proposition and
Remarque (printed pp. 113–114), II.5.14, Proposition 2 and Corollaire 2 (printed pp. 115–117),
and II.2.4, Remarque (printed p. 65), with I.2.7. Arthur–Clozel, *Simple Algebras, Base Change,
and the Advanced Theory of the Trace Formula* (1989), cited as AC: Chapter 1, Corollary 2.10
and Lemma 2.12 (ii) with its proof (printed pp. 18–19).

## The statement in words

Let `F` be a nonarchimedean local field of characteristic zero (`F : Type u` with
`[Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
[CharZero F]`). Let `E : Type v` be a field with `[Algebra F E] [TopologicalSpace E]
[IsTopologicalRing E] [IsModuleTopology F E]`, and let `σ : E ≃ₐ[F] E` and `l : ℕ` with
`hE : IsCyclicAlgebra σ l`. Thus `E` is a finite, reduced `F`-algebra of dimension `l`,
with `σ` of order `l` and fixed algebra `F`. Let `n : ℕ` with `0 < n`.

The statement takes `Module.Finite F E` from `hE` and gives `GL_n(E) = GeneralLinear n E`
its Borel σ-algebra locally, as in the Library's `HasCharacterValue`. The Hausdorff, locally
compact and totally disconnected instances come from `generalLinear_t2Space_of_finite`,
`generalLinear_locallyCompactSpace_of_finite` and `generalLinear_totallyDisconnectedSpace_of_finite`
(`Langlands.BaseChange.TwistedCharacter`).

Let `W : Type uW` be a complex vector space and `τ : Representation ℂ (GL_n(E)) W` with
`hτ : IsAdmissible τ` and `IsSigmaDiscreteSeries σ n τ`. Let
`χ : Subgroup.center (GL_n(E)) →* ℂˣ` with `HasCentralCharacterRep τ χ`, let
`A : SigmaIntertwiner σ n τ` be an isomorphism of `τ` onto `τ^σ = τ ∘ entrywiseAut σ n`,
and let `μ` be a Haar measure on `GL_n(E)`. Apart from `0 < n`, these are the data of the
Library's `Langlands.BaseChange.TwistedPseudoCoefficientExistenceStatement`,
which asserts (a) alone. Its Markdown writes `Π` (as HL do) for the representation called
`τ` here. One locally constant, compactly supported `φ : SchwartzBruhat (GL_n(E))` must
satisfy all four clauses:

- (a) `IsTwistedPseudoCoefficient μ (entrywiseAut σ n) χ τ hτ A φ`: the twisted trace
  at `(τ, A)` is `1`. The twisted trace is `0` at each irreducible admissible tempered
  representation of central character `χ`, with carrier in universe `uW` and not
  isomorphic to `τ`, for every isomorphism of that representation onto its σ-twist.
  The type of `A` is `τ.Equiv (τ.comp (entrywiseAut σ n).toMonoidHom)`, as required by
  `IsTwistedPseudoCoefficient`. See HL II.5.13 and AC Chapter 1, Corollary 2.10.
- (b) For every `B : GeneralLinear.BlockShape n` with `2 ≤ B.length` and every
  irreducible admissible `Ξ : Representation ℂ (B.Levi E) X` on a complex vector space
  `X : Type uW` with `IsLeviSigmaStable σ B Ξ`, put
  `Ind_B(Ξ) = Induction.smoothInduced (B.parabolic E) (Ξ.comp (B.leviProjection E))`.
  If `Ind_B(Ξ)` is irreducible, then for every `h : IsAdmissible (Ind_B(Ξ))` and every
  `A' : SigmaIntertwiner σ n (Ind_B(Ξ))`,
  `twistedDistribution μ (Ind_B(Ξ)) h A'.toLinearMap φ = 0`. This is unnormalized
  induction of the inflated Levi representation from a proper standard upper block
  parabolic. See HL II.5.13, Remarque, and II.5.14, Proposition 2 (1), and the proof of
  AC Lemma 2.12.
- (c) `SigmaOrbitalIntegralsVanishOffElliptic σ l μ ⇑φ`: the twisted orbital integrals
  vanish at every σ-regular element that is not σ-elliptic, for every right Haar
  measure on the σ-centralizer and every compatible quotient measure. See HL II.5.14,
  Proposition 2 (2), and AC Lemma 2.12 (ii), first half.
- (d) There is a nonempty open set `V` of `GL_n(E)` such that every `δ ∈ V`
  satisfies `IsSigmaElliptic σ l δ`, and for every `δ ∈ V`, every right Haar measure
  `μδ` on `sigmaCentralizer σ n δ`, and every `νδ` with
  `QuotientIntegration.IsCompatible (sigmaCentralizer σ n δ) μ μδ νδ`,
  `sigmaOrbitalIntegral σ n δ νδ ⇑φ ≠ 0`. See HL II.5.14, Corollaire 2, and AC
  Lemma 2.12 (ii), second half, together with the local constancy cited above.

## The compact lift from a fixed central character

HL and AC take their twisted pseudo-coefficients in `C^∞_c(G(E), χ)`, with central
covariance by `χ⁻¹` and compact support modulo the centre. HL II.5.14, Corollaire 1,
identifies the regular twisted orbital integrals of any two such pseudo-coefficients
of the same pair, so Proposition 2 (2) gives (c) for all of them. In the Library's
`C^∞_c(G(E))` (`Langlands.BaseChange.PseudoCoefficient`), adding `h` with weighted central average `h_χ = 0` preserves
(a) but can change the orbital integrals. The statement therefore asks for one
witness with (a)–(d). Changing a source intertwiner to a nonzero scalar multiple,
as allowed by Schur's lemma for the admissible irreducible `τ`, is compensated by
scaling the test function by the inverse scalar, without changing orbital vanishing
or nonvanishing.

Take such a source pseudo-coefficient `φ₀ ∈ C^∞_c(G(E), χ)`. Let
`Ω = {g | v(det g) ∈ {0, …, n - 1}}` for the normalized valuation `v` of `E`, and put
`β = 1_Ω / vol(Z ∩ K)` for `Z` the centre and `K = GL_n(O_E)`. Then `φ = φ₀ β` is
compactly supported and locally constant. Its average over `Z` with weight `χ` is
`φ₀`, since the weight cancels the covariance and the valuation condition picks
one coset of central units. The cutoff is constant on σ-conjugacy classes because
`det(x⁻¹ δ x^σ) = det(x)⁻¹ det(δ) σ(det x)` and `v ∘ σ = v`. Thus the twisted orbital
integral at `δ` is that of `φ₀` multiplied by `β(δ)`. This lift is not formalized here.

## Induced-trace vanishing

HL II.5.14, Proposition 2, and AC Lemma 2.12 first establish induced-trace vanishing
for the fixed-central-character function and use it in descent to prove orbital
vanishing. For the compact lift, one can deduce (b) from (c) without matching the
central character: the twisted induced-character formula makes the character with
the induced intertwiner vanish on the σ-elliptic set, and local integrability
(AC Chapter 1, Proposition 2.2, printed p. 11) and twisted Weyl integration give
trace zero. Clause (b) is explicit because the global comparison uses it directly.
Neither the induced intertwiner nor the twisted Weyl integration formula is defined here.

- `IsLeviSigmaStable σ B Ξ` asks for an isomorphism of `Ξ` onto its entrywise σ-twist.
  Without this restriction, for a quadratic twist the induction of `ξ ⊗ ξ^σ` with
  `ξ^σ ≇ ξ` can itself be σ-discrete, so its twisted trace need not vanish at `φ`.
- The sources use the intertwiner induced from the σ-isomorphism of `Ξ` (HL's group
  `G_ind(G(E), χ, σ)`, II.5.14, printed p. 115). For irreducible admissible `Ind_B(Ξ)`
  Schur's lemma makes every `A'` a scalar multiple of this one. For reducible induction,
  an arbitrary `A'` could act differently on the constituents. The admissibility
  proof `h` is an input to the trace, not a conclusion.

## Nonvanishing on an open set

AC Lemma 2.12 (ii) gives a σ-elliptic `δ` with nonzero twisted orbital integral for
`φ₀`: otherwise orbital vanishing off the σ-elliptic set and the twisted Weyl formula
would force trace zero, contrary to the normalization at `(τ, A)`. HL II.5.14,
Corollaire 2, uses the same nonvanishing argument to obtain σ-ellipticity of the
representation. The cutoff need not be nonzero at the original `δ`. Multiply `δ`
by a central scalar `z ∈ Eˣ` so that `v(det(z δ)) = v(det δ) + n v(z)` lies in
`{0, …, n - 1}`. The associated norm is scaled by `N_{E/F}(z)`, which preserves
regular ellipticity. The σ-centralizer is unchanged and central covariance scales
the orbital integral of `φ₀` by `χ(z)⁻¹`. Thus it is nonzero at `z δ`, where the
cutoff is nonzero too.

The σ-elliptic locus is open. Local constancy of twisted orbital integrals for compact
functions on the σ-regular set (HL II.2.4, Remarque, and I.2.7, with measures of
maximal compact subgroups of σ-centralizers normalized to one) now gives a nonempty
open set for the compact lift. Changing compatible measures only multiplies the
orbital integral at each element by a positive constant, so the same set works for
all compatible measures. The statement does not assert an exact orbital value.

HL II.6.16 (printed pp. 131–132) is the twisted application: local σ-elliptic elements
with nonzero twisted orbital integrals give neighbourhoods for choosing a global
`δ` by approximation. HL II.6.7 instead uses ordinary orbital integrals to choose a
global norm. Neither global application is used here to justify local existence.

### Why `0 < n`

HL fix `n ≥ 1` in II.1.2 (printed p. 55). At rank zero, the characteristic polynomial
`1` of the only element of `GL_0(F)` is not irreducible, so no element of `GL_0(E)` can
be associated to a regular elliptic element of `GL_0(F)`. The nonempty σ-elliptic open
set of (d) cannot exist at rank zero.

## Scope and proof routes

HL prove II.5.14, Proposition 1 (2), on which Corollaire 1 rests, by a global argument
with the twisted Deligne–Kazhdan trace formula. AC prove Lemma 2.12 by local descent.
A later proof must avoid results that in turn require the statement being proved.
The field hypothesis on `E` excludes the split case `E = F^l`, which the Library
treats separately (`Langlands.BaseChange.SplitPlace`). `CharZero F` follows AC and other
base-change statements of the Library (for instance `RegularTransferStatement`,
`TwistedCharacterRegularValuesStatement` and `TwistedPseudoCoefficientExistenceStatement`). HL also work in positive characteristic; the Library's separable
characteristic-polynomial test for regular semisimplicity agrees with HL's regularity
here in characteristic zero.

The definitions are reused under their published names: `IsCyclicAlgebra`,
`IsSigmaElliptic` and `entrywiseAut` (`Langlands.BaseChange.Norm`); `sigmaCentralizer`, `sigmaOrbitalIntegral`
and the Borel left-quotient instances `leftQuotientMeasurableSpace`, `leftQuotient_borelSpace`
(`Langlands.BaseChange.OrbitalIntegral`); `twistedDistribution`
(`Langlands.BaseChange.TwistedCharacter.Basic`); `SigmaIntertwiner` and the `_of_finite` topology
lemmas (`Langlands.BaseChange.TwistedCharacter`); `IsTwistedPseudoCoefficient`, `HasCentralCharacterRep`,
`IsLeviSigmaStable` and `IsSigmaDiscreteSeries` (`Langlands.BaseChange.PseudoCoefficient`); and
`SigmaOrbitalIntegralsVanishOffElliptic` (`Langlands.BaseChange.EllipticOrbitalIntegral`).
