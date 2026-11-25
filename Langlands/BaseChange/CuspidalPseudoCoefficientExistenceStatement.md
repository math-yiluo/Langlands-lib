# Existence of elliptic pseudo-coefficients for the discrete series of `GL_n(F)`

Module `Langlands.BaseChange.CuspidalPseudoCoefficientExistenceStatement`, declaration
`Langlands.BaseChange.CuspidalPseudoCoefficientExistenceStatement.{u, uV} : Prop`.
This `Prop`-valued definition states the existence result without proving it.

Sources: Kazhdan, *Cuspidal geometry of p-adic groups*, J. Analyse Math. 47 (1986),
Theorems A (printed pp. 2–3), J(b) and K (printed pp. 6–7); Henniart–Lemaire,
*Changement de base et induction automorphe pour GL_n en caractéristique non nulle*,
Mém. SMF 124 (2011), cited as HL: II.5.13, Proposition and Remarque (printed pp. 113–114),
and II.5.14, Proposition 2 (printed pp. 115–117), for `E = F`, `σ = 1`; II.4.10,
Lemme 1 (printed p. 93), and II.6.7 (printed pp. 123–124) for near-identity nonvanishing.

## The statement in words

Let `F` be a nonarchimedean local field of characteristic zero (`F : Type u` with
`[Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
[CharZero F]`) and `n : ℕ` with `0 < n`. The statement gives `GL_n(F) = GeneralLinear n F`
its Borel σ-algebra locally, as in the Library's `HasCharacterValue`.
`LocalFieldTopology.generalLinear_t2Space`, `generalLinear_locallyCompactSpace` and
`generalLinear_totallyDisconnectedSpace` provide the required topological instances.

Let `V : Type uV` be a complex vector space and `π : Representation ℂ (GL_n(F)) V` with
`hπ : IsAdmissible π`, `π.IsIrreducible` and `JacquetLanglands.IsSquareIntegrable π`
(square-integrability modulo the centre). Let `χ : Subgroup.center (GL_n(F)) →* ℂˣ` with
`HasCentralCharacterRep π χ`, and let `μ` be a Haar measure on `GL_n(F)`. Apart from
`0 < n`, these are the data of the Library's `Langlands.BaseChange.PseudoCoefficientExistenceStatement`,
which asserts (a) alone. Here one locally constant, compactly supported
`f : SchwartzBruhat (GL_n(F))` must satisfy all four clauses:

- (a) `IsPseudoCoefficient μ χ π hπ f`: the direct trace at `π` is `1`, and the trace at
  every irreducible admissible tempered representation of central character `χ`, with
  carrier in universe `uV` and not isomorphic to `π`, is `0`. See Kazhdan, Theorem K(a), and
  HL II.5.13 (the identity twist).
- (b) For every `B : GeneralLinear.BlockShape n` with `2 ≤ B.length` and every irreducible
  admissible `Ξ : Representation ℂ (B.Levi F) X` on a complex vector space `X : Type uV`, put
  `Ind_B(Ξ) = Induction.smoothInduced (B.parabolic F) (Ξ.comp (B.leviProjection F))`.
  For each proof `h` that this induction is admissible,
  `Character.distribution μ (Ind_B(Ξ)) h f = 0`. This is unnormalized induction of the
  inflated Levi representation from a proper standard upper block parabolic subgroup.
  No condition is put on the central character or temperedness of `Ξ`. See HL II.5.13,
  Remarque, and II.5.14, Proposition 2 (1), and the scope comparison below with
  Kazhdan's Theorems A and J(b).
- (c) `OrbitalIntegralsVanishOffElliptic μ ⇑f`: orbital integrals vanish at every regular
  semisimple element that is not regular elliptic, for every right Haar measure on the
  centralizer and every compatible quotient measure. See HL II.5.14, Proposition 2 (2),
  for `E = F`, and the definition of Kazhdan's `B(G)` on printed p. 6.
- (d) There is a neighbourhood `U ∈ nhds (1 : GL_n(F))` such that for every `γ ∈ U`
  with `IsRegularElliptic γ`, every right Haar measure `μγ` on `glCentralizer γ`, and every
  `νγ` with `QuotientIntegration.IsCompatible (glCentralizer γ) μ μγ νγ`,
  `orbitalIntegral γ νγ ⇑f ≠ 0`. This is the local input used in HL II.6.7.

### Why `0 < n`

HL fix `n ≥ 1` in II.1.2 (printed p. 55). At rank zero the sole element of `GL_0(F)`
has separable but not irreducible characteristic polynomial `1`, so it is regular
semisimple and not regular elliptic under the Library's predicates. Take the
one-dimensional trivial representation and the probability Dirac measures on the
group, centralizer and quotient, all of which are one-point spaces. The measures are
compatible since the quotient integration identity reduces to evaluation at `1`.
Clause (a) would force `f(1) = 1`, whereas (c) would force `f(1) = 0`.

## The compact lift from a fixed central character

HL take pseudo-coefficients in `C^∞_c(G, χ)`, with central covariance by `χ⁻¹`
and compact support modulo the centre. In this space (c) holds for every
pseudo-coefficient of the given representation: HL II.5.14, Corollaire 1, identifies
their orbital integrals, and Proposition 2 (2) gives vanishing for the one constructed
in II.5.13. In the Library's `C^∞_c(G)`, adding `h` whose weighted central
average `h_χ` is zero preserves (a) but can change the orbital integrals. The statement
therefore asks for one witness with (a)–(d), not for every pseudo-coefficient to have them.

For the lift, take such a source pseudo-coefficient `φ₀ ∈ C^∞_c(G, χ)` and let
`Ω = {g | v(det g) ∈ {0, …, n - 1}}` for the normalized valuation `v` of `F`.
Put `β = 1_Ω / vol(Z ∩ K)`, where `Z` is the centre and `K = GL_n(O_F)`.
Then `f = φ₀ β` is compactly supported and locally constant. Its central average with
weight `χ` is `φ₀`: the weight cancels the covariance and for each `g` exactly one
coset of central units satisfies `zg ∈ Ω`. Because `β` is constant on conjugacy
classes, the orbital integral of the lift is `β(γ)` times that of `φ₀` at `γ`.
This construction is not formalized here.

## Induced-trace vanishing and source conventions

In HL II.5.14, Proposition 2, induced-trace vanishing for a fixed central character
comes first and is used in the descent proving orbital vanishing. For the compact lift,
one can deduce (b) from (c): van Dijk's formula makes the induced character vanish
on regular elliptic classes, which do not meet the proper Levi. Harish-Chandra's local
integrability of characters and Weyl integration then give trace zero, with no need
to match the central character of the inducing data to `χ`. Clause (b) is explicit
because the global comparison uses it directly. All proper parabolics of `GL_n(F)`
are conjugate to ones of the stated form. The modulus twist relating normalized to
unnormalized induction preserves the family of irreducible admissible inducing
representations. Neither the Weyl integration formula nor van Dijk's formula is
formalized here.

Kazhdan's J(b) equates `B(G)` and `B'(G)` in Harish-Chandra's Schwartz space, testing
against tempered induction. His Theorem A (printed pp. 2–3) is the compact-support
analogue with general inducing data. The pairing of J(b) is `Tr π(f*)` with
`f*(g) = f(g⁻¹)` (printed pp. 2, 6). Inversion preserves the regular non-elliptic
locus and its orbital vanishing test, so one can compare with direct trace vanishing
by applying J(b) to `f*`. Theorem K(a) itself uses the direct trace normalization
in (a), in the compact-centre setting of §1.1 (printed p. 7).

## Nonvanishing near `1`

For HL's fixed-central-character pseudo-coefficient, the formula used in II.6.7
(II.4.10, Lemme 1) uses the complex conjugate of the character `Θ_π(γ)` on the regular
elliptic set with HL's measures. Kazhdan's Theorem K(b) is the compact-centre analogue,
not that fixed-central-character formula. The character is a nonzero constant on the
regular elliptic set near `1` (HL give Jacquet–Langlands as one reason), so the
conjugate is nonzero there. The cutoff `β` is nonzero near `1`, where `v(det g) = 0`,
so the compact lift retains this nonvanishing. Separately, changing the compatible
measures rescales the integral by a positive constant. No exact formula for the
elliptic orbital integral is stated in Lean.

In II.6.7 HL use the neighbourhood of nonvanishing, openness of the norm map near `1`,
and weak approximation to choose a global norm. One nonzero orbital integral at an
unspecified elliptic element would not supply the near-identity hypothesis they use.

## Scope and proof routes

HL prove II.5.14, Proposition 1 (2), on which Corollaire 1 rests, by a global argument
with the twisted Deligne–Kazhdan trace formula. A later proof must avoid appeals to
results that in turn use the statement being proved. `CharZero F` follows Kazhdan and
the programme's other base-change statements (on orbital integrals, twisted characters
and pseudo-coefficients). HL also
work in positive characteristic; the Library's separable characteristic-polynomial
test for regular semisimplicity agrees with HL's regularity here in characteristic zero.

The definitions are reused under their published names: `IsPseudoCoefficient` and
`HasCentralCharacterRep` (module `Langlands.BaseChange.PseudoCoefficient`), `glCentralizer`
and the Borel left-quotient instances `leftQuotientMeasurableSpace` and
`leftQuotient_borelSpace` (module `Langlands.BaseChange.OrbitalIntegral`), `orbitalIntegral`
(module `Langlands.TraceFormula.TwistedOrbital`), and `OrbitalIntegralsVanishOffElliptic`
(module `Langlands.BaseChange.EllipticOrbitalIntegral`).
