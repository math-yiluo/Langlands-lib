# Test functions killing properly induced twisted traces have σ-elliptic orbital integrals

Module `Langlands.BaseChange.ProperInducedVanishingOrbitalStatement`, declaration
`Langlands.BaseChange.ProperInducedVanishingOrbitalStatement.{u, v, uW} : Prop`.
This `Prop`-valued definition states the result without proving it. Nothing in the module is
proved.

Sources: Arthur–Clozel, *Simple Algebras, Base Change, and the Advanced Theory of the Trace
Formula* (1989), cited as AC: Chapter 1, Lemma 2.12 (ii) and its proof (printed p. 19), with the
descent argument in the proof of Proposition 2.7 (printed pp. 15–17). Henniart–Lemaire,
*Changement de base et induction automorphe pour GL_n en caractéristique non nulle*, Mém. SMF
124 (2011), cited as HL: II.5.14, proof of Proposition 2 (2) (printed pp. 116–117), with
II.4.5, formulas (1) and (2) and Remarque, for descent.

## The statement in words

Let `F` be a nonarchimedean local field of characteristic zero (`F : Type u` with
`[Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
[CharZero F]`). Let `E : Type v` be a field with `[Algebra F E] [TopologicalSpace E]
[IsTopologicalRing E] [IsModuleTopology F E]`, and let `σ : E ≃ₐ[F] E` and `l r : ℕ` with
`hE : IsCyclicAlgebra σ l`. Put `n = r + 1`. The statement takes `Module.Finite F E` from
`hE.1`, the Hausdorff, locally compact and totally disconnected structures on
`GeneralLinear (r + 1) E` from `generalLinear_t2Space_of_finite`,
`generalLinear_locallyCompactSpace_of_finite` and `generalLinear_totallyDisconnectedSpace_of_finite`,
and the Borel σ-algebra with its `BorelSpace` instance, as
`SigmaDiscreteEllipticOrbitalTestStatement` does.

Let `μ` be a Haar measure on `GL_n(E)` and `φ : SchwartzBruhat (GL_n(E))`. Assume:

- for every `B : GeneralLinear.BlockShape (r + 1)` with `2 ≤ B.length`, every complex vector
  space `X : Type uW` and every `Ξ : Representation ℂ (B.Levi E) X` with `IsAdmissible Ξ`,
  `Ξ.IsIrreducible` and `IsLeviSigmaStable σ B Ξ`, writing
  `Ind_B(Ξ) = Induction.smoothInduced (B.parabolic E) (Ξ.comp (B.leviProjection E))`: if
  `Ind_B(Ξ)` is irreducible, then for every `h : IsAdmissible (Ind_B(Ξ))` and every
  `A' : SigmaIntertwiner σ (r + 1) (Ind_B(Ξ))`,
  `twistedDistribution μ (Ind_B(Ξ)) h A'.toLinearMap φ = 0`.

Then `SigmaOrbitalIntegralsVanishOffElliptic σ l μ ⇑φ`: for every `δ` with
`IsSigmaRegular σ l δ` and not `IsSigmaElliptic σ l δ`, every right Haar measure on the
σ-centralizer of `δ` and every quotient measure compatible with it and with `μ`, the σ-orbital
integral of `φ` at `δ` is `0`.

The hypothesis is, word for word at `n = r + 1`, clause (b) of the Library's
`TwistedCuspidalPseudoCoefficientExistenceStatement` and of
`SigmaDiscreteProperInducedVanishingTestStatement`.

## Library notation

- `BlockShape`, `B.Levi E`, `B.parabolic E`, `B.leviProjection E` (module
  `Langlands.Group.GL.Blocks`): ordered positive block sizes with sum `n`, the product of the
  groups `GL_{n_i}(E)`, the standard upper block triangular subgroup of `GL_n(E)` and its
  projection onto the block diagonal.
- `Induction.smoothInduced P ρ` (module `Langlands.Representation.Induction.Definitions`):
  unnormalized smooth induction, right translation on the smooth `f` with `f(p x) = ρ(p) f(x)`.
- `IsLeviSigmaStable σ B Ξ` (module `Langlands.BaseChange.PseudoCoefficient`): `Ξ` is isomorphic
  to its entrywise σ-twist.
- `SigmaIntertwiner`, `twistedDistribution` (modules `Langlands.BaseChange.TwistedCharacter`,
  `Langlands.BaseChange.TwistedCharacter.Basic`): an isomorphism onto the σ-twist, and
  `φ ↦ tr(Π(φ) ∘ A')`.
- `IsSigmaRegular`, `IsSigmaElliptic` (module `Langlands.BaseChange.Norm`): `δ` is associated with
  a regular semisimple, respectively regular elliptic, element of `GL_n(F)`.
- `SigmaOrbitalIntegralsVanishOffElliptic` (module `Langlands.BaseChange.EllipticOrbitalIntegral`).

## Design

- **Compactly supported functions.** AC Proposition 2.7 is a density theorem for `C^∞_c(G(E))`
  itself; HL work in `C^∞_c(G(E), χ)` and pass between the two by Fourier analysis on the
  centre. The statement is for compactly supported `φ` with no central character, as the
  Library's test functions are.
- **Irreducible induced representations only.** The hypothesis concerns only irreducible
  `Ind_B(Ξ)`. The proof route below only meets such representations: normalized induction of an
  irreducible tempered representation of a Levi subgroup of `GL_n(E)` is irreducible
  (Zelevinsky 1980, Theorem 9.7: the segments of tempered representations are not linked). With this premise the hypothesis is exactly what HL's and AC's
  vanishing on properly induced representations gives, through Schur's lemma; see
  `SigmaDiscreteProperInducedVanishingTestStatement`.
- **Unnormalized induction.** For the modulus character `δ_B` of the parabolic, the normalized
  induction of `Ξ₀` is `Ind_B(Ξ₀ ⊗ δ_B^{1/2})`, and `δ_B` is invariant under entrywise `σ` since
  `|σ(x)|_E = |x|_E`. So `Ξ₀ ⊗ δ_B^{1/2}` is irreducible admissible and σ-stable when `Ξ₀` is.
- **Carrier universe.** The inducing representation is quantified on `Type uW`. An irreducible
  admissible representation of the Levi product has countable dimension (it is the union of its
  finite-dimensional fixed spaces under a countable basis of compact open subgroups), so it is
  isomorphic to a representation on a carrier in any universe.
- **`n = r + 1`.** The setting is that of `SigmaDiscreteEllipticOrbitalTestStatement`. At
  `r = 0` the hypothesis is empty, and so is the conclusion's content: the characteristic
  polynomial of an element of `GL_1(F)` has degree one, so every regular semisimple element of
  `GL_1(F)` is regular elliptic and every σ-regular element of `GL_1(E)` is σ-elliptic.

## Provenance and proof route

This is a derived statement: the descent half of AC Lemma 2.12 (ii) and of HL II.5.14,
Proposition 2 (2), stated for any test function with the vanishing property, not only for a
pseudo-coefficient. AC's proof of Lemma 2.12 says that the descent argument in the proof of
Proposition 2.7 gives the vanishing off the σ-elliptic set, because `tr(Π(φ) I_σ) = 0` for every
σ-stable `Π` properly induced from a σ-stable representation. In detail:

1. **Descent of orbital integrals.** Let `δ` be σ-regular and not σ-elliptic. Then `δ` is
   σ-conjugate into a proper standard Levi subgroup `M(E) = G_α(E)`, `l(α) > 1`, where it is
   σ-elliptic (HL II.5.14, printed p. 116). The descent formula (AC proof of Proposition 2.7;
   HL II.4.5, formula (1) and Remarque) writes the σ-orbital integral of `φ` at `δ` as a nonzero
   constant times the σ-orbital integral in `M(E)` of the twisted constant term `φ_{P,σ}`, a
   locally constant compactly supported function on `M(E)`. The constant and the choice of
   compatible measures do not affect vanishing.
2. **Density on the Levi subgroup.** If that orbital integral is nonzero, the twisted density
   theorem for `M(E)`, a product of general linear groups (AC Proposition 2.7, proved by descent
   and a global argument; HL II.5.14, Proposition 1 (2), with fixed central character, after the
   Fourier argument on the centre of HL printed p. 116), gives an irreducible tempered
   σ-stable `Ξ₀` of `M(E)` with an isomorphism `B₀ : Ξ₀ ≅ Ξ₀^σ` and `tr(Ξ₀(φ_{P,σ}) ∘ B₀) ≠ 0`.
3. **Descent of characters.** The normalized induction `Π'` of `Ξ₀` is irreducible and tempered
   (Zelevinsky 1980, Theorem 9.7), and with the induced intertwiner `A'` the twisted trace satisfies
   `tr(Π'(φ) ∘ A') = tr(Ξ₀(φ_{P,σ}) ∘ B₀)` (AC proof of Proposition 2.7, after Harish-Chandra;
   HL II.4.5, formula (2) and Remarque). So `tr(Π'(φ) ∘ A') ≠ 0`.
4. **Contradiction.** `Π' = Ind_B(Ξ)` with `Ξ = Ξ₀ ⊗ δ_B^{1/2}` irreducible, admissible and
   σ-stable, realized on a carrier in `Type uW` (Design). The hypothesis gives
   `tr(Π'(φ) ∘ A') = 0`, a contradiction. Hence the σ-orbital integrals of `φ` vanish off the
   σ-elliptic set.

HL's version (printed pp. 116–117) runs the same contradiction for `φ ∈ C^∞_c(G(E), χ)`: after
descent, a character `χ̃` of the centre of `G_α(E)` extending `χ` is chosen by Fourier inversion
so that the `χ̃`-average of `φ_{P,σ}` still has a nonzero σ-orbital integral at `δ`, and
Proposition 1 (2) is applied with central character `χ̃`.

## Sources

- J. Arthur, L. Clozel, *Simple algebras, base change, and the advanced theory of the trace
  formula*, Ann. of Math. Stud. 120 (1989): Chapter 1, Proposition 2.7 and its proof (printed
  pp. 15–17) and Lemma 2.12 and its proof (printed p. 19).
- G. Henniart, B. Lemaire, *Changement de base et induction automorphe pour GL_n en
  caractéristique non nulle*, Mém. SMF 124 (2011): II.4.5 (descent formulas); II.5.14,
  Propositions 1 and 2 and their proofs (printed pp. 114–117).
- A. V. Zelevinsky, *Induced representations of reductive p-adic groups. II. On irreducible
  representations of GL(n)*, Ann. Sci. ÉNS 13 (1980), Theorem 9.7, for the irreducibility of
  representations parabolically induced from irreducible tempered representations of Levi
  subgroups of `GL_n` (cited by AC in the proof of Lemma 2.11).
