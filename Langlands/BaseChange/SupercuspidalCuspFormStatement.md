# Supercuspidal cusp-form pseudo-coefficients with nonzero elliptic orbital integrals near 1

Lean module: `Langlands.BaseChange.SupercuspidalCuspFormStatement`, namespace
`Langlands.BaseChange`. Author: Worker 820, for Task 7457.

This module defines one proposition, `SupercuspidalCuspFormStatement.{u, uV} : Prop`. It is a
statement only: nothing here proves it, and no declaration assumes it.

## Statement

Let `F : Type u` be a field with `[ValuativeRel F] [TopologicalSpace F]`, Mathlib's
`[IsNonarchimedeanLocalField F]` and `[CharZero F]`, and let `n : ℕ`. Give `GL_n(F)` (the
Library's `GeneralLinear n F`) its Borel σ-algebra and the topological properties that
`Character.distribution` needs (Hausdorff, locally compact, totally disconnected), supplied
locally by the Library's certificates `LocalFieldTopology.generalLinear_t2Space`,
`generalLinear_locallyCompactSpace` and `generalLinear_totallyDisconnectedSpace`. The data are:

- a complex vector space `V : Type uV` and `π : Representation ℂ (GL_n(F)) V` with
  `hπ : IsAdmissible π`, `π.IsIrreducible` and `GeneralLinear.IsSupercuspidal π`;
- `χ : Subgroup.center (GL_n(F)) →* ℂˣ` with `HasCentralCharacterRep π χ` (Task 7442);
- a Haar measure `μ` on `GL_n(F)` (`[μ.IsHaarMeasure]`).

For all such data there is `f : SchwartzBruhat (GL_n(F))` (a locally constant compactly
supported function) with the following four properties.

- (a) `HasVanishingConstantTerms f`: definition 1 of `Langlands.BaseChange.CuspForm`, for the
  underlying function of `f`.
- (b) `IsPseudoCoefficient μ χ π hπ f` (Task 7442): `π` has central character `χ`, the
  character `Character.distribution μ π hπ` takes the value `1` at `f`, and the character of
  every irreducible tempered admissible `π' ≇ π` on a space in universe `uV` with central
  character `χ` vanishes at `f`.
- (c) For every complex vector space `V' : Type uV`, every
  `π' : Representation ℂ (GL_n(F)) V'` with `hπ' : IsAdmissible π'`, `π'.IsIrreducible`,
  `HasCentralCharacterRep π' χ` and `IsEmpty (π'.Equiv π)`:
  `Character.distribution μ π' hπ' f = 0`. Unlike (b), this asks nothing about temperedness.
- (d) There is `U ∈ nhds 1` in `GL_n(F)` such that for every `γ ∈ U` with
  `IsRegularElliptic γ` (the Library's predicate: the characteristic polynomial is separable
  and irreducible), every right Haar measure `μγ` on `glCentralizer γ` (Task 7416; a measure
  with `IsHaarMeasure` and `IsMulRightInvariant`) and every
  `νγ : Measure (LeftQuotient (glCentralizer γ))` with
  `QuotientIntegration.IsCompatible (glCentralizer γ) μ μγ νγ`, the orbital integral
  `orbitalIntegral γ νγ f` (Task 7402: `∫ f(x⁻¹ γ x) dνγ(x)` over `G_γ(F)\G(F)`) is nonzero.
  The coset space `LeftQuotient (glCentralizer γ)` carries its Borel σ-algebra, through the
  reducible definition `leftQuotientMeasurableSpace` (`= borel _`) of Task 7416's module
  `Langlands.BaseChange.OrbitalIntegral`, which this module installs as a local instance of
  high priority, as that module and its statement modules do; the centralizer carries the
  subspace σ-algebra.

All measures in the Lean proposition are quantified; none is chosen or normalized there.

Names: the module imports the published modules `Langlands.BaseChange.PseudoCoefficient`
(Task 7442: `HasCentralCharacterRep ρ χ`, `IsPseudoCoefficient μ χ π hπ f`),
`Langlands.BaseChange.OrbitalIntegral` (Task 7416: `glCentralizer γ`, with `n` implicit) and
`Langlands.TraceFormula.TwistedOrbital` (Task 7402: `orbitalIntegral γ ν f`, imported through
`OrbitalIntegral`). Their published names and argument orders are those cited in the objective,
so no correspondence is needed.

## The construction behind the statement (not formalized)

**Positive rank.** Put `G = GL_n(F)` and `Z = Z(G)`. For this paper construction choose a Haar
measure `dz` on `Z` and use the quotient measure `dḡ = dμ/dz` on `Z\G`. Choose `v ∈ V` and a
smooth covector `ℓ` with `ℓ(v) = 1`, and set `φ₀(g) = d_π ℓ(π(g⁻¹)v)`, where the formal degree
`d_π` is relative to `dḡ` (Casselman 1995, Proposition 5.2.4, printed pp. 47–48). This
contragredient coefficient belongs to `C^∞_c(G, χ)`: it transforms by
`φ₀(zg) = χ(z)⁻¹ φ₀(g)` and is compactly supported modulo `Z` (Theorem 5.2.1, printed p. 46).

Take `β = 1_Ω / vol_dz(Z ∩ K)`, with `K = GL_n(𝔬_F)` and `Ω` the set of `g` with
`v_F(det g) ∈ {0, …, n − 1}`, where `v_F` is the normalized integer valuation. Multiplying `g`
by the scalar `z` adds `n v_F(z)` to the determinant valuation. Thus the scalars `z` for which
`zg ∈ Ω` form one coset of `Z ∩ K` for each `g`. The map `Ω → Z\G` identifies `Ω/(Z ∩ K)`
with `Z\G` and is proper because `Z ∩ K` is compact. Hence `f = φ₀ β` is locally constant and
compactly supported, and `∫_Z f(zg) χ(z) dz = φ₀(g)`. The factor `β` is invariant under
conjugation and under multiplication by unipotent elements.

- **(a)** For any Haar measure on a proper unipotent radical `N`, the integral of a two-sided
  translate of the coefficient is well defined: the translate is another coefficient, and
  its support on `N` is compact because `N` is closed and lies in the determinant-valuation-zero
  slice of `Ω`. Integrating over `N` gives an `N`-invariant functional in the vector argument,
  which factors through the zero Jacquet module (Casselman §5.1, printed p. 46). In `f(xuy)`
  the cut-off is constant as `u` varies over `N`, so integrability and vanishing hold for `f`.
- **(b) and (c)** For any `π'` with central character `χ`, central averaging and quotient
  integration give `π'(f) = π'(φ₀)`, where the latter action uses `dḡ`. Schur orthogonality
  (Casselman, Proposition 5.2.4) gives `π(φ₀)w = ℓ(w)v`, a rank-one operator of trace `1`.
  For an irreducible `π' ≇ π` and fixed `w'` in its space, the map
  `w ↦ ∫_{Z\G} ℓ(π(g⁻¹)w) π'(g)w' dḡ` is an intertwiner: the integrand descends because the
  central characters cancel, and left translation gives equivariance. The map is zero by
  irreducibility and inequivalence. Evaluating at `v` and multiplying by `d_π` gives
  `π'(φ₀)w' = 0`, without assuming temperedness. The projection in the proof of Casselman's
  Theorem 5.4.1 (printed p. 49) is onto a copy of `π` in a space of coefficient functions in
  the regular representation, not the action of `φ₀` on `π` used here.
- **(d)** For regular elliptic `γ`, `G_γ = F[γ]^×` and `G_γ/Z` is compact. Harish-Chandra's
  fixed-central-character integral formula for the supercuspidal character identifies the
  integral of `φ₀(g⁻¹ γ g)` over `Z\G` with `Θ_π(γ⁻¹)` in this inverse-coefficient convention.
  To obtain the orbital integral over `G_γ\G`, divide by the finite positive volume of
  `G_γ/Z` for the quotient measure from `μγ` and `dz`. Henniart–Lemaire (HL) II.4.10 (printed
  pp. 93–94, with `E = F`) use the normalization giving `G_γ/Z` volume `1`. Kazhdan 1986,
  Theorem K(b) (printed p. 7), gives the compact-centre analogue, not the formula for `GL_n`.
  Since `β` is conjugation invariant, the orbital integral of `f` gains the factor `β(γ)`.
  Near `1`, `β` is nonzero and the character on regular elliptic elements is a nonzero
  constant, as HL II.6.7 (printed p. 123) explain using Jacquet–Langlands. Inversion preserves
  regular ellipticity, so the neighborhood can be shrunk to be invariant under inversion.

**Rank zero.** On the singleton `GL_0(F)`, use `f(1) = 1 / μ({1})` instead of the determinant
cut-off. This has trace `1` on the one-dimensional trivial representation, the unique
irreducible representation up to equivalence. There are no proper block parabolics and no
regular elliptic elements (the characteristic polynomial `1` is a unit, not irreducible).
Thus (a), (c) and (d) are vacuous in this rank.

## Why (c) is stated

`IsPseudoCoefficient` (Task 7442) only kills tempered representations. The local components of
cuspidal automorphic representations are not known to be tempered, so the globalization of a
supercuspidal representation needs the trace of every irreducible admissible `π' ≇ π` with
central character `χ` to vanish. For supercuspidal `π` this holds for the construction above.

## Nonvanishing

In (d), nonvanishing does not depend on the choice of compatible measures: rescaling the
centralizer Haar measure rescales the compatible quotient measure inversely, by a positive
constant. An open set is needed, not a point. In HL II.6.7 (printed pp. 123–124), nonvanishing
near `1` at the target place `v₀` combines with openness of the norm map near `1` to find a
local norm with nonzero orbital integral. Approximation at `v₀` and `v₁` then gives a global
element with nonzero orbital integrals at both places.

## Hypotheses and universes

- `CharZero F` is assumed, like the other base-change statements of the programme (Tasks 7416,
  7432, 7442 and 7446). Kazhdan works in characteristic zero, and the Library's
  `IsRegularSemisimple` (part of `IsRegularElliptic`) asks for a separable characteristic
  polynomial, which agrees with HL's regularity (squarefree characteristic polynomial) in
  characteristic zero. Statements 4-6 of Task 7457 need no such hypothesis.
- The representations `π'` in (c), like those in (b), are on spaces in the universe `uV` of
  `V`.

## Use

HL use two distinct local inputs. At the cuspidal place `v₁`, the hypothesis `c_{v₁}(f)` of
II.6.3 requires that the local test function be supported on regular elliptic elements and
be a linear combination of coefficients of smooth irreducible cuspidal representations.
The comparison of Task 7340 formulates its cuspidality input through vanishing constant
terms. Clause (a) supplies that input; it does not assert regular elliptic support. At the
target place `v₀`, HL II.6.7 instead use an elliptic pseudo-coefficient of the chosen discrete
series; that is the source of the near-identity nonvanishing in (d) for the supercuspidal
case. This statement packages these properties for the project's characteristic-zero
comparison with the simple trace formula and its twisted form. `SupercuspidalExistenceStatement`
supplies the representation in positive rank, `CuspFormConvolutionStatement` lets the comparison
convolve with Hecke operators, and `SplitTensorCuspFormStatement` passes from `GL_n(F)` to
`GL_n(F^l)` at a split place.

## Sources

- Casselman 1995 (`casselman-1995-admissible-representations`): §5.1 and Theorem 5.2.1
  (printed p. 46), Proposition 5.2.4 (printed pp. 47–48), Theorem 5.4.1 (printed p. 49).
- Henniart–Lemaire 2011 (`provided-a0a5445aba86b871bcd83f08813de3234fddb463ff9bb3c9dfd60d2d2fcdae61`):
  II.4.10, printed pp. 93–94 (PDF pp. 101–102); II.6.3, printed pp. 119–120
  (PDF pp. 127–128); II.6.7, printed pp. 123–124 (PDF pp. 131–132).
- Kazhdan 1986 (`kazhdan-1986-cuspidal-geometry`): Theorem K(b) and §1.1, printed p. 7.
