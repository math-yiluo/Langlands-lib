# Pseudo-coefficients of the discrete series of `GL_n(F)` normalized on determinant slices

Module `Langlands.BaseChange.DeterminantSlicePseudoCoefficientStatement`. It defines the
predicate `Langlands.BaseChange.IsDeterminantSliceNormalized` and the `Prop`-valued
definition `Langlands.BaseChange.DeterminantSlicePseudoCoefficientExistenceStatement.{u, uV}`.
The module states the existence result and does not prove it.

Sources: Kazhdan, *Cuspidal geometry of p-adic groups*, J. Analyse Math. 47 (1986),
Theorem K (printed p. 7), proved there for groups with compact centre (printed p. 2);
Henniart–Lemaire, *Changement de base et induction automorphe pour GL_n en caractéristique
non nulle*, Mém. SMF 124 (2011), cited as HL:
II.5.13, Proposition and Remarque (printed pp. 113–114), II.5.14, Proposition 2
(printed pp. 115–117), for `E = F` and `σ = 1`; II.4.10, Lemme 1 (printed p. 93), and II.6.7
(printed pp. 123–124) for nonvanishing near the identity.

## Normalization on determinant slices

Let `F` be a nonarchimedean local field (`F : Type u` with `[Field F] [ValuativeRel F]
[TopologicalSpace F] [IsNonarchimedeanLocalField F]`), `n : ℕ`, `G = GL_n(F) =
GeneralLinear n F` with centre `Z = Subgroup.center G`, and write
`|det g| = JacquetLanglands.determinantNorm F n g` (the residue-normalized absolute value of
the determinant). Put `G¹ = {g ∈ G : |det g| = 1}`.

For `χ : Z →* ℂˣ` and `f : G → ℂ`, `IsDeterminantSliceNormalized χ f` is the conjunction of:

- (n1) for every `z ∈ Z` with `|det z| = 1` and every `g ∈ G`,
  `f (z * g) = (χ z)⁻¹ * f g`: the central units act on `f` through `χ⁻¹`;
- (n2) for every `z ∈ Z` and `g ∈ G`, if `f g ≠ 0` and `|det (z * g)| = 1`, then
  `|det g| = 1`: on the subgroup `Z · G¹`, `f` vanishes outside `G¹`.

Since `|det z| = |a|^n` for the scalar `z = a · 1`, the subgroup `Z · G¹` consists of the
`g` with `v(det g) ∈ nℤ`, for the normalized valuation `v` of `F`, and (n2) says that `f`
vanishes where `v(det g)` is a nonzero multiple of `n`.

## The statement in words

Let `F` be as above with `[CharZero F]`, let `0 < n`, and give `G` its Borel σ-algebra
locally, with the instances `LocalFieldTopology.generalLinear_t2Space`,
`generalLinear_locallyCompactSpace` and `generalLinear_totallyDisconnectedSpace`. Let
`V : Type uV` be a complex vector space and `π : Representation ℂ G V` with
`hπ : IsAdmissible π`, `π.IsIrreducible` and `JacquetLanglands.IsSquareIntegrable π`
(square-integrability modulo the centre). Let `χ : Z →* ℂˣ` with
`HasCentralCharacterRep π χ`, and let `μ` be a Haar measure on `G`. Then there is
`f : SchwartzBruhat G` (locally constant with compact support) such that:

- (a) `IsPseudoCoefficient μ χ π hπ f`: the trace of `π` at `f` is `1`, and the trace at
  every irreducible admissible tempered representation of central character `χ`, with carrier
  in universe `uV` and not isomorphic to `π`, is `0`;
- (b) for every `B : GeneralLinear.BlockShape n` with `2 ≤ B.length`, every irreducible
  admissible `Ξ : Representation ℂ (B.Levi F) X` on a complex vector space `X : Type uV`,
  and every proof `h` that `Induction.smoothInduced (B.parabolic F) (Ξ.comp
  (B.leviProjection F))` is admissible, the character of this unnormalized induction
  vanishes at `f`;
- (n) `IsDeterminantSliceNormalized χ ⇑f`;
- (d) there is `U ∈ nhds (1 : G)` such that for every regular elliptic `γ ∈ U`, every right
  Haar measure `μγ` on `glCentralizer γ` and every `νγ` with
  `QuotientIntegration.IsCompatible (glCentralizer γ) μ μγ νγ`, the orbital integral
  `orbitalIntegral γ νγ ⇑f` is nonzero.

Clauses (a), (b) and (d) are clauses (a), (b) and (d) of the Library's
`Langlands.BaseChange.CuspidalPseudoCoefficientExistenceStatement`, with the same data and
the same quantifiers. Clause (c) of that statement (orbital vanishing off the elliptic set)
is not part of this one; clause (n) is added.

## Origin of the normalization

HL and Kazhdan construct pseudo-coefficients `φ₀` in `C^∞_c(G, χ)`: `φ₀(zg) = χ(z)⁻¹ φ₀(g)`
for every `z ∈ Z`, with compact support modulo `Z`. The module
`Langlands.BaseChange.CuspidalPseudoCoefficientExistenceStatement` and its Markdown describe
the lift `f = φ₀ · β` to `C^∞_c(G)`, where `β = 1_Ω / vol(Z ∩ GL_n(O_F))` and
`Ω = {g | v(det g) ∈ {0, …, n - 1}}`. Such an `f` satisfies (n):

- for a central unit `z`, `v(det (zg)) = v(det g)`, so `β(zg) = β(g)` and (n1) follows from
  the covariance of `φ₀`;
- if `β(g) ≠ 0` then `0 ≤ v(det g) < n`, and if moreover `v(det (zg)) = 0` for a central
  `z = a · 1`, then `v(det g) = -n · v(a)` is a multiple of `n` in `{0, …, n - 1}`, hence `0`.

Clauses (a), (b) and (d) for the lift are discussed in the Markdown of
`CuspidalPseudoCoefficientExistenceStatement`: the central average of `f` with weight `χ` is
`φ₀`, so traces at representations of central character `χ` are those of `φ₀`, and
`β` is constant on conjugacy classes and equal to `1 / vol(Z ∩ GL_n(O_F))` near `1`, so the
orbital integrals of `f` near `1` are nonzero multiples of those of `φ₀`.

## Use

With (n), the restriction of `f` to `G¹` is the function `1_{G¹} · f`, which is locally
constant with compact support because `G¹` is open and closed. Its trace at an admissible
representation `π'` is the average of the traces of `f` at the twists of `π'` by the
unramified characters `g ↦ ζ^{v(det g)}` with `ζ^n = 1`: by (n2), `1_{G¹} f = 1_{Z G¹} f`,
and `1_{Z G¹}` is the average of these characters. These twists have the same central
character as `π'`, so clause (a) identifies the traces at tempered `π'` of central character
`χ`. By (n1), the trace at `π'` vanishes unless the central character of `π'` agrees with `χ`
on the central units. Without (n), the passage from `f` to its central average with weight
`χ` would require integration over the centre.

## Conventions

`CharZero F` and `0 < n` are kept as in `CuspidalPseudoCoefficientExistenceStatement`, whose
Markdown explains both. The definitions are used under their published names:
`IsPseudoCoefficient` and `HasCentralCharacterRep` (module
`Langlands.BaseChange.PseudoCoefficient`), `JacquetLanglands.determinantNorm` and
`JacquetLanglands.IsSquareIntegrable` (module `Langlands.JacquetLanglands.EssentiallySquareIntegrable`),
`glCentralizer`, `leftQuotientMeasurableSpace` and `leftQuotient_borelSpace` (module
`Langlands.BaseChange.OrbitalIntegral`), and `orbitalIntegral` (module
`Langlands.TraceFormula.TwistedOrbital`).

## Sources

- David Kazhdan, *Cuspidal geometry of p-adic groups*, J. Analyse Math. 47 (1986). Retained
  source `kazhdan-1986-cuspidal-geometry`, SHA-256
  `06821a391bee5ae07e42cd1c5dfacb0a040f1e6bf0a636c88401309a35b3a886`. Theorem K (printed p. 7):
  pseudo-coefficients of square-integrable representations and their orbital integrals at
  the regular elliptic elements, for a reductive group with compact centre; the paper
  assumes a compact centre throughout and notes that its results extend to the general
  case (printed p. 2).
- Guy Henniart and Bertrand Lemaire, *Changement de base et induction automorphe pour `GL_n` en
  caractéristique non nulle*, Mém. Soc. Math. Fr. 124 (2011). Retained source
  `provided-a0a5445aba86b871bcd83f08813de3234fddb463ff9bb3c9dfd60d2d2fcdae61`, SHA-256
  `7af2940c75a75937c1bf9096eb329931d4245cf592e3572db0ff93ec6e76c5e0` (PDF page = printed
  page + 8). II.5.13 and II.5.14, Proposition 2 (printed pp. 113–117), II.4.10, Lemme 1
  (printed p. 93), and II.6.7 (printed pp. 123–124).
