# Elliptic determination of traces

The module `Langlands.BaseChange.EllipticTraceDeterminationStatement` states, as the
proposition `EllipticTraceDeterminationStatement.{u, uI, uV}`, the following. Let `F` be a
nonarchimedean local field of characteristic zero and `0 < n`. If a finite linear combination of
the characters of irreducible admissible representations of `GL_n(F)` vanishes on every test
function supported in the regular elliptic set, then it vanishes on every test function whose
orbital integrals vanish at the regular semisimple elements that are not elliptic. This file
states the proposition and does **not** prove it.

## Notation (Library and Mathlib)

- `[ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F]`
  (Mathlib): `F` is a nonarchimedean local field of characteristic zero with its valued
  topology.
- `GeneralLinear n F` (module `Langlands.Group.GL.Basic`) is `GL_n(F)`. Its topology is made
  Hausdorff, locally compact and totally disconnected by
  `LocalFieldTopology.generalLinear_t2Space`, `generalLinear_locallyCompactSpace` and
  `generalLinear_totallyDisconnectedSpace` (module `Langlands.Group.GL.LocalFieldTopology`); the
  σ-algebra is the Borel σ-algebra. As in the module `Langlands.BaseChange.OrbitalIntegral`,
  every coset space `H \ GL_n(F)` carries its Borel σ-algebra through the local instances
  `leftQuotientMeasurableSpace` and `leftQuotient_borelSpace`.
- `IsAdmissible ρ` (module `Langlands.Representation.Smooth.Definitions`) and Mathlib's
  `ρ.IsIrreducible`: `ρ` is admissible and irreducible (nonzero, with no invariant subspace
  other than `0` and the whole space).
- `SchwartzBruhat (GeneralLinear n F)` (module `Langlands.HarmonicAnalysis.Basic`): the
  locally constant compactly supported functions `GL_n(F) → ℂ`. The two predicates below are
  applied to the underlying function `(f : GeneralLinear n F → ℂ)`.
- `Character.distribution μ ρ hρ f` (module `Langlands.Representation.Character.Basic`): the
  trace of the finite-rank operator `ρ(f) v = ∫ f(g) ρ(g) v dμ(g)`, written `tr ρ(f)` below.
- `IsEllipticSupported f` (module `Langlands.BaseChange.EllipticSupport`): every `g` with
  `f g ≠ 0` is regular elliptic (`IsRegularElliptic`, module
  `Langlands.JacquetLanglands.RegularElliptic`: the characteristic polynomial of `g` is
  separable and irreducible over `F`; `IsRegularSemisimple`: it is separable).
- `OrbitalIntegralsVanishOffElliptic μ f` (module `Langlands.BaseChange.EllipticOrbitalIntegral`):
  for every regular semisimple `γ` that is not regular elliptic, every right Haar measure on the
  centralizer `G_γ(F)` and every measure on `G_γ(F) \ GL_n(F)` compatible with `μ` and it, the
  orbital integral `∫ f(x⁻¹ γ x)` is `0`. For locally constant compactly supported functions
  this is Kazhdan's space `A(G)` (1986, printed p. 2); his `B(G)` (printed p. 6) is the
  corresponding subspace of Harish-Chandra's Schwartz space. Henniart–Lemaire (II.4.10,
  printed p. 93) call such a function "elliptique".

## Statement

`EllipticTraceDeterminationStatement.{u, uI, uV}` quantifies over `F : Type u` as above, over
`n : ℕ` with `0 < n`, and over a Haar measure `μ` on `GL_n(F)`. For every finite type
`I : Type uI`, complex vector spaces `V i : Type uV`, irreducible admissible representations
`ρ i` of `GL_n(F)` on `V i` (with admissibility proofs `hρ i`) and coefficients `a : I → ℂ`:
if

`∑ i, a i * Character.distribution μ (ρ i) (hρ i) f = 0`

for every `f : SchwartzBruhat (GeneralLinear n F)` with `IsEllipticSupported f`, then the same
sum is `0` for every `f : SchwartzBruhat (GeneralLinear n F)` with
`OrbitalIntegralsVanishOffElliptic μ f`. The same Haar measure `μ` defines the characters and
the orbital integrals.

## Why it is true (sketch)

Write `Θ_i` for the character function of `ρ i`: it is locally integrable, represents the
character distribution and is locally constant on the regular semisimple set
(Harish-Chandra 1999, Theorem 16.3; the Library's `CharacterLocalIntegrabilityStatement`). Put
`Θ = ∑ i, a i Θ_i`.

1. *Pointwise vanishing on the regular elliptic set.* The regular elliptic set is open
   (the Library's theorem `Langlands.BaseChange.regularEllipticOpen`). At a regular elliptic
   `γ` the function `Θ` is constant on a compact open neighbourhood `U` of `γ` consisting of
   regular elliptic elements; the indicator of `U` is an admissible test function, and the
   hypothesis gives `Θ(γ) μ(U) = 0`, so `Θ(γ) = 0`.
2. *Weyl integration.* For `f` locally constant and compactly supported, `f Θ` is integrable
   and `∑ i, a i tr ρ_i(f) = ∫ f Θ dμ`. The Weyl integration formula (Henniart–Lemaire, II.2.10,
   formula (2); the Library's `WeylIntegrationFormulaStatement`) writes this integral as a sum
   over a set of representatives `T` of the conjugacy classes of maximal tori of integrals over
   `T` of the weighted orbital integrals of `f Θ` at the regular elements `t ∈ T`. Since `Θ` is
   invariant under conjugation and locally constant near `t`, the orbital integral of `f Θ` at
   `t` is `Θ(t)` times that of `f`.
3. *Only elliptic tori contribute.* If `T` is not elliptic, its regular elements are regular
   semisimple and not elliptic (their characteristic polynomials have at least two irreducible
   factors), so the orbital integrals of `f` vanish there by hypothesis. If `T` is elliptic,
   its regular elements are regular elliptic, and `Θ` vanishes there by step 1. Hence
   `∫ f Θ dμ = 0`.

Arthur–Clozel (Chapter 1, proof of Lemma 2.12, printed p. 19) use the identity
`1 = trace Π(φ) = ∫ Θ_Π(g) φ(g) dg`, for a pseudo-coefficient `φ` whose orbital integrals
vanish off the elliptic set, to pass between traces and the values of the character on the
elliptic set. Henniart–Lemaire (II.6.13, printed pp. 129–130) use the Weyl integration formula
to compare the traces of test functions whose regular orbital integrals vanish on a given set
of classes, and the local constancy of characters on the regular set (as in step 1) to choose
test functions supported on a small compact open set.

## Remarks

- The hypothesis `0 < n` excludes the trivial group `GL_0(F)`, in which no element is regular
  elliptic and the identity is regular semisimple and not regular elliptic. It is the same
  hypothesis as in the companion proposition `SupercuspidalEllipticPseudoCoefficientStatement`
  (module `Langlands.BaseChange.SupercuspidalEllipticPseudoCoefficientStatement`), where it is
  needed.
- Kazhdan (1986, Theorem A (a), printed p. 3), for groups with compact centre, identifies the
  virtual representations whose characters vanish on all of `A(G)` with the combinations of
  properly induced representations. The present proposition is a statement about the
  restriction of a virtual character to the regular elliptic set and does not use that
  theorem.

## Sources

- Harish-Chandra, *Admissible invariant distributions on reductive p-adic groups*, notes by
  DeBacker and Sally, ULS 16, AMS 1999, source ID
  `harish-chandra-1999-admissible-invariant-distributions` (PDF page = printed page + 15),
  Theorem 16.3, printed p. 75: the character of an admissible irreducible representation is a
  locally summable function, locally constant on the regular set.
- Henniart–Lemaire, *Changement de base et induction automorphe pour `GL_n` en
  caractéristique non nulle*, Mém. SMF 124 (2011), source ID
  `provided-a0a5445aba86b871bcd83f08813de3234fddb463ff9bb3c9dfd60d2d2fcdae61` (PDF page =
  printed page + 8): II.2.10, printed pp. 70–72, formula (2) on printed p. 72 (Weyl
  integration formula); II.4.10, printed p. 93 (definition of elliptic functions); II.6.13,
  printed pp. 129–130 (use of the Weyl integration formula and of the local constancy of
  characters to compare traces).
- Arthur–Clozel, *Simple Algebras, Base Change, and the Advanced Theory of the Trace Formula*
  (1989), source ID `arthur-clozel-1989-base-change` (PDF page = printed page + 14),
  Chapter 1, Lemma 2.12 and its proof, printed p. 19.
- Kazhdan, *Cuspidal geometry of p-adic groups*, J. Analyse Math. 47 (1986), source ID
  `kazhdan-1986-cuspidal-geometry` (PDF page = printed page): the space `A(G)`, printed p. 2;
  Theorem A, printed p. 3; the space `B(G)`, printed p. 6.

## Derived content

The proposition is formulated for the Library. It is the consequence of Harish-Chandra's local
integrability theorem and of the Weyl integration formula used in the sources cited above; it
records, for finite combinations of irreducible characters, that the restriction of a virtual
character to the regular elliptic set determines its values on the test functions whose
orbital integrals vanish off the elliptic set.
