# Elliptic pseudo-coefficients of supercuspidal representations

The module `Langlands.BaseChange.SupercuspidalEllipticPseudoCoefficientStatement` states, as the
proposition `SupercuspidalEllipticPseudoCoefficientStatement.{u, uV, uW}`, the following. Let
`F` be a nonarchimedean local field of characteristic zero, `0 < n`, and `π` an irreducible
supercuspidal representation of `GL_n(F)` with central character `χ`. For every Haar measure
`μ` there is a locally constant compactly supported `f` whose orbital integrals vanish at the
regular semisimple elements that are not elliptic, with `tr π(f) = 1` and `tr ρ(f) = 0` for
every irreducible admissible `ρ` with central character `χ` not isomorphic to `π`. This file
states the proposition and does **not** prove it.

## Notation (Library and Mathlib)

- `[ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F]`
  (Mathlib): `F` is a nonarchimedean local field of characteristic zero with its valued
  topology.
- `GeneralLinear n F` (module `Langlands.Group.GL.Basic`) is `GL_n(F)`, made Hausdorff, locally
  compact and totally disconnected by `LocalFieldTopology.generalLinear_t2Space`,
  `generalLinear_locallyCompactSpace` and `generalLinear_totallyDisconnectedSpace` (module
  `Langlands.Group.GL.LocalFieldTopology`), with its Borel σ-algebra; the coset spaces
  `H \ GL_n(F)` carry their Borel σ-algebras through the local instances
  `leftQuotientMeasurableSpace` and `leftQuotient_borelSpace`, as in the module
  `Langlands.BaseChange.OrbitalIntegral`.
- `SchwartzBruhat (GeneralLinear n F)` (module `Langlands.HarmonicAnalysis.Basic`): the locally
  constant compactly supported functions `GL_n(F) → ℂ`.
- `Character.distribution μ ρ hρ f` (module `Langlands.Representation.Character.Basic`): the
  trace of the finite-rank operator `ρ(f) v = ∫ f(g) ρ(g) v dμ(g)` of an admissible `ρ`,
  written `tr ρ(f)` below.
- `IsAdmissible ρ` (module `Langlands.Representation.Smooth.Definitions`) and Mathlib's
  `ρ.IsIrreducible`: `ρ` is admissible and irreducible (nonzero, with no invariant subspace
  other than `0` and the whole space).
- `IsRegularElliptic g` and `IsRegularSemisimple g` (module
  `Langlands.JacquetLanglands.RegularElliptic`): the characteristic polynomial of `g` is
  separable and irreducible over `F`, respectively separable.
- `GeneralLinear.IsSupercuspidal π` (module
  `Langlands.Representation.Classification.Supercuspidal`): `π` is admissible (the first
  component, `hπ.1`) and its Jacquet coinvariants vanish along the unipotent radical of every
  proper block parabolic subgroup and every conjugate of it.
- `HasCentralCharacterRep ρ χ` (module `Langlands.BaseChange.PseudoCoefficient`): every element
  `z` of the centre of `GL_n(F)` acts on `ρ` by the scalar `χ z`.
- `OrbitalIntegralsVanishOffElliptic μ f` (module `Langlands.BaseChange.EllipticOrbitalIntegral`),
  applied to the underlying function of `f`: the orbital integrals of `f`, for every right Haar
  measure on the centralizer and every compatible quotient measure, vanish at every regular
  semisimple element that is not regular elliptic (Kazhdan's `A(G)`, Henniart–Lemaire's
  "fonction elliptique", II.4.10, printed p. 93).
- `IsEmpty (ρ.Equiv π)` (Mathlib): `ρ` and `π` are not isomorphic.

## Statement

`SupercuspidalEllipticPseudoCoefficientStatement.{u, uV, uW}` quantifies over `F : Type u` as
above and `n : ℕ` with `0 < n`. For every complex vector space `V : Type uV`, every
representation `π` of `GL_n(F)` on `V` with `hπ : GeneralLinear.IsSupercuspidal π` and
`π.IsIrreducible`, every `χ : Subgroup.center (GeneralLinear n F) →* ℂˣ` with
`HasCentralCharacterRep π χ` and every Haar measure `μ` on `GL_n(F)`, there is
`f : SchwartzBruhat (GeneralLinear n F)` such that

1. `OrbitalIntegralsVanishOffElliptic μ f`;
2. `Character.distribution μ π hπ.1 f = 1`;
3. for every complex vector space `W : Type uW` and every representation `ρ` of `GL_n(F)` on
   `W` with `hρ : IsAdmissible ρ`, `ρ.IsIrreducible`, `HasCentralCharacterRep ρ χ` and
   `IsEmpty (ρ.Equiv π)`, `Character.distribution μ ρ hρ f = 0`.

The carriers of `π` and of the tested `ρ` lie in independent universes. No temperedness or
unitarity is assumed of `π`, `χ` or `ρ`.

## Why it is true (sketch)

Let `Z` be the centre of `G = GL_n(F)` and `dḡ` the quotient of `μ` by a Haar measure `dz` on
`Z`.

1. *Coefficient.* Choose `v` in the space of `π` and a smooth linear form `ℓ` with `ℓ(v) = 1`,
   let `d_π` be the formal degree of `π` relative to `dḡ`, and put
   `e(g) = d_π ℓ(π(g⁻¹)v)`. It is locally constant, satisfies `e(zg) = χ(z)⁻¹ e(g)`, and is
   compactly supported modulo `Z` because `π` is supercuspidal.
2. *Cut-off.* Let `v_F` be the normalized valuation. The set `{g : 0 ≤ v_F(det g) < n}` is open
   and closed and meets each coset `Zg` in a set of the form `Z_0 g'` with `Z_0` the maximal
   compact subgroup of `Z`, because `v_F(det(zg)) = n v_F(z) + v_F(det g)`. Its indicator
   times `e`, divided by the `dz`-volume of `Z_0`, is a locally constant compactly supported
   function `f` with `ρ(f) = ∫_{Z\G} e(g) ρ(g) dḡ` for every admissible `ρ` with central
   character `χ`.
3. *Traces.* Schur orthogonality for the coefficients of `π`, which are compactly supported
   modulo the centre, gives `π(f)w = ℓ(w) v`, so `tr π(f) = 1` (twisting `π` by a character
   `|det|^s` reduces to a unitary central character and changes neither side). For an
   irreducible admissible `ρ ≇ π` with central character `χ` and a vector `w'` of `ρ`, the map
   `w ↦ ∫_{Z\G} ℓ(π(g⁻¹)w) ρ(g)w' dḡ` intertwines `π` with `ρ`, hence vanishes since `π` and
   `ρ` are irreducible and not isomorphic, and its value at `v` is `d_π⁻¹ ρ(f)w'`; so
   `ρ(f) = 0`. No temperedness of `ρ` is needed.
4. *Orbital integrals.* The integral of `f` along every unipotent radical of a proper parabolic
   subgroup vanishes (the constant terms of a supercuspidal coefficient vanish, and the
   cut-off depends only on `det`, which is constant along unipotent cosets); the same holds
   for every conjugate of `f` by an element of the maximal compact subgroup. For a regular
   semisimple `γ` that is not elliptic, `γ` is conjugate into a proper Levi subgroup `M` with
   centralizer in `M`, and the parabolic descent of orbital integrals (Iwasawa decomposition
   and the change of variables `n ↦ n⁻¹ γ n` on the unipotent radical) writes the orbital
   integral of `f` at `γ` as an orbital integral on `M` of a constant term of the average of
   the conjugates of `f` over the maximal compact subgroup; so it vanishes.

Steps 1–3 follow the proof of Kazhdan's Proposition 3 of §5 (printed p. 28; stated as
Theorem K, printed p. 7), where the group has compact centre, the coefficient is the matrix
coefficient `(π(g)v, v)` of a unit vector normalized by the formal dimension, and the tested
representations are tempered, and Arthur–Clozel's
Corollary 2.10 (Chapter 1, printed p. 18), whose pseudo-coefficients transform under the centre
by `χ⁻¹` and act through `∫_{Z\G}`. Step 4 is the descent formula of Arthur–Clozel, Chapter 1,
proof of Proposition 2.7 (printed p. 16), by which they prove, in Lemma 2.12 (ii) (printed
p. 19), that the orbital integrals of a pseudo-coefficient vanish off the elliptic set; it is
also Kazhdan's description of `B(G)` by constant terms in the proof of Lemma 7 of §5 (printed
p. 26), which gives the coefficient of Proposition 3 in `B(G)`. The proposition is the untwisted
analogue (`E = F`, `σ = 1`) of these statements of Arthur–Clozel.

## Remarks

- `0 < n` is needed: in `GL_0(F)` the identity is regular semisimple but not regular elliptic
  (its characteristic polynomial `1` is not irreducible), and the orbital integral of `f` there
  is a nonzero multiple of `f(1)`, which cannot vanish if `tr π(f) = 1`.
- For `n = 1` every regular semisimple element is regular elliptic, so condition 1 holds for
  every `f` (the Library's `orbitalIntegralsVanishOffElliptic_one`), and every irreducible
  admissible representation with central character `χ` is one-dimensional and isomorphic to
  `π`, so condition 3 is vacuous.
- The Library's `SupercuspidalCuspFormStatement` asks for a test function with vanishing
  constant terms that is a pseudo-coefficient of `π`, has the trace property 3 (for `ρ` in the
  universe of `π`) and, in addition, has nonzero orbital integrals at the regular elliptic
  elements near `1`. The Library's `CuspidalPseudoCoefficientExistenceStatement` concerns
  square-integrable `π` and tests only tempered `ρ` and properly induced representations. The
  present proposition asks neither the nonvanishing near `1` nor temperedness of `ρ`.

## Sources

- Arthur–Clozel, *Simple Algebras, Base Change, and the Advanced Theory of the Trace Formula*
  (1989), source ID `arthur-clozel-1989-base-change` (PDF page = printed page + 14),
  Chapter 1: Proposition 2.7 and its proof, printed pp. 15–17 (descent formula for orbital
  integrals through the constant term, printed p. 16); Corollary 2.10, printed p. 18
  (pseudo-coefficients with fixed central character acting through `∫_{Z\G}`); Lemma 2.12 (ii)
  and its proof, printed p. 19 (vanishing of the orbital integrals of a pseudo-coefficient off
  the elliptic set).
- Kazhdan, *Cuspidal geometry of p-adic groups*, J. Analyse Math. 47 (1986), source ID
  `kazhdan-1986-cuspidal-geometry` (PDF page = printed page): the space `A(G)`, printed p. 2;
  Theorem K, printed p. 7; §5, Lemma 7 and its proof, printed p. 26; §5, Proposition 3 and its
  proof, printed p. 28.
- Henniart–Lemaire, *Changement de base et induction automorphe pour `GL_n` en
  caractéristique non nulle*, Mém. SMF 124 (2011), source ID
  `provided-a0a5445aba86b871bcd83f08813de3234fddb463ff9bb3c9dfd60d2d2fcdae61` (PDF page =
  printed page + 8): I.2.9, printed p. 22 (the space `C_c^∞(G(F), ω)`); II.4.10, printed
  pp. 93–94 (elliptic functions and, in Lemmes 1 and 2, the simple local trace formula for
  them with a central character); II.5.13, printed p. 113 (pseudo-coefficients of σ-discrete
  series, tested on tempered representations); II.5.14, Proposition 2 (2), printed p. 115 (they
  are σ-elliptic).

## Derived content

The proposition is formulated for the Library: it is the untwisted, fixed-central-character
analogue of the pseudo-coefficients of Arthur–Clozel, Corollary 2.10 and Lemma 2.12 (ii), for a
supercuspidal representation, in the strengthened form, available for supercuspidal
coefficients, in which the trace vanishes on every irreducible admissible representation with
the same central character, tempered or not.
