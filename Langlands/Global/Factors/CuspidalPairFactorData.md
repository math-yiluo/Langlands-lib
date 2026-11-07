# Finite-place factor data of cuspidal Rankin–Selberg pairs

Authors: Worker 1794 (Lean declarations, design) and Worker 1802 (source
locators and normalization comparisons, merged from their note, and remarks
that shaped the declarations). Definition contribution to task
`876d1f0c-d287-4743-adf6-aef3a9efb5ba`, revision 1.

**Scope.** This module defines the finite-place vocabulary and the analytic
predicate of the completed global Rankin–Selberg functional equation of cuspidal
pairs. Every declaration is a definition. Nothing is proved or assumed.

The completed statement itself is not defined here. It is intended for a later
module `Langlands.Global.Factors.CuspidalPairFunctionalEquationStatement`, under
the proposition name `CuspidalPairGlobalFunctionalEquationStatement`. It needs, at
every infinite place, the actual archimedean components of the cuspidal
realizations, their Langlands parameters and the attached pair L- and epsilon
factors. These are reserved exports of task
`6c50b2fd-cb4a-47b3-8f5d-d464916d69fb` and are not public (§9). The sections
below that mention "the intended statement" explain how these definitions are
meant to be used. They describe no declaration of this module.

## 1. Sources and provenance

Page conventions: "p." is the printed page, "PDF" the page of the registered
file.

| Source ID | Short name | Locators used |
|---|---|---|
| `henniart-1986-cyclic` | H86 | §2.10 p.155 (PDF 12); §4.3 pp.158–159 (PDF 15–16) |
| `henniart-2000-simple-proof` | H00 | §2.3 pp.444–445 (PDF 6–7) |
| `jpss-1983-rankin-selberg` | JPSS83 | p.368; (0.1), (0.3); (0.2)(6)–(10) pp.374–375 (PDF 9–10); Thm (2.7) pp.390–391; Thm (3.1) pp.404–405 (PDF 39–40); (9.4)(3)–(4) p.458 (PDF 93) |
| `henniart-2002-characterization` | H02 | §2.8 p.596 (PDF 10) |
| `cogdell-2004-analytic-theory-gln` | Cog04 | §3 pp.211–217; Thm 4.1 p.219 (PDF 222); proof p.220 |
| `getz-hahn-2024-automorphic-representations` | GH | §11.6 p.308 (PDF 319); Thm 11.7.1 p.309 (PDF 320); App. C pp.551–553 |
| `getz-hahn-2024-errata-2026-10` | GH errata | p.3: the only Chapter 11 entry (§11.5, ψ defined twice on p.304) is editorial; none concerns §11.6–11.7 |
| `gross-1998-satake-isomorphism` | Gross98 | Satake normalization, via the Library module `Unramified.HeckeOperators` |

Supporting sources read by Worker 1802 for the proof routes: Shahidi 1981
(Thm 4.1 p.344), Shahidi 1985 (Thm 1 / Thm 3.1 p.990), Henniart–Herb 1995 §8.15
(p.181) and Jacquet 2009 (archimedean theory, Thm 2.1 p.6, App. 16).

**What the sources state.**

- H86 §2.10 (p.155): for automorphic `Π`, `Π'` of `GL(n)`, `GL(m)` over a number
  field, `L(Π × Π')(s) = ∏_v L(Π_v × Π'_v)(s)` for `Re s` large;
  `ε(Π_v × Π'_v, ψ_v) = 1` off a finite set; `ε(Π × Π') = ∏_v ε(Π_v × Π'_v, ψ_v)`
  does not depend on `ψ`; and `L(Π × Π')(s) = ε(Π × Π')(s) L(Π∨ × Π'∨)(1 - s)`.
  H86 cites [JPS 4], the 1981 C. R. note.
- H00 §2.3 (pp.444–445) quotes Theorem 4.1 of H86 for continuous
  representations of `W_F` associated with automorphic representations `P`, `P'`
  of `GL_n(A_F)`, `GL_n'(A_F)`, with no cuspidality assumption. It says that the
  theorem uses the global pair functional equations crucially, and attributes
  them to Shahidi [Sh 1, 2, 3] with the comments of Henniart–Herb 1995 §8.15. The
  cuspidal application follows in H00 §2.4 (p.445), for irreducible unitary `S`
  and cuspidal unitary `P`.
- H02 §2.8 (p.596) works over a non-archimedean local field. It writes each
  irreducible representation as the Langlands quotient
  `J(π_1, …, π_r)` of essentially square-integrable blocks, with
  `J∨ ≃ J(π_r∨, …, π_1∨)`. For two such representations it states that the
  L-, γ- and ε-factors of the pair are the products of the JPSS factors of all
  pairs of blocks. The finite ε-factor used here is this product (§4).
- **Announcement versus proof.** JPSS83 p.368 announces the global result ("whose
  proof will appear elsewhere"). Its (0.3) fixes a non-archimedean field
  throughout, so it supplies only the finite local theory. Henniart–Herb 1995
  §8.15 (p.181) says the pair equation was "announced … but not proven" in the
  1981 note. The established statements used here are Cog04 Thm 4.1 (p.219) and
  GH Thm 11.7.1 (p.309). Cog04 proves Thm 4.1 by the Jacquet–Shalika global
  integrals and the JPSS83 finite local theory. At the archimedean places Cog04
  §3.2 (p.216) follows Jacquet–Shalika, *Rankin–Selberg convolutions:
  Archimedean theory* (1990, his [27]), and the archimedean parts of
  Jacquet–Shalika, *On Euler products and the classification of automorphic
  representations* I, II (1981, his [25]); see his bibliography, p.227. GH
  Thm 11.7.1 is quoted from Cogdell's later notes [Cog07, Theorems 4.1 and 4.2],
  and GH p.309 uses Jacquet 2009 [Jac09, §16] for the archimedean ε-factors. The
  two archimedean references are different routes and are kept apart here.
  Shahidi's route is the one H00 cites. None of these routes is formalized, so
  the proof stays with a later proof task.

## 2. Scope and hypotheses

| Item | H86 §2.10 | Cog04 §4 | GH §11.7 | These definitions |
|---|---|---|---|---|
| Representations | arbitrary automorphic | cuspidal, unitary (§3.1, p.211) | cuspidal, trivial on `A_G` | actual cuspidal realizations, no central-character condition |
| Field | number field | global field | global field | number field `F` with `[CompactSpace (AdeleQuotient F)]` |
| Additive character | nontrivial on `K\A_K` | `⊗ψ_v`, trivial on `k` | nontrivial on `F\A_F` | any `ψ` on the adeles; intended: nontrivial, trivial on the diagonal |
| Bad set | `ε_v = 1` off a finite set | `S ⊇ S_∞`, all data unramified off `S` (p.218) | Cor. 11.6.3 | a finite set `S` of finite places (§6) |

Source-to-application gaps:

- **Cuspidal specialization.** H86 states §2.10 and Theorem 4.1 (p.157, proved
  in §4.3) for arbitrary automorphic representations, and H00 Theorem 2.3
  (pp.444–445) has the same generality. The module specializes to actual
  cuspidal realizations `Automorphic.CuspidalOperatorRealization F r` of
  `GL_(r+1)` and `GL_(t+1)`. This is the specialization the Library's consumers
  need: `AssociatedGammaStatement` (module
  `Langlands.Automorphic.AssociatedFactorStatement`) and
  `RelativeGammaComparisonStatement`. It covers the cuspidal application of
  H00 §2.4 (p.445), where `P` and `P'` are cuspidal unitary. It does not cover
  the non-cuspidal cases of H86 Theorem 4.1 or H00 Theorem 2.3.
- **Central characters.** Cog04 assumes unitarity and GH a normalized central
  character. `CuspidalOperatorRealization` assumes neither. GH p.309 reduces the
  general case by the norm shift
  `L(s, π|det|^{s₁} × π'|det|^{s₂}) = L(s + s₁ + s₂, π × π')`. Every cuspidal
  realization is a unitary one twisted by `|det|^t`, and the half-plane of
  convergence moves to `Re s > 1 - Re(t + t')`. The intended statement will
  therefore assert convergence on *some* right half-plane, matching Cog04's `Re s ≫ 0`
  (p.219), and quantify over all realizations. The sharp bound `Re s > 1` of GH
  is not stated.
- **Hecke twists.** H86 §4.3 (pp.158–159) applies the equation to `χΠ × Π'` with
  `χ` a Hecke character of finite order, trivial at the infinite places. These are
  the Library's `CuspidalOperatorRealization.determinantTwist χ hχ` with
  `hχ : χ.HasFiniteOrder`, and the presentations
  `CuspidalSpectralPresentation.determinantTwist`. A statement quantifying over all
  realizations and presentations covers them by specialization. The Library's
  twists do not realize `|det|^t`, so the norm-shift reduction is an obligation
  of the proof (§10), not a specialization of the statement.

## 3. Actual objects

- The finite local components are those of the original spectral presentation
  `P : CuspidalSpectralPresentation T`: `P.localComponent v` at every finite place
  `v`, its exceptional set `P.exceptional`, and the Satake spectra
  `P.spectralSystem.eigenvalues v hv : Unramified.Eigenvalues (r + 1)` for
  `v ∉ P.exceptional`. By `P.hasSpectrum v hv` these are
  the eigenvalues of the actual spherical Hecke operators on the component.
- The completion at `v` is the published p-adic field `padicField v`. Local
  factors are those of the canonical p-adic class `padicClass` of the component.
- The dual side uses other actual realizations `Td`, `Td'` with their own
  presentations `Pd`, `Pd'`. The intended statement will require
  `Td.realization.IsContragredientOf T.realization` and
  `Td'.realization.IsContragredientOf T'.realization`, as in the published
  `CuspidalContragredientStatement`. This is the dual pair `π̃ × π̃'` of Cog04
  Thm 4.1 and `π^∨ × π'^∨` of GH (11.25). JPSS83 writes `π^ι(g) = π(ᵗg⁻¹)`,
  which is equivalent to `π̃` for irreducible `π` ((0.3), pp.376–377).

## 4. Declarations

Namespace `Langlands.Global.CuspidalPairFunctionalEquation`. The field `F` is a
number field with `[CompactSpace (AdeleQuotient F)]`, the instance needed by
`CuspidalOperatorRealization`.

### `residueCardinality v`

The residue cardinality `q_v` of the canonical topological data of
`padicField v`.

### `pairEulerPolynomial a b`

For `a : Unramified.Eigenvalues n` and `b : Unramified.Eigenvalues m`, the
polynomial `∏_(α ∈ a, β ∈ b) (1 - αβ X)`, the product over the multiset product
with multiplicities. Then `pairEulerPolynomial a b` evaluated at `q_v^(-s)` is
`det(1 - q_v^(-s) A ⊗ A')` with `A`, `A'` diagonal with entries `a`, `b`. This is
the unramified pair L-factor of Cog04 Thm 3.3 (p.215):
`L(s, π × π') = det(I - q^(-s) A_π ⊗ A_π')^(-1)` and `ε = 1`. The same formula is
JPSS83 (0.1) and GH Thm 11.6.1 (p.308).

Normalization check. `Unramified.Eigenvalues.eulerPolynomial a` is
`∏_(α ∈ a) (1 - α X)`, and `pairEulerPolynomial a b` has the same shape on the
products `αβ`. The Library's spectral relation `HasSphericalHeckeSpectrum a`
(module `Langlands.Representation.Unramified.HeckeOperators`) makes the `i`-th
standard Hecke operator act by `q^(i(n-i)/2) e_i(a)`, following Gross98 (3.14)
and (6.5)–(6.7), as recorded in that module's Markdown. Here `e_i` is the `i`-th
elementary symmetric function. This is the unitary Satake normalization, so `a`
consists of the Satake parameters `A_π` of Cog04 Thm 3.3, without a further shift
by `q^((n-1)/2)`. The identification of the Satake parameters with the Hecke
eigenvalues for unramified generic components is not proved in the Library
(§10).

### `HasIrreducibleAdmissibleComponents P`

Every finite local component `P.localComponent v` is irreducible and admissible.
This is intrinsic data about the presentation, and it is a hypothesis of the
intended statement, not a conclusion. The consumer precedents take it the same
way: `AssociatedGammaStatement` and `RelativeGammaComparisonStatement` quantify
over irreducible admissible local components, and the published
`CuspidalContragredientPresentationExistenceStatement` produces presentations
with this property. The pair factor predicates are defined on classes, which
need these witnesses.

### `localClass P h v`

The canonical p-adic class `(P.localComponent v).padicClass` of the component at
`v`, of rank `r + 1`, formed with the witnesses `h v`.

### `FinitePairFactorChoice ψ P P' Pd Pd' h h' hd hd'`

Local data at every finite place `v`:

- `additive v` with `IsCanonicalFiniteAdditiveComponent ψ v (additive v)`. The
  local character is the restriction of the global `ψ` to `F_v`, as in Cog04
  (`ψ = ⊗ψ_v`, p.218) and Henniart–Herb 1995 §8.15. It is not a separately
  chosen character.
- `measure v` with `Correspondence.IsSelfDualMeasure`: the iterated Fourier
  transform for `additive v` is `f ↦ f(-x)`, the form of GH App. C.2 (C.3)
  (p.553). Locally, ε depends on `(ψ_v, measure)` (GH (12.13)). Self-dual local
  measures are the ones whose product is the self-dual global measure, which the
  Poisson summation step of Cog04 §4 uses. No JPSS83 measure convention is cited.
- `lPolynomial v` with `Correspondence.IsAutomorphicPairLPolynomial` for
  `(localClass P h v, localClass P' h' v)`, and `dualLPolynomial v` with the same
  predicate for `(localClass Pd hd v, localClass Pd' hd' v)`.
- `epsilon v` with `Correspondence.IsAutomorphicPairEpsilonFactor` for
  `(localClass P h v, localClass P' h' v)`.

The two pair-factor predicates come from modules
`Correspondence.FullLFactorCompatibility` and `Correspondence.FullFactorCompatibility`,
and they descend from representatives to classes. They have different sources.

- **L.** `IsAutomorphicPairLPolynomial` descends
  `RankinSelberg.IsLanglandsPairLPolynomial`, the L-factor of JPSS83 (9.4),
  p.458, defined through the Langlands classification. Both representations are
  Langlands quotients of standard modules `ξ`, `η` of tempered data, and
  `L(s, ξ × η)` is the integral L-factor of the standard modules. For generic
  irreducible quotients, JPSS83 (9.4)(4) gives `L(s, ξ × η) = L(s, π × σ)`, the
  integral factor of the pair itself. In the Library this is
  `GenericLanglandsQuotientLFactorStatement`, a conjunct of the unproved
  `LanglandsQuotientLFactorStatement`.
- **ε.** `IsAutomorphicPairEpsilonFactor` descends
  `RankinSelberg.IsLanglandsPairEpsilonFactor` (module
  `RankinSelberg.LanglandsFactors`). Both representations are Langlands quotients
  of essentially square-integrable data, and for every such pair of data `e` is the
  product of the JPSS epsilon factors of all pairs of blocks. This is the ε of
  H02 §2.8, p.596, last display. Its existence for all irreducible admissible
  pairs is the Library's unproved `LanglandsPairEpsilonFactorExistenceStatement`.
  JPSS83 (9.4) concerns only L. JPSS83 (0.2)(10), p.375, remarks that ε could
  also be defined through the standard module and computed from the
  supercuspidal case by Thm (3.1), which is γ-multiplicativity (pp.404–405).

The global theory uses the integral (Whittaker) factors of the components, which
are generic as local components of cuspidal representations. For L, the
comparison with the classification factor is the target above. For ε, the
Library has no target that compares `IsLanglandsPairEpsilonFactor` with the
integral ε of a generic pair at the same `ψ_v` and measure. It proves the
comparison only for supercuspidal pairs
(`IsLanglandsPairEpsilonFactor.isPadicSymmetricEpsilonFactor_of_isSupercuspidal`,
module `RankinSelberg.SupercuspidalLanglandsEpsilon`). The general comparison is a
separate obligation (§10).

No epsilon factor of the dual pair is included, because the equation has ε only
on the left. The identity `ε(s)ε∨(1 - s) = 1` is not part of the statement.

### `c.finiteL v s`, `c.finiteDualL v s`, `c.finiteEpsilon v s`

`L(s, Π_v × Π'_v) = 1 / P_v(q_v^(-s))`, `L(s, Π∨_v × Π'∨_v) = 1 / P∨_v(q_v^(-s))`
and `ε(s, Π_v × Π'_v, ψ_v) = c_v q_v^(-m_v s)` for `epsilon v = (c_v, m_v)`. The
variable `q_v^(-s)` is `RankinSelberg.spectralPoint q_v s`. These match JPSS83
Thm (2.7)(ii)–(iii) and Cog04 Thms 3.1–3.2 (pp.213–214): `L` is the inverse of a
polynomial with constant term `1` in `q^(-s)`, and ε is a unit monomial. The
ε of the definition excludes the sign of the local functional equation. In the
rank convention of JPSS83 and Cog04, `π` on `GL_n` and `π'` on `GL_m` with
`m ≤ n`, that sign is `ω_π'(-1)^(n-1)`: JPSS83 Thm (2.7)(iii), p.391, and Cog04
Thm 3.2, p.214. The γ-factor without the sign gives
`ε = γ · L(s, π × π') / L(1 - s, π̃ × π̃')`, JPSS83 (0.2)(6), p.374, and Cog04
p.214. The same sign `ω'_v(-1)^(n-1)` is the one cancelled globally in §7.

### `c.IsUnramifiedOutside S`

For a finite set `S` of finite places and every `v ∉ S`:

- if `v ∉ P.exceptional` and `v ∉ P'.exceptional`, then
  `lPolynomial v = pairEulerPolynomial` of the two supplied Satake spectra;
- the same for `dualLPolynomial v` with `Pd`, `Pd'`;
- `epsilon v = (1, 0)`, i.e. `ε_v(s) = 1`.

These are the actual local identities of Cog04 Thm 3.3 (p.215), JPSS83 (0.1) and
GH Thm 11.6.1, 11.6.2 and Cor. 11.6.3 (p.308). They require `ψ_v` unramified and
self-dual measure (GH §11.6 assumes `vol(GL_m(O_v)) = 1`). The intended statement
will assert them for a set `S` that contains all four exceptional sets and all
finite ramification of `ψ` (§6). Then the hypotheses on `v` are automatic. The
identities serve two purposes. They justify ε-triviality outside `S`, so the
global ε is the finite product over `S` and the infinite places. They also
supply the unramified Euler factors in terms of Hecke eigenvalues, which H86
§4.3 cancels against the Frobenius factors on the arithmetic side.

### `c.CompletedEquationHolds S Linf Ldinf εinf`

For functions `Linf`, `Ldinf`, `εinf : ℂ → ℂ`, there exist `σ : ℝ` and
`Λ`, `Λd : ℂ → ℂ` such that:

1. `Λ` and `Λd` are meromorphic on all of `ℂ`;
2. for `σ < Re s`, the sums `∑_v ‖L_v(s) - 1‖` and `∑_v ‖L∨_v(s) - 1‖` over all
   finite places converge, and the finite Euler products have limits `p`, `pd`
   (`HasProd`) with `Λ(s) = Linf(s) p` and `Λd(s) = Ldinf(s) pd`;
3. off a discrete subset of `ℂ` (`Filter.codiscrete ℂ`),
   `Λ(s) = (∏_(v ∈ S) ε_v(s)) εinf(s) Λd(1 - s)`.

The summability conditions give absolute convergence of both Euler products,
as in Cog04 p.219 and GH p.309 (GH Thm 11.5.2 together with [JS81b, Theorem 5.3],
as cited there). The completed functions are `Λ = L_∞ · ∏_(v finite) L_v` over all
places, as in Cog04 pp.218–219, GH (11.23)–(11.24) and JPSS83 (0.1). The equation
has the normalized shift `1 - s` and the dual-side pair `(Pd, Pd')` on the
right. The predicate does not require this pair to be the contragredient pair;
the intended statement will impose that through `IsContragredientOf` (§3). It is the completed equation, not a product of all local γ-factors: GH
p.309 warns that "the product of the local γ-factors does not converge".
Meromorphy is stated on `Set.univ` and the equation holds off a discrete set, so
nothing is claimed at poles. Pole location, boundedness in vertical strips and
nonvanishing are not stated; they belong to other tasks. GH Thm 11.7.1 states
the first two only for representations trivial on `A_GL_n` and `A_GL_m`, and a
norm twist `|det|^t` moves the poles.

The predicate places no condition on `Linf`, `Ldinf`, `εinf`. In the intended
statement they are the finite products over the infinite places of the actual
archimedean pair factors exported by task `6c50b2fd`. They are not arbitrary
meromorphic witnesses (§9).

## 5. Normalizations

- **Additive character.** Finite components are restrictions of `ψ` (§4). At the
  infinite places the sources use different signs. GH App. C.1 (p.551) has
  `ψ_ℝ(a) = e^(-2πia)`, while Jacquet 2009 App. 16 and Shahidi 1985 p.974 have
  `e^(2πix)` and `e^(2πi(z + z̄))`. The intended statement will quantify over every
  nontrivial `ψ` trivial on `F`, and each archimedean ε will be taken at the actual
  component `ψ_v`, so the sign does not matter. The Library already pins
  archimedean components through `IsRealAdditiveComponent ψ v hv a` and
  `IsComplexAdditiveComponent ψ v hv a` (module `HeckeFunctionalEquationStatement`)
  with an arbitrary nonzero scale `a`. These are additive characters, not
  representation components. The change-of-ψ rule at infinity is Jacquet 2009
  Remark 2.2 (pp.7–8).
- **Measures.** Self-dual for the local component at every place (§4).
- **Shift and dual pair.** `1 - s`, with the dual-side pair; the intended
  statement will require it to be the actual contragredient pair (§3).
- **ε independent of ψ.** Cog04 p.219, GH p.308 and H86 §2.10 state that the
  global ε-product does not depend on `ψ`. The intended statement will hold for every
  `ψ` but will have no separate conjunct comparing two characters.

## 6. The single exceptional set

The intended statement will assert one finite set `S` of finite places with:

- `P.exceptional ∪ P'.exceptional ∪ Pd.exceptional ∪ Pd'.exceptional ⊆ S`;
- `Global.FiniteAdditiveSupport ψ S` (module `RelativeGammaComparisonStatement`):
  every canonical finite component of `ψ` outside `S` has additive conductor
  zero. For `F ≠ ℚ` and the standard character, this includes the places
  dividing the different;
- `c.IsUnramifiedOutside S` (§4);
- `c.CompletedEquationHolds S …` with this same `S`.

As the Library's docstring of `FiniteAdditiveSupport` says, conductor zero alone
does not assert ε-triviality, so the identities of `IsUnramifiedOutside` are
stated as well. The infinite places are not in `S`. Their factors enter through
the archimedean products.

## 7. Auxiliary sign cancellation

In the proof of Cog04 Thm 4.1 (p.220), dividing the global integral equation by
the local equations at `v ∈ S ∪ S_∞` leaves `∏_v ω'_v(-1)^(n-1) ε_v`. The sign is
`1` because `ω'_v(-1) = 1` at unramified places, and
`∏_v ω'_v(-1) = ω'(-1) = 1` since the central character `ω'` is trivial on
`F^×`. The infinite places must be included here, since `ω'_v(-1)` can be `-1`
there. Henniart–Herb 1995 p.181 makes the analogous remark for Shahidi's
coefficients. The local ε above excludes this sign (§4), so the global equation
contains no sign, and the cancellation is part of the proof, not the statement.
The Library has the global central character (`T.HasCentralCharacter χ`,
`HasUnitaryCentralCharacter T`). Expressing the archimedean local signs needs the
archimedean components (§9).

## 8. Existence

The intended statement will assert the existence of the objects it uses and will
not take them as hypotheses. It will require `Nonempty (FinitePairFactorChoice …)`,
which gives local additive components, self-dual measures and both kinds of
local pair factors at every finite place. It will also require the existence of the
archimedean data once that data is exported. The analytic conclusions will then be
asserted for *every* choice `c` (§4). Each field is determined by its predicate
(canonical component, self-dual measure, normalized generator), so this is the
universal form of a unique choice. The completed functions and the meromorphic
continuation are existentially quantified inside `CompletedEquationHolds`.

## 9. Archimedean gate (task `6c50b2fd-cb4a-47b3-8f5d-d464916d69fb`)

At every infinite place `v` the sources need the following:

- the actual archimedean component `Π_v` of the cuspidal realization (a
  Casselman–Wallach representation in Jacquet 2009 §2);
- its Langlands parameter `ρ_(Π_v)`, a semisimple representation of `W_ℝ` or
  `W_ℂ`;
- the component `ψ_v` of `ψ` with its self-dual measure;
- `L(s, Π_v × Π'_v) = L(s, ρ ⊗ ρ')` and `ε(s, Π_v × Π'_v, ψ_v) = ε(s, ρ ⊗ ρ', ψ_v)`
  for the pair and for the dual pair (Cog04 §3.2, p.216; GH §12.3, p.326;
  Jacquet 2009 Thm 2.1 and App. 16);
- compatibility with contragredients: `ρ_(Π̃_v) = ρ_(Π_v)^∨`.

For the twists of H86 §4.3 the intended statement will also need `(χΠ)_∞ = Π_∞` when
`χ` is trivial at infinity.

The Library has genuine presented Weil-side objects (`RealPresentation`,
`ComplexPresentation` and their L- and epsilon factors) and archimedean place
actions (`ArchimedeanPlaceLie`, `ArchimedeanPlaceEnveloping`,
`PlaceEnvelopingAction`). None of these is an attachment of an actual
automorphic component. As of Library `f73044d9` and Worker 2's draft revision
175 (`INTERFACES.md`), the actual archimedean components, their attachment, the
pair L- and epsilon factors and the compatibility with contragredients at
infinity are still missing. The operator's decision reserves them to Worker 2's
task. This module neither rebuilds them nor replaces them by arbitrary
meromorphic witnesses. The completed statement will be defined once those exports
are public.

## 10. Remaining proof obligations

A later proof of the completed statement has to supply:

1. the global integral representation and its continuation (Jacquet–Shalika 1981;
   Cog04 §4), or Shahidi's route (Shahidi 1981 Thm 4.1 for partial L-functions,
   together with the local-coefficient comparisons Shahidi 1984 Thm 5.1 and
   Shahidi 1985 Thm 1 / Thm 3.1);
2. the finite local theory (JPSS83 Thm (2.7)) and the comparison of the
   integral factors of generic components with the classification factors used
   here (§4):
   - for L, JPSS83 (9.4)(4), p.458, the Library target
     `GenericLanglandsQuotientLFactorStatement`, a conjunct of
     `LanglandsQuotientLFactorStatement`;
   - for ε, the identity, for generic irreducible pairs, of the block product of
     H02 §2.8 (`IsLanglandsPairEpsilonFactor`) with the integral ε of the pair at
     the same `ψ_v` and self-dual measure. No Library statement expresses this
     yet. It needs its own target and proof. A possible route uses
     γ-multiplicativity, JPSS83 Thm (3.1)(i) (Library
     `GammaMultiplicativityStatement`), and the block product formula for L,
     JPSS83 Thm (9.5) (Library `SquareIntegrableDataLFactorStatement`, a conjunct
     of `LanglandsQuotientLFactorStatement`), applied to the pair and to the
     contragredient pair. These give the identity because
     `ε = γ · L(s, π × σ) / L(1 - s, π̃ × σ̃)` (JPSS83 (0.2)(6)), and because H02
     §2.8 writes `J∨` as the Langlands quotient of the contragredient blocks in
     reversed order. The route also needs each generic component to be the full
     induced representation of its blocks, so that Thm (3.1) applies to it. The
     Library proves only the supercuspidal case;
3. the archimedean local theory for the exported archimedean factors, either by
   Jacquet–Shalika 1990 and the archimedean parts of Jacquet–Shalika 1981, as in
   Cog04 §3.2 (p.216), or by Jacquet 2009 (Thm 2.1, §16), as in GH p.309;
4. the unramified computation (Cog04 Thm 3.3; GH §11.6) and the identification
   of the Satake parameters with the Library's Hecke eigenvalues;
5. the norm-shift reduction to normalized central characters (GH p.309),
   including local shift identities and a realization of `π|det|^t`;
6. the sign cancellation of §7;
7. absolute convergence (GH Thm 11.5.2 and [JS81b, Theorem 5.3], as cited on
   GH p.309).

The exact target name for the proof task is fixed when the statement
`CuspidalPairGlobalFunctionalEquationStatement` is defined.
