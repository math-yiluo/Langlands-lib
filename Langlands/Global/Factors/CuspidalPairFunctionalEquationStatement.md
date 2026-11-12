# The completed global Rankin–Selberg functional equation of cuspidal pairs

Author: Worker 5013. Statement contribution to task
`876d1f0c-d287-4743-adf6-aef3a9efb5ba`, revision 1.

**Scope.** This module defines one proposition and proves nothing:

- `Langlands.Global.CuspidalPairGlobalFunctionalEquationStatement`
  (module `Langlands.Global.Factors.CuspidalPairFunctionalEquationStatement`).

It is the completed global functional equation for Rankin–Selberg pairs of actual
cuspidal realizations of `GL_(r+1)` and `GL_(t+1)` over a number field. Its finite
places use the vocabulary of the published `CuspidalPairFactorData` (namespace
`Langlands.Global.CuspidalPairFunctionalEquation`). Its infinite places use Task
`6c50b2fd`'s published archimedean exports:
`OperatorRealization.HasRealPlaceParameter` and `HasComplexPlaceParameter`
(`Langlands.Automorphic.ArchimedeanPlaceParameter`), and the pair factors
`realPairLFactor`, `realPairEpsilon`, `complexPairLFactor` and `complexPairEpsilon`
(`Langlands.LocalFactor.ArchimedeanPairFactor`). Nothing is rebuilt here.

**Proof target.** A later proof task should prove the Library statement
`Langlands.Global.CuspidalPairGlobalFunctionalEquationStatement`, with universe
parameters `u` (the number field) and `uQ` (the factor universe of the spectral
presentations).

## 1. Sources

"p." is the printed page and "PDF" the page of the registered file.

| Source ID | Short name | Locators used |
|---|---|---|
| `henniart-1986-cyclic` | H86 | §2.10 p.155 (PDF 12); §4.3 pp.158–159 (PDF 15–16) |
| `henniart-2000-simple-proof` | H00 | §2.3 pp.444–445 (PDF 6–7); §2.4 p.445 |
| `cogdell-2004-analytic-theory-gln` | Cog04 | p.211 (PDF 214); Thm 3.3 p.215; §3.2 p.216 (PDF 219); Thm 3.6 p.217 (PDF 220); pp.218–219 and Thm 4.1 p.219 (PDF 222); proof p.220 (PDF 223) |
| `getz-hahn-2024-automorphic-representations` | GH | §11.6 (11.23)–(11.24) p.308 (PDF 319); Thm 11.7.1 and the norm shift, p.309 (PDF 320); App. C pp.551–553 |
| `getz-hahn-2024-errata-2026-10` | GH errata | p.3: the only Chapter 11 entry (§11.5) is editorial; none concerns §11.6–11.7 |
| `jpss-1983-rankin-selberg` | JPSS83 | p.368 (announcement); (0.1); (0.2)(6) p.374; Thm (2.7) pp.390–391; (9.4) p.458 (PDF 93) |
| `jacquet-2009-archimedean-rankin-selberg` | Jac09 | Thm 2.1 p.6; Remark 2.2 pp.7–8; §16 |
| `knapp-1994-archimedean-llc` | Knapp | Thm 1 p.400 (PDF 410); Thm 2 p.403 (PDF 413); Thms 4–5 pp.405–406 |
| `tate-1979-number-theoretic-background` | Tate | (3.2.4)–(3.2.5) p.13 (PDF 22); (3.4.1)–(3.4.2) pp.14–15 |
| `henniart-herb-1995-induction` | HH95 | §8.15 p.181 |
| `henniart-2002-characterization` | H02 | §2.8 p.596 (PDF 10) |

The finite-place locators, the comparison of the finite factors with JPSS83 and
H02, and the separation of announcement from proof are recorded in
`CuspidalPairFactorData.md` §§1–4. They are summarized here.

**What the sources state.** H86 §2.10 (p.155) states, for automorphic `Π`, `Π'` of
`GL(n)`, `GL(m)` over a number field: `L(Π × Π')(s) = ∏_v L(Π_v × Π'_v)(s)` for
`Re s` large; `ε(Π_v × Π'_v, ψ_v) = 1` off a finite set; the global
`ε(Π × Π') = ∏_v ε(Π_v × Π'_v, ψ_v)` is independent of `ψ`; and
`L(Π × Π')(s) = ε(Π × Π')(s) L(Π∨ × Π'∨)(1 - s)`. H86 attributes this to the 1981
note of Jacquet, Piatetski-Shapiro and Shalika. H00 §2.3 (pp.444–445) uses these
equations through Theorem 4.1 of H86 and attributes them to Shahidi, with the
comments of HH95 §8.15. JPSS83 p.368 announces the global result, and HH95 §8.15
(p.181) notes that the 1981 note announced it without proof. The established
statements followed here are:

- Cog04 Thm 4.1 (p.219): for cuspidal `π`, `π'`, `L(s, π × π')` has a meromorphic
  continuation, is bounded in vertical strips, and satisfies
  `L(s, π × π') = ε(s, π × π') L(1 - s, π̃ × π̃')`. Here `L` and `ε` are the
  products over all places, including the archimedean ones (pp.218–219).
- GH Thm 11.7.1 (p.309), for the completed function `Λ(s, π × π')` of
  (11.23)–(11.24) (p.308): meromorphic continuation and
  `Λ(s, π × π') = ε(s, π × π') Λ(1 - s, π^∨ × π'^∨)`.

## 2. The statement

For every

- number field `F` with `[CompactSpace (AdeleQuotient F)]` (the instance needed by
  `CuspidalOperatorRealization`);
- unitary additive character `ψ` of the adeles that is nontrivial
  (`∃ x, ψ x ≠ 1`) and trivial on the diagonal image of `F`;
- `r t : ℕ`, actual cuspidal realizations `T`, `Td` of `GL_(r+1)` and `T'`, `Td'`
  of `GL_(t+1)` (`Automorphic.CuspidalOperatorRealization`), with
  `Td.realization.IsContragredientOf T.realization` and
  `Td'.realization.IsContragredientOf T'.realization`;
- spectral presentations `P`, `P'`, `Pd`, `Pd'` of `T`, `T'`, `Td`, `Td'`
  (`Automorphic.CuspidalSpectralPresentation`), with witnesses `h`, `h'`, `hd`, `hd'`
  of `HasIrreducibleAdmissibleComponents`,

the statement asserts the conjunction of the following.

1. **Existence of the local data.**
   - `Nonempty (FinitePairFactorChoice ψ P P' Pd Pd' h h' hd hd')`: at every finite
     place there are the canonical component of `ψ`, a self-dual measure, the pair
     L-polynomials of `(P, P')` and of `(Pd, Pd')`, and the pair ε-factor of
     `(P, P')` (`CuspidalPairFactorData.md` §4).
   - At every real place `v`: some `a : ℝˣ` with `IsRealAdditiveComponent ψ v a`,
     and for each of `T`, `T'`, `Td`, `Td'` some block list `ds` with
     `OperatorRealization.HasRealPlaceParameter _ v ds`.
   - At every complex place `v`: some `a : ℂˣ` with
     `IsComplexAdditiveComponent ψ v a`, and for each of the four realizations some
     `ds` with `OperatorRealization.HasComplexPlaceParameter _ v ds`.
2. **One finite set and the completed equation.** There is `S : Finset (FinitePlace F)`
   with
   - `P.exceptional ⊆ S`, `P'.exceptional ⊆ S`, `Pd.exceptional ⊆ S` and
     `Pd'.exceptional ⊆ S`;
   - `FunctionalEquationComparison.FiniteAdditiveSupport ψ S`: every canonical finite
     component of `ψ` outside `S` has conductor zero;
   - for every finite choice `c`:
     - `c.IsUnramifiedOutside S`: outside `S` the two L-polynomials are the
       unramified Euler polynomials of the Satake spectra, and `ε_v = 1`;
     - for every family `aR`, `aC` of archimedean additive components of `ψ` and
       every family of archimedean parameters `dR`, `dR'`, `dRd`, `dRd'` (real
       places) and `dC`, `dC'`, `dCd`, `dCd'` (complex places) of `T`, `T'`, `Td`,
       `Td'`, the predicate `c.CompletedEquationHolds S L∞ L∞∨ ε∞` holds for the
       archimedean factors of §3.

`CompletedEquationHolds` (`CuspidalPairFactorData.md` §4) asserts that there are
`σ : ℝ` and functions `Λ`, `Λ∨ : ℂ → ℂ` such that:

- `Λ` and `Λ∨` are meromorphic on all of `ℂ`;
- for `σ < Re s` the finite Euler products of `(P, P')` and of `(Pd, Pd')` converge
  absolutely (summability of `‖L_v(s) - 1‖`), with
  `Λ(s) = L∞(s) ∏_(v finite) L_v(s)` and the same for `Λ∨`;
- off a discrete subset of `ℂ`,
  `Λ(s) = (∏_(v ∈ S) ε_v(s)) ε∞(s) Λ∨(1 - s)`.

So the statement asserts right-half-plane convergence of the actual Euler products,
meromorphic continuation of the actual completed functions, and the completed equation
with the contragredient pair and the shift `1 - s`. The global ε is the finite product
over `S` and the infinite places. Outside `S` the local identities
`IsUnramifiedOutside` give `ε_v = 1`. The completed functions and their continuations
are existentially quantified. They are not assumed.

## 3. Archimedean factors

At an infinite place the statement uses the archimedean pair factors of the
parameters of the realizations at that place. Write `RP` and `CP` for the real and
complex places. In the Lean statement:

- `L∞(s) = ∏_(v ∈ RP) (realPairLFactor (dR v) (dR' v)).denominator(s)⁻¹ ·
  ∏_(v ∈ CP) (complexPairLFactor (dC v) (dC' v)).denominator(s)⁻¹`;
- `L∞∨(s)` is the same with `dRd`, `dRd'`, `dCd`, `dCd'`;
- `ε∞(s) = ∏_(v ∈ RP) realPairEpsilon (dR v) (dR' v) (aR v) |aR v|^(1/2) s ·
  ∏_(v ∈ CP) complexPairEpsilon (dC v) (dC' v) (aC v) ‖aC v‖ s`.

The L-factors are `ReciprocalEntire` values, so `L(s) = 1 / denominator(s)` with an
entire denominator. In Lean, `0⁻¹ = 0` at a pole. This affects only the values of
`L∞` and `L∞∨` at poles. The Euler-product identity is required only on a right
half-plane, and the existential `σ` may be chosen to the right of all archimedean
poles. The completed equation holds off a discrete set, so nothing is claimed at
poles.

**Parameters.** `HasRealPlaceParameter X v ds` says that the rank of `ds` is the rank
of the realization and that the `(𝔤, K)`-module of the standard module of `ds` maps
injectively and equivariantly into the realization's space under the place actions
at `v` (`ArchimedeanPlaceParameter.md`). For an irreducible realization, by the
explanation in that Markdown (Flath's factorization), this means that the archimedean
component `π_v` is infinitesimally equivalent to the standard module of `ds`. For a generic `π_v` this
holds for the blocks of its Langlands parameter, in any order (Knapp Thms 1–2, 4–5).
Local components of cuspidal representations are generic: Cog04 p.211 says so for
the non-archimedean places ("as is true for local components of cuspidal
representations"), and the archimedean integrals of Cog04 §3.2 (p.217) are likewise
formed with Whittaker functions `W ∈ W(π, ψ)`.

**Pair factors.** `realPairLFactor ds ds'` and `realPairEpsilon ds ds' a c hc s` are
Tate's factors of the block decomposition of `σ ⊗ σ'`
(`ArchimedeanPairFactor.md`). The ε-factor is taken at the character
`x ↦ e^(2πi a x)` and the measure `c dx`. The complex factors use
`z ↦ e^(2πi Tr(a z))` and `c · 2 dx dy`. These are the archimedean factors of
Cog04 §3.2 (p.216): Jacquet–Shalika *define*
`L(s, π × π') = L(s, ρ_π ⊗ ρ_π')` and `ε(s, π × π', ψ) = ε(s, ρ_π ⊗ ρ_π', ψ)`
through the local Langlands correspondence. In Jac09 Thm 2.1 (p.6) the archimedean
integrals are holomorphic multiples of `L(s, σ ⊗ σ')` and satisfy local functional
equations with the Weil-side `γ(s, σ ⊗ σ', ψ)`; GH p.309 uses Jac09 §16.

**Additive characters and self-dual measures.** `IsRealAdditiveComponent ψ v a` and
`IsComplexAdditiveComponent ψ v a` (published in
`Langlands.Global.Factors.HeckeFunctionalEquationStatement`) say that `ψ` restricted
to the `v` coordinate of the infinite adeles is `realScaledCharacter a` or
`complexScaledCharacter a`. The coordinate is read through Mathlib's
`InfinitePlace.Completion.ringEquivRealOfIsReal` or `ringEquivComplexOfIsComplex`.
The place actions of the parameters use the same coordinates. The measure scale is
self-dual for this character:

- real place, `ψ_v(x) = e^(2πi a x)`: `c = |a|^(1/2)`, written
  `NNReal.sqrt ‖(a : ℝ)‖₊`;
- complex place, `ψ_v(z) = e^(2πi Tr(a z))`: `c = ‖a‖`, written `‖(a : ℂ)‖₊`.

These are the scales of the published Hecke statement
(`HeckeFunctionalEquationStatement.md`). They follow from Tate (3.2.4)–(3.2.5)
(`dx` self-dual for `e^(2πi x)`, `2 dx dy` for `e^(2πi Tr z)`), and the dilation
`x ↦ ψ(ax)` multiplies the self-dual measure by `|a|_v^(1/2)`. They are derived
content.

The archimedean ε of the dual pair does not appear, because the equation has ε only
on the left.

## 4. Finite factors and the single exceptional set

These are as in `CuspidalPairFactorData.md` §§4 and 6:

- the local components are those of the original spectral presentations, at the
  completions `padicField v`, through their canonical p-adic classes;
- L is the Langlands-classification pair L-factor (JPSS83 (9.4)) and ε is the block
  product of H02 §2.8, both at the restriction of `ψ` with a self-dual measure. The
  ε excludes the sign `ω'_v(-1)^(n-1)` of the local functional equation (JPSS83
  Thm (2.7)(iii); Cog04 Thm 3.6);
- outside `S`, `IsUnramifiedOutside` gives the unramified Euler factors of the Satake
  spectra (Cog04 Thm 3.3; GH §11.6) and `ε_v = 1`. These are the actual local
  identities that justify ε-triviality and the cancellation of unramified factors in
  H86 §4.3.

There is one set `S` for the bad places of all four presentations and for the finite
ramification of `ψ`, and the same `S` is used in the completed equation.

## 5. Normalizations

- **Shift and dual pair.** `1 - s`, with the actual contragredient pair `(Td, Td')`
  and its own presentations `(Pd, Pd')`. This is `π̃ × π̃'` of Cog04 Thm 4.1 and
  `π^∨ × π'^∨` of GH Thm 11.7.1. The dual L-factors at every place are those of
  `Td` and `Td'` themselves, not a formal dual of the parameters of `T` and `T'`.
- **Sign.** No sign appears in the equation. In Cog04's proof (p.220), the signs
  `ω'_v(-1)^(n-1)` from the local functional equations multiply to
  `ω'(-1)^(n-1) = 1` over all places, including the infinite ones. The local ε-factors
  of the statement exclude this sign at the finite places. At the infinite places
  `ε(s, ρ ⊗ ρ', ψ_v)` is the Artin–Weil ε of Cog04 §3.2. Cog04 Thm 3.6 (p.217) and
  Jac09 Thm 2.1(iii) put the sign in front of γ, so the archimedean ε excludes it too.
- **Additive characters.** The finite components are restrictions of `ψ`. The
  archimedean ones are the actual components `aR v`, `aC v`. The sign conventions of
  GH App. C.1 (`e^(-2πia)`) and Jac09 (`e^(2πix)`) differ. The statement holds for
  every nontrivial `ψ` trivial on `F`, so it does not depend on either choice.
- **Independence of ψ.** H86 §2.10, Cog04 p.219 and GH p.308 note that the global ε
  does not depend on `ψ`. The statement holds for every `ψ` and has no separate
  conjunct comparing two characters.
- **Half-plane.** The statement asserts convergence on *some* right half-plane, as in
  Cog04 p.219 (`Re s ≫ 0`). The sharp `Re s > 1` of GH needs normalized
  central characters (§6).

## 6. Source-to-application gaps

- **Cuspidal pairs only.** H86 §2.10 and Theorem 4.1, and H00 Theorem 2.3, are
  stated for arbitrary automorphic representations. The statement covers actual
  cuspidal realizations, as needed by the cuspidal application H00 §2.4 (p.445) and
  by the Library consumers `AssociatedGammaStatement` and
  `RelativeGammaComparisonStatement`. It does not cover non-cuspidal (isobaric)
  pairs.
- **Central characters and the norm shift.** Cog04 assumes unitary and GH normalized
  central characters. `CuspidalOperatorRealization` assumes neither, and the
  statement quantifies over all realizations. GH p.309 reduces the general case by
  `L(s, π|det|^(s₁) × π'|det|^(s₂)) = L(s + s₁ + s₂, π × π')`. The reduction is a
  proof obligation (§8). Poles and boundedness in vertical strips are not stated;
  they move under the norm shift and belong to other tasks.
- **Hecke-character twists.** H86 §4.3 applies the equation to `χΠ × Π'` with `χ` of
  finite order. These are the Library's `CuspidalOperatorRealization.determinantTwist
  χ hχ` (`hχ : χ.HasFiniteOrder`) with `CuspidalSpectralPresentation.determinantTwist`.
  The statement quantifies over all realizations and presentations, so it covers them
  by specialization, with the twist's own archimedean parameters. The identity
  `(χΠ)_∞ = Π_∞` for `χ` trivial at infinity is not part of the statement.
- **Contragredients and presentations are supplied.** The statement takes `Td`, `Td'`
  with `IsContragredientOf` and arbitrary presentations with irreducible admissible
  components as inputs. Their existence is a separate matter: the Library has
  `CuspidalUnitaryContragredientExistenceStatement` (unitary central character) and
  `CuspidalContragredientPresentationExistenceStatement`. For a realization with no
  supplied contragredient the statement says nothing.
- **Realizations and classes.** The statement is phrased for realizations. The
  parameter predicates descend to isomorphism classes
  (`CuspidalOperatorRealization.IsoClass.HasRealPlaceParameter`,
  `HasComplexPlaceParameter`), so a consumer working with classes applies the
  statement to representative realizations.
- **Number field.** Cog04 and GH also allow global function fields. The Library realizations
  are over number fields.

## 7. Design

- **Existence, then every choice.** The statement asserts that the finite data, the
  archimedean additive components and the archimedean parameters exist. It then asserts
  the analytic conclusions for every choice of them. The finite data and the additive
  components are determined by their predicates (`CuspidalPairFactorData.md` §8;
  `e^(2πi a x)` determines `a`). By Knapp's Theorem 1, the parameter of `π_v` is
  determined up to the order of its blocks; the Library's block lists may also write a
  weight-zero induced block as two characters (§8 item 3). So the universal form says
  nothing beyond the source equation, provided the pair factors agree on all lists
  attached to the same component. This agreement is a proof obligation.
- **No family of certified factors.** The archimedean factors are the published
  factors of the actual parameters. They are not arbitrary meromorphic witnesses, and
  no factor family satisfying the equation is assumed.
- **Template.** The shape follows the published `HeckeGlobalFunctionalEquationStatement`
  (module `Langlands.Global.Factors.HeckeFunctionalEquationStatement`): ψ hypotheses,
  real and complex additive components, self-dual archimedean scales, existence
  conjuncts and finite-place choices.
- **General library.** The statement uses the Library's general automorphic
  realizations (`OperatorRealization`, `CuspidalOperatorRealization`,
  `CuspidalSpectralPresentation`), its general local factor objects and Mathlib's
  number-field places. It introduces no new analytic theory.

## 8. Remaining proof obligations

A proof of `Langlands.Global.CuspidalPairGlobalFunctionalEquationStatement` must
supply:

1. the global theory: the Jacquet–Shalika integrals, their Euler factorization and
   continuation (Cog04 §§2, 4) or Shahidi's route (`CuspidalPairFactorData.md` §10
   item 1);
2. the finite local theory and the comparison of the integral factors of generic
   components with the classification L-factor and the block-product ε used here
   (`CuspidalPairFactorData.md` §10 item 2);
3. at the infinite places:
   - existence of parameters: genericity of archimedean components of cuspidal
     representations, the Langlands classification (Knapp Thms 1–2, 4–5) and the
     irreducibility of standard modules of generic representations;
   - independence of the factors from the parameter: if two lists satisfy
     `HasRealPlaceParameter` (or `HasComplexPlaceParameter`) for the same
     realization and place, their pair factors with any second list agree, and
     symmetrically in the second argument.
     Permutations are covered by the published `realPairLFactor_perm`,
     `realPairEpsilon_perm` and their complex analogues. If a weight-zero induced
     block and the corresponding two characters can both occur, the comparison needs
     the duplication formula and Tate's ε of induced representations;
   - the archimedean local theory relating the integrals to these factors
     (Jacquet–Shalika 1990, as in Cog04 §3.2; or Jac09 Thm 2.1 and §16);
4. the unramified computation and the identification of Satake parameters with the
   Library's Hecke eigenvalues (`CuspidalPairFactorData.md` §10 item 4);
5. the norm-shift reduction (GH p.309), including the local shift identities at every
   place and a realization of `π|det|^t`;
6. the sign cancellation of §5, including the archimedean signs `ω'_v(-1)`;
7. absolute convergence of the Euler products (GH Thm 11.5.2 and [JS81b, Thm 5.3], as
   cited on GH p.309).
