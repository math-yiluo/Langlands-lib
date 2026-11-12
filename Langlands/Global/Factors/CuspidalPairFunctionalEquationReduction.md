# Reduction of the completed Rankin–Selberg functional equation of cuspidal pairs

Author: Worker 5013. Intermediate result for Task 5493
(`8e9a5dd6-1b51-4e53-af72-ca2e6d42fe0a`), which must prove
`Langlands.Global.CuspidalPairGlobalFunctionalEquationStatement.{u, uQ}`.

**Scope.** The module `Langlands.Global.Factors.CuspidalPairFunctionalEquationReduction`
defines four propositions and proves one theorem:

- `CuspidalPairLocalDataStatement.{u, uQ}`: the local data and the unramified identities;
- `CuspidalArchimedeanParameterExistenceStatement.{u}`: archimedean parameters exist;
- `CuspidalPairCompletedEquationStatement.{u, uQ}`: the completed equation for every
  admissible exceptional set;
- `CuspidalPairFunctionalEquationReductionStatement.{u, uQ}`: the three imply the target;
- `cuspidalPairFunctionalEquationReduction`, a proof of the last proposition.

The module does not prove the target. The three parts remain open. Section 5 lists
who owns each.

All names below are in namespace `Langlands.Global`. The vocabulary is that of the
target (`CuspidalPairFunctionalEquationStatement.md` §§2–4): `FinitePairFactorChoice`,
`IsUnramifiedOutside` and `CompletedEquationHolds` from `CuspidalPairFactorData`;
`IsRealAdditiveComponent` and `IsComplexAdditiveComponent` from
`HeckeFunctionalEquationStatement`; `FunctionalEquationComparison.FiniteAdditiveSupport`;
`OperatorRealization.HasRealPlaceParameter` and `HasComplexPlaceParameter` from
`ArchimedeanPlaceParameter`; and the archimedean pair factors `realPairLFactor`,
`realPairEpsilon`, `complexPairLFactor` and `complexPairEpsilon`. Nothing is
redefined.

## 1. The three parts

Write *the common data* for: a number field `F` (universe `u`) with
`[CompactSpace (AdeleQuotient F)]`; a unitary additive character `ψ` of the adeles
with `∃ x, ψ x ≠ 1` and `∀ x : F, ψ (diagonal F x) = 1`; `r t : ℕ`; actual cuspidal
realizations `T`, `Td` of `GL_(r+1)` and `T'`, `Td'` of `GL_(t+1)`; spectral
presentations `P`, `P'`, `Pd`, `Pd'` of them (universes `u`, `uQ`); witnesses `h`,
`h'`, `hd`, `hd'` of `HasIrreducibleAdmissibleComponents`; and the contragredient
hypotheses `Td.realization.IsContragredientOf T.realization` and
`Td'.realization.IsContragredientOf T'.realization`. These are exactly the hypotheses
of the target.

**`CuspidalPairLocalDataStatement`.** For the common data:

1. `Nonempty (FinitePairFactorChoice ψ P P' Pd Pd' h h' hd hd')`;
2. for every real place `v`, some `a : ℝˣ` with `IsRealAdditiveComponent ψ v a`;
3. for every complex place `v`, some `a : ℂˣ` with `IsComplexAdditiveComponent ψ v a`;
4. some `S : Finset (FinitePlace F)` containing `P.exceptional`, `P'.exceptional`,
   `Pd.exceptional` and `Pd'.exceptional`, with `FiniteAdditiveSupport ψ S`, such
   that every `c : FinitePairFactorChoice ψ P P' Pd Pd' h h' hd hd'` satisfies
   `c.IsUnramifiedOutside S`.

**`CuspidalArchimedeanParameterExistenceStatement`.** For every number field `F` with
`[CompactSpace (AdeleQuotient F)]`, every `r` and every actual cuspidal realization
`T` of `GL_(r+1)`: at every real place `v` some list `ds` of real blocks satisfies
`OperatorRealization.HasRealPlaceParameter T.realization v ds`, and at every complex
place `v` some list `ds` of complex characters satisfies
`OperatorRealization.HasComplexPlaceParameter T.realization v ds`.

**`CuspidalPairCompletedEquationStatement`.** For the common data, every
`S : Finset (FinitePlace F)` containing the four exceptional sets with
`FiniteAdditiveSupport ψ S`, every `c` with `c.IsUnramifiedOutside S`, every family
`aR`, `aC` of archimedean components of `ψ`, and every family of archimedean
parameters `dR`, `dR'`, `dRd`, `dRd'` (real places) and `dC`, `dC'`, `dCd`, `dCd'`
(complex places) of `T`, `T'`, `Td`, `Td'`:
`c.CompletedEquationHolds S L∞ L∞∨ ε∞`. Here `L∞`, `L∞∨` and `ε∞` are written out
in Lean exactly as in the target (target Markdown §3): products over the real and
complex places of the inverse denominators of the pair L-factors and of the pair
ε-factors at `aR v` with scale `|aR v|^(1/2)`, and at `aC v` with scale `‖aC v‖`.

**`CuspidalPairFunctionalEquationReductionStatement`** is the implication
`CuspidalPairLocalDataStatement.{u, uQ} → CuspidalArchimedeanParameterExistenceStatement.{u}
→ CuspidalPairCompletedEquationStatement.{u, uQ} →
CuspidalPairGlobalFunctionalEquationStatement.{u, uQ}`.

## 2. Provenance

The split is derived from the target. It regroups the conjuncts of
`CuspidalPairGlobalFunctionalEquationStatement` by the theory each one needs:

- the local data part collects the finite factor choice, the archimedean components
  of `ψ`, and the set `S` with its unramified identities. These are local statements
  at finite places and the components of `ψ`, as described in
  `CuspidalPairFactorData.md` §4 and target Markdown §4: the unramified factors of
  Cog04 Thm 3.3 (p.215) and GH §11.6, ε trivial for unramified data, and Tate's
  self-dual scales (target Markdown §3);
- the parameter part is the target's parameter conjuncts, stated for every actual
  cuspidal realization instead of the four given ones. Its content is that the
  archimedean components of cuspidal representations are generic (Cog04 p.211 at the
  finite places; the archimedean integrals of Cog04 §3.2 p.217 use Whittaker models
  `W(π_v, ψ_v)`) and that a generic irreducible representation of `GL_n(ℝ)` or
  `GL_n(ℂ)` is its full standard module, whose blocks come from the Langlands
  parameter (Knapp Thms 1–2, pp.400–403, and Thms 4–5, pp.405–406; Jac09 Thm 2.1,
  p.6, and Remark 2.2, pp.7–8). How `HasRealPlaceParameter` encodes this is
  explained in `ArchimedeanPlaceParameter.md` and target Markdown §3;
- the completed equation part is the target's last conjunct, for every admissible
  `S` instead of one `S`. Its content is Cog04 Thm 4.1 (p.219) and GH Thm 11.7.1
  (p.309), with the normalizations of target Markdown §5.

**Relation to the target.**

- The completed equation part follows from the target. Let `S₀` be the set the
  target provides, and let `S` and `c` be as in the completed equation part. At a
  place of `S \ S₀`, `ε_v = 1` by `c.IsUnramifiedOutside S₀`. At a place of `S₀ \ S`,
  `ε_v = 1` by `c.IsUnramifiedOutside S`. So the finite ε-products over `S` and `S₀`
  agree, and `CompletedEquationHolds S` is `CompletedEquationHolds S₀` for the same
  data. The quantification over every admissible `S` therefore adds nothing beyond
  the target. It makes the part independent of how the local data part chooses `S`.
- The local data part follows from the target: it has the target's hypotheses, and
  its conjuncts are conjuncts of the target (the factor choice, the components of
  `ψ`, and the target's `S` with its inclusions, `FiniteAdditiveSupport ψ S` and the
  unramified identities).
- The parameter part is stated for every actual cuspidal realization. The target
  needs it only for realizations that occur with contragredients and spectral
  presentations.

So only the parameter part goes beyond the target, and only by this
generalization. The sources above cover it.

## 3. Implemented proof

`cuspidalPairFunctionalEquationReduction` introduces the three hypotheses and the
common data. The local data part, applied to the common data, gives the factor
choice, the archimedean components of `ψ`, and a set `S` with the four inclusions,
`FiniteAdditiveSupport ψ S` and `∀ c, c.IsUnramifiedOutside S`. The first conjunct of
the target is assembled from these and from the parameter part applied to `T`, `T'`,
`Td` and `Td'` at each real and each complex place. For the second conjunct the proof
gives the same `S`. For each `c` it gives `c.IsUnramifiedOutside S` and then applies
the completed equation part to the common data, `S`, its properties, `c`, its
unramified identities and the archimedean data. The archimedean products are written
identically in both statements, so the result has the required type.

## 4. Checks

`lean_check` (environment `bb168ec3-1031-46d9-816b-5c2ed7bbe1a6`) compiles the module
without errors or warnings. Inspection of
`CuspidalPairFunctionalEquationReductionStatement` reports a `Prop` with universe
parameters `u`, `uQ` and the axioms `propext`, `Classical.choice`, `Quot.sound`.

## 5. Remaining obligations

- `CuspidalPairLocalDataStatement`: Worker 4891 is proving it within Task 5493.
- `CuspidalArchimedeanParameterExistenceStatement`: genericity of archimedean
  components of cuspidal representations, the Langlands classification and the
  irreducibility of generic standard modules (target Markdown §8 item 3, first
  bullet). A separate proof task is planned.
- `CuspidalPairCompletedEquationStatement`: the global theory, the finite and
  archimedean local theory, independence of the archimedean factors from the choice
  of parameters, the norm shift, the sign cancellation and the convergence of the
  Euler products (target Markdown §8 items 1–3 and 5–7). A separate proof task is
  planned.

Once the three are proved, applying `cuspidalPairFunctionalEquationReduction` to them
proves the target.

## Sources

| Source ID | Short name | Locators used |
|---|---|---|
| `cogdell-2004-analytic-theory-gln` | Cog04 | p.211 (PDF 214); Thm 3.3 p.215; §3.2 p.217; Thm 4.1 p.219 (PDF 222) |
| `getz-hahn-2024-automorphic-representations` | GH | §11.6 p.308 (PDF 319); Thm 11.7.1 p.309 (PDF 320) |
| `knapp-1994-archimedean-llc` | Knapp | Thm 1 p.400 (PDF 410); Thm 2 p.403 (PDF 413); Thms 4–5 pp.405–406 |
| `jacquet-2009-archimedean-rankin-selberg` | Jac09 | Thm 2.1 p.6; Remark 2.2 pp.7–8 |
