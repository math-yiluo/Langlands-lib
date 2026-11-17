# Proof of the reduction of the archimedean pair regularity

Author: Worker 3657 (shared draft); checked and submitted by Worker 832.

Module `Langlands.Automorphic.CuspidalArchimedeanPairRegularityReductionProof`
proves

```lean
theorem Langlands.Automorphic.cuspidalArchimedeanPairRegularityReduction :
    CuspidalArchimedeanPairRegularityReductionStatement.{u}
```

The target is the published proposition
`Langlands.Automorphic.CuspidalArchimedeanPairRegularityReductionStatement` of
module `Langlands.Automorphic.CuspidalArchimedeanComponentStatement`. That
module is the sole import here. The target is the implication

```text
ArchimedeanStandardAdmissibleStatement →
  CuspidalArchimedeanStandardIrreducibleStatement.{u} →
  CuspidalArchimedeanStandardGenericStatement.{u} →
  CuspidalArchimedeanStandardUnitarizableStatement.{u} →
  Archimedean.RealUnitaryGenericPairRegularityStatement.{0, 0} →
  Archimedean.ComplexUnitaryGenericPairRegularityStatement.{0, 0} →
  CuspidalArchimedeanPairRegularityStatement.{u}
```

All six hypotheses are propositions taken as arguments. None is proved here,
and the theorem holds whether or not they are true. The proof uses no axiom
beyond `propext`, `Classical.choice` and `Quot.sound`.

## Statements involved

- `CuspidalArchimedeanPairRegularityStatement.{u}` (the conclusion): for a
  number field `F : Type u` with `CompactSpace (AdeleQuotient F)`, actual
  cuspidal realizations `T` of `GL_{r+1}` and `T'` of `GL_{t+1}` with
  `HasUnitaryCentralCharacter`, and standard-module parameters `ds`, `ds'` of
  `T` and `T'` at the same real place (`HasRealPlaceParameter`), the
  denominator of `realPairLFactor ds ds'` does not vanish at any `s` with
  `1 ≤ s.re`. The same holds at a complex place with `HasComplexPlaceParameter`
  and `complexPairLFactor`.
- The four component hypotheses say that the `(𝔤, K)`-module
  `(realStandardRep (r + 1) ds, realStandardLie (r + 1) ds)` of a place
  parameter `ds` of `T` is admissible (for every `n` and `ds`, not only
  parameters), irreducible, generic and, when the central character of `T` is
  unitary, unitarizable. Each hypothesis is the conjunction of a real and a
  complex part.
- `Archimedean.RealUnitaryGenericPairRegularityStatement.{0, 0}` (module
  `Langlands.Representation.Archimedean.UnitaryGenericPairRegularityStatement`)
  is the case `F = ℝ` of Getz–Hahn, Theorem 11.5.2, for carriers in `Type`.
  Given `(𝔤𝔩_n(ℝ), O(n))`- and `(𝔤𝔩_m(ℝ), O(m))`-modules `(ρ, π)` and
  `(ρ', π')` with the properties `IsRealGKModule`, `IsIrreducibleGKModule`,
  `IsAdmissibleGKModule`, `IsRealGenericGKModule`, `IsRealUnitarizableGKModule`
  and standard parameters `ds`, `ds'` (`HasRealStandardParameter`), it gives
  `(realPairLFactor ds ds').denominator s ≠ 0` for `1 ≤ s.re`. The complex
  statement is the same over `ℂ`.

## The proof

Fix `F`, `r`, `t`, `T`, `T'` and the two unitarity hypotheses `hT`, `hT'`.

1. **Real place.** Let `v` be a real place, `ds` and `ds'` parameters of `T`
   and `T'` at `v` (`hds`, `hds'`), and `1 ≤ s.re`. Apply the real local
   statement with `n = r + 1`, `m = t + 1`,
   `V = realStandardKFinite (r + 1) ds`, `W = realStandardKFinite (t + 1) ds'`
   and the actions `realStandardRep`, `realStandardLie`. Its hypotheses for `V`
   are discharged as follows; those for `W` are the same with `t`, `T'`, `ds'`
   and `hT'`.
   - `IsRealGKModule`: `Archimedean.isRealGKModule_realStandardModule (r + 1) ds`
     (module `Langlands.Representation.Archimedean.RealStandardModuleGKModule`).
   - Irreducible, generic and unitarizable: the real conjuncts of the
     irreducibility, genericity and unitarizability hypotheses, at `F`, `r`, `T`
     (and `hT`), applied to `v`, `ds` and `hds`.
   - Admissible: the real conjunct of the admissibility hypothesis at `r + 1`
     and `ds`.
   - `HasRealStandardParameter (r + 1) _ _ ds`: the rank condition
     `realRank ds = r + 1` is the first conjunct `hds.1` of the place parameter.
     The map is `LinearMap.id`, injective by `Function.injective_id`. Its
     intertwining property is `Archimedean.isRealStandardIntertwiner_id (r + 1) ds`
     (same module). The definition `IsRealStandardIntertwiner` is, by its
     docstring, exactly the last two clauses of `HasRealStandardParameter`, so
     the anonymous constructor accepts it by definitional unfolding.
2. **Complex place.** The same, with the complex conjuncts of the four
   component hypotheses, the complex local statement,
   `Archimedean.isComplexGKModule_complexStandardModule` and
   `Archimedean.isComplexStandardIntertwining_id` (module
   `Langlands.Representation.Archimedean.PrincipalSeriesGKModule`), and the rank
   condition `ds.length = r + 1` from `hds.1`.

The carriers `realStandardKFinite (r + 1) ds` and
`complexStandardKFinite (r + 1) ds` are submodules of `GL_{r+1}(ℝ) → ℂ` and
`GL_{r+1}(ℂ) → ℂ`, so they live in `Type`. This is why the local statements
enter at universes `0, 0`. The place parameter and the local predicates use
the same `realStandardKFinite`, which is an abbreviation for
`Archimedean.kFiniteFunctions (realStandardModule n ds) (unitaryCompact ℝ n)`,
so no transport between carriers is needed.

## Provenance

This is step 5 ("Reduction") of "Why the statements are true" in the statement
Markdown (`Langlands/Automorphic/CuspidalArchimedeanComponentStatement.md`). It
follows the route in the contract of Task 7000
(`f273c02c-55ab-425f-b5d0-c51b0ea23a34`). The mathematics is the archimedean
step on p.309 (PDF p.320) of J. R. Getz and H. Hahn (2024), *An introduction to
automorphic representations*. The registered file is
`getz-hahn-2024-automorphic-representations` (SHA256
`a125cf9c0f445972cbbd3552b4fb9905ca948108a05880f90eaa43558d09a507`). For
cuspidal `π`, `π'` trivial on `A_{GL_n}` and `A_{GL_m}`, the text says
"`L(s, πv × π′v)` converges absolutely for `Re(s) ≥ 1` for all `v` by
Theorem 11.5.2". Theorem 11.5.2, p.305 (PDF p.316), reads "If `π` and `π′`
are unitary, then `L(s, π × π′)` is holomorphic and nonzero for `Re(s) ≥ 1`".
There `π` and `π′` are, by the standing assumption of §11.5 on p.304 (PDF
p.315), "irreducible admissible generic representations". So the local
statement needs its components to be irreducible, admissible, generic and
unitary. For the archimedean local components of a cuspidal representation,
§11.4, displays (11.14)–(11.17), pp.300–302 (PDF pp.311–313), gives the tensor
factorization with irreducible unitary local factors `V_v` and fixes their
Whittaker models `W(π_v, ψ_v)`. Here the four properties are the four
component hypotheses. Two choices are
derived content and not in the source. The local component is the standard
module of the place parameter, and the identity map witnesses the standard
parameter of that module.

## Scope

The theorem proves none of its six hypotheses. A proof of the entry point
`CuspidalArchimedeanPairRegularityStatement.{u}` follows by applying
`cuspidalArchimedeanPairRegularityReduction` to proofs of the six hypotheses.
That application is the entry-point proof child, Task 7005
(`1a9d552f-6429-45fa-afcd-7f2806c4312f`). Proofs of the hypotheses are assigned to these
tasks:

- admissibility: Task 6999 (`ae8500ea-b349-43af-a409-c33bbccb5317`);
- irreducibility: Task 7004 (`c77dc5a4-25c6-4498-bc30-ecfbcf470106`);
- genericity: Task 7003 (`d785ecd7-e7cc-4174-9da9-68b37467f224`);
- unitarizability: Task 7000, the other target of this task;
- the archimedean case of Getz–Hahn, Theorem 11.5.2: Tasks 6818, 6819
  and 6820.
