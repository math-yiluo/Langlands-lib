# Reductions of the Sharp class formula and of cuspidal-series retention

Module `Langlands.Representation.Aubert.General.RationalSharpReductionStatements`.
Author: Worker 29, with Worker 3640 (who chose this block for the general
Aubert program, Task 3640). The input sets are the ones used by the
conditional assemblies in the shared drafts of the proof tasks for the two
conclusions. Workers 751 and 4217 wrote the class-formula assembly
(`RationalSharpClassFormulaInputs`, Task 4217,
`13e2abdc-2be7-4191-b74b-9eae99a56fcc`). Worker 4221 wrote the
cuspidal-series assembly (`RationalSharpCuspidalSeriesReduction`, Task 4221,
`6316db5a-5618-43bb-a920-eadd3a912b88`).

The module declares two propositions in
`Langlands.Aubert.General.RationalPointFamily`. Each is an implication between
whole published propositions, at the same universes `u` and `v`. Neither is
proved here. Neither proves its conclusion, and neither adds a premise to it:
each conclusion is the unchanged published target.

## `RationalSharpClassFormulaReductionStatement`

```
RationalCorrectedGradedVanishingStatement.{u, v} →
  RationalSupportCategoryInductionJacquetStatement.{u, v} →
    RationalSupportCategoryExactnessDetectionStatement.{u, v} →
      RationalSupportCategoryJacquetVanishingStatement.{u, v} →
        RationalSharpClassFormulaStatement.{u, v}
```

The conclusion is the signed class formula of Aubert (1995), Corollaire
3.9 (a), printed p. 2189: `(-1)^{|I|} [E#] = D_G([E])`. It is extended, as the
1996 erratum (printed p. 4690) requires, to finite-length members `E` of the
actual support category `Alg({I})` whose `E#` has finite length. Here `E#` is
the actual terminal cokernel of the corrected smooth complex, and `D_G` is
the unadjusted operator built from every finite-length proof `hfl`, which
stays quantified inside the target. `RationalSharpConsequenceTargets.md`
gives its full reading.

The four inputs are the following published propositions about the same
actual rational-point families.

| Input | Module | Content |
| --- | --- | --- |
| `RationalCorrectedGradedVanishingStatement` | `RationalCorrectedFiltrationTargets` | A nonzero graded piece of the support filtration of `r_I(E_J)` at a length-ordered Weyl element `w` forces `w L_I w⁻¹` to be a standard Levi `L_K` with `K ⊆ J` (erratum, pp. 4688–4689, with the Ban–Jantzen correction) |
| `RationalSupportCategoryInductionJacquetStatement` | `RationalSupportCategoryTargets` | The actual support category is stable under normalized induction after normalized Jacquet restriction along every standard Levi |
| `RationalSupportCategoryExactnessDetectionStatement` | `RationalSupportCategoryTargets` | Exactness at a member of the actual support category is detected by the normalized Jacquet modules along all associated standard Levis (erratum, p. 4687) |
| `RationalSupportCategoryJacquetVanishingStatement` | `RationalSupportCategoryTargets` | If no standard Levi inside `L_K` is associated to `L_I`, the normalized Jacquet module along `L_K` of every member of the support category is zero |

Each input is a whole proposition, quantified over every nonarchimedean local
field and connected reductive group with its own displayed premises. These
are not per-instance premises of the class formula. Exactness detection
stays an explicit input. The corrected exactness before the terminal degree
also needs the rational Bruhat decomposition and the surviving graded
transitions. Both are published theorems
(`Langlands.GroupScheme.rationalBruhat` and
`rationalCorrectedGradedTransitionStatement`), so neither is an input.

## `RationalSharpCuspidalSeriesReductionStatement`

```
RationalSharpSupportRetentionStatement.{u, v} →
  RationalSharpIrreducibleStatement.{u, v} →
    RationalSharpCuspidalSeriesStatement.{u, v}
```

The conclusion is the derived step in the proof of Aubert (1995),
Corollaire 3.9 (c), printed p. 2189. If `E` is in the actual cuspidal
series `𝔈(I)`, then `E#` is in `𝔈(I')` for some `I'` and some actual point
`n`, with `rootAssociation i ν hN hZ I I' n` and `L_{I'} = n L_I n⁻¹`. The
step is needed to apply `#` a second time; the erratum describes
`Alg({I})` and `E#` on pp. 4687 and 4690. The two inputs are sibling targets
in `RationalSharpConsequenceTargets`:

- `RationalSharpSupportRetentionStatement`: `E ∈ Alg({I})` implies
  `E# ∈ Alg({I})`;
- `RationalSharpIrreducibleStatement`: `E ∈ 𝔈(I)` implies that `E#` is
  irreducible (Corollaire 3.9 (b)).

The inputs and conclusion fix the same actual group, families and universes,
so `E`, `E#` and the Levi representations lie in one category.

## Scope

All four inputs, both sibling inputs and both conclusions are the published
propositions themselves, quantified over the same actual setting:

- every nonarchimedean local field, including positive characteristic;
- every connected reductive group, with its actual maximal split torus,
  generic cocharacter and actual simple relative roots, including the empty
  set;
- the canonical `pointTopology` on rational points;
- field universe `u` and representation carriers in `max (u + 1) v`, with
  `u` and `v` independent.

Neither proposition restricts to split, quasisplit or characteristic-zero
groups, or to `GL`.

## Provenance

These are derived, internal statements. They make no new claim from the
literature. Their mathematical content is that of the cited Corollaire 3.9 and
erratum, through the published targets. Aubert's Proposition 3.2 and its
original application are not used. The route recorded by each implication
is the following.

- Class formula. Corrected exactness before the terminal degree comes from
  `rationalIsExactBeforeTerminal_of_inputs`. Below `|I|` labels, the Jacquet
  modules vanish by the vanishing input, because association preserves the
  number of labels. The finite exact Euler identity then gives the signed
  class of `E#`.
- Cuspidal series. Use `E#` as its own irreducible subquotient, together with
  support retention and the published generic reduction
  `sharpCuspidalSeries_of_irreducible_supportRetention`.

The proofs belong to separate `lean.proof@1` successor tasks. Statement review
does not establish them.
