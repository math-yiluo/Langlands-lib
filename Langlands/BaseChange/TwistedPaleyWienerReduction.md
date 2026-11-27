# Reduction of the twisted trace Paley–Wiener theorem to Levi inputs

The module `Langlands.BaseChange.TwistedPaleyWienerReduction` (namespace
`Langlands.BaseChange.TwistedLeviPaleyWiener`) proves

```lean
theorem twistedTracePaleyWiener_of_inputs
    (hCT : TwistedLeviInductionTransferStatement.{u, v, z})
    (hJ : TwistedLeviJacquetDescentStatement.{u, v, z})
    (hD : TwistedLeviDiscretePaleyWienerStatement.{u, v, z})
    (hA5 : TwistedLeviGoodRestrictionStatement.{u, v, z})
    (hA7 : TwistedLeviInducedSpanStatement.{u, v, z})
    (hA8 : TwistedLeviTraceGoodStatement.{u, v, z}) :
    TwistedTracePaleyWienerStatement.{u, v, z}
```

for the six propositions of `Langlands.BaseChange.TwistedLeviPaleyWienerStatements`,
with all three universes free. `TwistedTracePaleyWienerOfLeviInputsStatement`
is the implication from their conjunction `TwistedLeviPaleyWienerInputsStatement`
to the target, and `twistedTracePaleyWienerOfLeviInputs` proves it. The module
does not prove the six inputs.

## Changing the measure

`isCompactlyDominatedFunctional_congr_measure`,
`isTwistedTraceFunctional_congr_measure`, `twistedDistribution_congr_measure`
and `isLeviSigmaInducedRegularFunctional_congr_measure` transport the
predicates along an equality of measures. Each is `subst` followed by `rfl`;
the instance arguments are propositions.

## The theorem on every Levi product

`levi_isTwistedTraceFunctional_of_inputs` fixes the data of the target, a
family `μs` of Haar measures on all Levi products `C.Levi E` (`C : BlockShape n`)
and proves that every compactly dominated regular functional on a Levi product
is a twisted trace functional. It applies
`PaleyWienerAssembly.exists_eq_eval_of_good_of_discrete` to the following
system:

- indices: block shapes of `n`; the Levis of `B` are `ProperRefinement E B`,
  with target `C`; the relation `n - C.length < n - B.length` is well founded
  (it is the inverse image of `<` on `ℕ`) and holds for proper refinements
  because a block shape of `n` has at most `n` blocks (`BlockShape.length_le`);
- test spaces `SchwartzBruhat (B.Levi E)`, irreducible distributions
  `twistedSpectrum (μs B) (leviAut σ B)`, good forms the compactly dominated
  regular functionals;
- `CT B C` chosen by the induction input `hCT`, and `L B`, `c B` chosen by the
  descent input `hJ` applied to these `CT B`.

The assembly hypotheses are checked as follows. Each generator
`θ' ∘ CT B C` of the abstract `inducedSpan` is, by the transfer property and
the admissibility given by `hA7`, the twisted character of an actual proper
induction, so it lies in `leviProperInducedSpan` and, by `hA7`, in the span of
the irreducible twisted characters (`hA7` of the assembly). Conversely each
generator of `leviProperInducedSpan` is `θ' ∘ CT B C` for the inducing
twisted character `θ'`, so the two spans coincide. Hence the discrete input
`hD` gives the discrete case `hD` of the assembly, and the descent identity
of `hJ` on `leviProperInducedSpan` gives `hA3`; `hJ` also gives `hA6`, and
`hA5`, `hA8` are the restriction and trace-form inputs.
`isTwistedTraceFunctional_iff` translates between `IsTwistedTraceFunctional`
and agreement with an evaluation on `twistedSpectrum`.

## Transport to `GL_n(E)`

`exists_levi_equiv_generalLinear` provides a block shape `T` of `n` and a
topological group isomorphism `e : T.Levi E ≃ₜ* GL_n(E)` equal to the
block-diagonal embedding: the one-block shape `oneBlock n` with
`singleBlockLeviEquivContinuous` when `n > 0`, and the empty shape, whose Levi
product and `GL_0(E)` are trivial groups, when `n = 0`. Then
`levi_equiv_leviAut` and `levi_equiv_symm_entrywiseAut` say that `e`
intertwines `leviAut σ T` with `entrywiseAut σ n`, and `relParabolicEquiv`
identifies `relParabolic E T C` with `C.parabolic E` through `e`.

`pushforward_twistedDistribution_comp` and `pushforward_twistedDistribution`
compare twisted characters across `e`: if `μ₁.map e = μ`, the pushforward
along `e` of the twisted character of `π ∘ e` (computed with `μ₁`) is the
twisted character of `π` (computed with `μ`). They follow from the Library's
change of variables `twistedDistribution_comp_equiv` and, for the second
form, `twistedDistribution_eq_of_equivariant`.

In `twistedTracePaleyWiener_of_inputs`, let `μ₁ = μ.map e.symm` (a Haar
measure with `μ₁.map e = μ`), let `μs` be `Measure.haar` except `μs T = μ₁`
(`Function.update`), and let `Φ₁ = Φ ∘ e_*`, where `e_*` is the pushforward of
distributions.

- Compact domination of `Φ₁`: for the compact open subgroup `J` of `Φ`, use
  its preimage under `e`. An irreducible admissible `π₁` of `M_T` without
  fixed vectors under it gives `π₁ ∘ e⁻¹` on `GL_n(E)` without `J`-fixed
  vectors (`fixedVectors_comp_eq_map`), with the same twisting operator, and
  `Φ₁` of its twisted character is `Φ` of the twisted character of
  `π₁ ∘ e⁻¹`, which is zero.
- Regularity of `Φ₁`: for a refinement `C` of `T` (every block shape), the
  Library's `Induction.precomposeSmoothInducedGroupEquiv` identifies the
  induction from `relParabolic E T C` with the induction from `C.parabolic E`
  pulled back along `e`. It carries `TwistedPaleyWiener.inducedSigmaIntertwiner`
  to `relInducedSigmaIntertwiner`, because
  `(entrywiseAut σ n)⁻¹ (e x) = e ((leviAut σ T)⁻¹ x)`. Admissibility transfers
  through this equivalence and `isAdmissible_comp_continuousMulEquiv_iff`, so
  the Laurent expansion given by `IsSigmaInducedRegularFunctional` for
  `GL_n(E)`, with the same finite set and coefficients, is one for `Φ₁`.
- The theorem on `M_T` (with the measure changed from `μs T` to `μ₁`) gives a
  test `φ₁` on `M_T`. The test `φ₁ ∘ e⁻¹` on `GL_n(E)` works: for an
  irreducible admissible `π` and `A : π ≅ π ∘ σ`, the pair `(π ∘ e, A)` is an
  irreducible admissible σ-pair of `M_T`, its twisted character pushes forward
  to that of `(π, A)`, and pulling `φ₁ ∘ e⁻¹` back along `e` gives `φ₁`.

The proof uses the propositional axioms only (`propext`, `Classical.choice`,
`Quot.sound`) and covers rank zero, the trivial twist and every Haar measure,
as the target does.
