# A polynomial annihilating the Casimir operator on an irreducible realization

Module: `Langlands.Automorphic.CuspidalAdmissible.CasimirAnnihilator`.
Provenance: internal. This is the first algebraic step of the proof of joint admissibility
of unitary cuspidal realizations (an input of the cuspidal contragredient existence
theorem): the classical fact that the Casimir element acts on an irreducible
`(𝔤, K)`-type module through a finite-dimensional quotient of `ℂ[Ω]`, in the weak form
"one nonzero polynomial in `Ω` vanishes identically".

## Adjoint invariance of the trace-form Casimir (namespace `Langlands.Global.ArchimedeanGL`)

- `matrixTraceForm_realLieConjugation g X Y`: the real trace form
  `matrixTraceForm K n X Y` is invariant under the archimedean adjoint action
  `realLieConjugation K n g`. In matrix coordinates the action is `A ↦ G A G⁻¹`, and
  `tr (G A G⁻¹ G B G⁻¹) = tr (A B)` by cyclicity of the trace.
- `realEnvelopingGenerator_realLieConjugation`: the real enveloping generator intertwines
  `realLieConjugation` with `envelopingConjugation` (definitions unfold to
  `envelopingConjugation_generator` and `complexLieConjugation_tmul`).
- `envelopingConjugation_matrixCasimir g`: `envelopingConjugation K n g` fixes
  `matrixCasimir K n`. Proof: write the Casimir as `∑ X_i X_i^∨` for a basis `X_i` and its
  trace-dual basis (`matrixCasimir_eq_sum`). Conjugating maps the basis `b` to the basis
  `b' = g · b`, and by invariance of the trace form the dual basis of `b'` is the conjugate
  of the dual basis of `b` (`LinearMap.BilinForm.dualBasis_eq_iff`). The expression for
  `b'` is again the Casimir.

## The Casimir operator of a realization (namespace `Langlands.Automorphic.CuspidalAdmissible`)

For an actual operator realization `S : OperatorRealization F n`:

- `casimirOperator S := S.envelopingAction (matrixCasimir F n)`.
- `exists_casimir_annihilator_vector S f`: every `f` is killed by a nonzero polynomial in
  the Casimir operator. The orbit span of `f` under the enveloping center is
  finite-dimensional (`S.centerRepresentation_isFiniteVector`) and Casimir-stable
  (the Casimir is the image of `matrixCentralCasimir`), so `exists_aeval_apply_eq_zero`
  applies.
- The Casimir operator commutes with finite translations
  (`finiteRepresentation_casimirOperator`, from `finiteRepresentation_envelopingAction`),
  with compact translations (`compactRepresentation_casimirOperator`, from
  `compactRepresentation_envelopingAction` and the adjoint invariance above), and with
  the whole differential action (`envelopingAction_casimirOperator`, because the Casimir is
  central, `matrixCasimir_mem_center`).
- `exists_ne_zero S hS`: an irreducible realization has a nonzero vector (its lattice of
  subrepresentations is nontrivial).
- `exists_casimir_annihilator S hS` (**Casimir annihilator**): if `S` is irreducible, some
  nonzero `q` satisfies `q(Ω) f = 0` for every `f`. Proof: pick `f₀ ≠ 0` and `q` with
  `q(Ω) f₀ = 0`. The kernel of `q(Ω)` is stable under the finite, compact and enveloping
  actions (each commutes with `Ω`, hence with `q(Ω)` by `aeval_apply_commute`), so by
  `S.representation_mem_of_stable` it is a subrepresentation. It contains `f₀ ≠ 0`, so it
  is not `⊥`; by irreducibility (`IsSimpleOrder`) it is everything.
