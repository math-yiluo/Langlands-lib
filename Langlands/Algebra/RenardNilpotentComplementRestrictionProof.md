# Renard C.I: restriction to a complement and the dimension bound

Worker 308 proves
`Langlands.Renard.nilpotentComplementRestriction.{u}` with exactly the closed
published proposition
`Langlands.Renard.NilpotentComplementRestrictionStatement.{u}` as its type.
The statement and its imported constructions are used unchanged.

The source is David Renard, *Représentations des groupes réductifs p-adiques*,
French edition dated 9 July 2026, Appendix C.I, printed p.275 / one-based
PDF281, the two consecutive assertions immediately after `R · W = V`.
The registered original is
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`,
at
`/home/taskhub/central-library/Renard--Representations des groupes reductifs p-adiques (2026 version)--2026.pdf`.
Worker 308 read PDF281–282 and visually checked PDF281. The supplementary
2010-edition corrections, registered as `renard-2010-corrections-complements`,
SHA256 `fdf3c88716c294c451c1f6fad67f6b99c95dae670aae0b8ad191ab0a96e69863`,
were read on PDF18–19. Their C.I entries concern older numerical inequalities
and exponents; the 2026 original governs the assertions proved here.

## Actual objects and hypotheses

For every finite-dimensional complex vector space `V : Type u`, every
natural tuple length `l`, and every pairwise commuting, individually
nilpotent tuple `a : Fin l → Module.End ℂ V`, write
`R = NilpotentFiltration.generatedAlgebra a` and
`I = NilpotentFiltration.generatorIdeal a`. The imported construction
`Langlands.Algebra.RenardNilpotentIdealFiltration` makes `R` the actual
unital adjoin of the original tuple, `I` its tuple-generated ideal, and
`idealPowerSubspace a 1` the original-action subspace `I V`.
Scalars and the identity already belong to the unital adjoin and do not
add counted generators.

The theorem uses an arbitrary complex subspace `W` satisfying
`IsCompl (NilpotentFiltration.idealPowerSubspace a 1) W`.
The restriction map sends an original endomorphism in `R` to its
domain restriction in `W →ₗ[ℂ] V`. The complement is not assumed
invariant, and the codomain remains `V`.

## Implemented proof

First, `NilpotentFiltration.generatedAlgebra_isMulCommutative` derives
commutativity of the actual algebra from tuple commutation. The proof
imports Worker 88's published
`Langlands.Renard.nilpotentComplementGeneration` from
`Langlands.Algebra.RenardNilpotentComplementGenerationProof` and uses
its second conjunct, `Submodule.span R (W : Set V) = ⊤`, with the
same tuple, nilpotence hypotheses and complement. Generation is thereby
proved from the target's hypotheses rather than added as a premise.
The imported generation proof uses Nakayama on this same actual algebra,
ideal and action after deriving nilradical containment.

The next step converts this algebra span to the complex span of the
original evaluation vectors:

```text
span_ℂ {r(w) | r ∈ R, w ∈ W} = V.
```

The set of these vectors is identified with `(Set.univ : Set R) • W`.
The scalar-tower identity `Submodule.span_smul_of_span_eq_top`, with
`Submodule.span_univ`, identifies its complex span with the restriction
to complex scalars of `span_R W`. Rewriting by the generation equality
and `Submodule.restrictScalars_top` gives the required full complex span.
Commutativity in `R` is also passed to commutation of the underlying
original endomorphisms by applying `Subtype.val` to `mul_comm`.

The final two steps specialize Worker 307's published helpers from
`Langlands.Algebra.CommutingDimensionHelpers`.
`Langlands.CommutingDimension.restriction_injective` proves injectivity:
an element killing `W` kills every `r(w)` by commutativity, hence kills
their complex span, which is all of `V`. The helper implements this
argument by proving that the kernel of the linear restriction map is
zero. That linear map has exactly the restriction function in the target.

`Langlands.CommutingDimension.dimension_le_generating_subspace` applies
the dimension inequality for this injection into `W →ₗ[ℂ] V`.
The dimension of this linear-map space is
`Module.finrank ℂ W * Module.finrank ℂ V`, so it yields the second
conjunct with the target's factor order. Both `R`, as a subspace of
the endomorphism space, and `W`, as a subspace of `V`, are
finite-dimensional. The proof imports these named published helpers
without copying their proofs.

All carrier universes, natural tuple lengths, zero spaces, empty tuples,
zero entries, repetitions and redundant generators remain within the exact
statement. No positivity, nontriviality, invariance, maximality, basis,
supplied generation, supplied vanishing, injectivity or sharp dimension
bound is assumed.

This pair proves only the stated restriction injection and complement
dimension bound. Maximum attainment, the sharp filtration endpoint,
complement generation, algebra splitting, restriction to `V_1`,
monotonicity, floor recurrence, numerical base cases, carrier transport
and other source obligations retain their separate owners.
