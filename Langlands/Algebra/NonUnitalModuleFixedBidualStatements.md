# Fixed-bidual comparison and canonical evaluation

These internal statements isolate the fixed-space comparison used in the proof
of Renard's I.5.1 reflexivity proposition, printed p.26 / PDF32 of the French
edition dated 9 July 2026. The registered source is
`renard-2026-representations-groupes-reductifs-padiques`, SHA-256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The registered `renard-2010-corrections-complements`, SHA-256
`fdf3c88716c294c451c1f6fad67f6b99c95dae670aae0b8ad191ab0a96e69863`,
PDF2, corrects the converse proof on printed 2010 p.29 by passing through the
ordinary bidual of each fixed space. The 2026 text incorporates this argument.
These comparison names are internal infrastructure, rather than separately named
assertions in the source.

The original algebra A is a possibly nonunital complex algebra satisfying the
published scalar compatibility and idempotented-ring hypotheses. M retains its
original additive A-action and nondegeneracy witness. Algebra and module carrier
universes are independent. There is no separately supplied complex structure
on M, admissibility premise, or finite-dimensionality hypothesis.

`InverseComparisons hA hM` states both inverse identities of the concrete
maps from `NonUnitalModuleFixedBidualMaps`, for every original idempotent e.
Writing T for `toOrdinaryBidual` and S for `fromOrdinaryBidual`, the identities
are S(T(Phi)) = Phi on the actual fixed part of the actual nondegenerate bidual,
and T(S(Psi)) = Psi on the ordinary complex algebraic bidual of `FixedPart e M`.
The actual bidual has exactly the original A-action `bidualAction`, obtained by
the specified double-opposite transport. Both fixed-space structures are the
published canonical `NonUnitalModuleCorner.complexModule` structures.

`EvaluationCompatibility hA hM` states that S sends the ordinary canonical
evaluation of every x in `FixedPart e M` to the published actual evaluation of
its original vector x.val. The equality is of entire elements of the actual
nondegenerate bidual after the fixed-subgroup inclusion. Its left side uses
exactly `Module.Dual.eval` for the canonical fixed-space coefficients; its
right side uses exactly `NonUnitalModuleDual.evaluation`. Thus this assertion
specifies the canonical evaluation square, rather than an unspecified abstract
equivalence of vector spaces.

`FixedBidualComparisons` universally quantifies all original algebra and module
parameters and conjoins both assertions. Complete unapplied type checks retain
the independent universes and original instance interface. These are
Prop-valued statement definitions only. Their proofs, the finite-dimensional
criterion, and the I.5.1 admissibility and simplicity results remain separate
obligations.
