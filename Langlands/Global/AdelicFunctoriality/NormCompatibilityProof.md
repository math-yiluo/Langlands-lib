# Unconditional local/global compatibility of the actual adelic norm

`Langlands.Global.AdelicFunctoriality.normCompatibility` proves exactly
`NormCompatibility.{u, v}` from `NormStatement`. The two universes remain
independent. Both conjuncts quantify arbitrary fields `K : Type u` and
`L : Type v` with their `NumberField` instances and the given `Algebra K L`.
There is no additional arithmetic hypothesis.

The first conjunct is `CompletedTensorComparison`: the canonical
`finiteTensorMap` and `infiniteTensorMap` are bijective at every actual
finite and infinite place of `K`. The factors are the actual completions
of `L` at places above the chosen place, and the source is the completed
scalar extension `K_p ⊗[K] L`.

The second conjunct is `PrincipalNormCompatibility`. For every `x : L`,
including zero, the constructed `adeleNorm` sends the diagonal adele of
`x` to the diagonal adele of `Algebra.norm K x`. This is equality in the
full adele ring of `K` for the existing product of local determinant norms.

The Lean proof is an assembly of two independently published theorems.
It supplies `completedTensorComparison.{u, v}` as the first conjunct.
The first projection of `normAssembly.{u, v}` has type
`CompletedTensorComparison.{u, v} → PrincipalNormCompatibility.{u, v}`;
applying it to the same completed tensor comparison gives the second
conjunct. Thus the compatibility premise of that implication is fully
discharged. All constructions and the target proposition are imported
unchanged.

The imported comparison proof obtains the finite-place bijections from
the completed local-degree bounds and the finite comparison reduction;
its infinite-place part uses the established `infiniteTensorMap_bijective`.
The imported norm reduction compares determinants under scalar extension
and finite products, then assembles the coordinate identities into the
principal-adele identity. This module adds only the conjunction proof.
The separate quotient-descent implication in `normAssembly` is not used:
the present theorem constructs no named idele-class norm and asserts no
reciprocity result.

This conjunction is the project's internal organization of the classical
completed tensor decomposition and local/global norm formula. Their
original mathematical source is Andre Weil, *Basic Number Theory*, second
edition (1973), Chapter III section 4, Theorem 4 and Corollary 3, printed
pp. 56–58 (PDF pp. 73–75). The coordinate formula for the adelic norm is
Chapter IV section 1, Corollary 3, printed p. 64 (PDF p. 81). These pages
were read. Registered source: `weil-1973-basic-number-theory`, SHA256
`32fff78f8ccc5d6378907941e26746c34e20fc3adf5096508844cfe8a301e33b`.
The implemented proof reuses the published Lean results rather than
repeating the original arithmetic arguments.
