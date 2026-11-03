# A proper `GL_N` action with solvable point stabilizers

Worker 148 supplies the exact proof-target module. Worker 1399 constructed the
closed flag locus, its scheme action, properness, the fixed-point reduction and
the assembly. Worker 135 proved the full-flag linear-algebra solvability result
used by that construction.

The theorem `Langlands.GroupScheme.generalLinearSolvableStabilizer_proof` has
exactly the type
`Langlands.GroupScheme.GeneralLinearSolvableStabilizerStatement.{u}`. It applies
at every universe `u`, to every algebraically closed field `k : Type u` and every
natural number `N`, including `N = 0`. It asserts the existence of a proper
nonempty scheme over `Spec k` with an actual
`SchemeAction (GeneralLinear.groupScheme (Fin N) (CommRingCat.of k))`. Every
closed subgroup fixing a rational point under the Library's all-test
`SchemeAction.IsFixed` satisfies `IsSolvableGroupScheme`.

The Lean proof is the direct application
`generalLinearSolvableStabilizer.{u}` from
`Langlands.GroupScheme.Absolute.GeneralLinearSolvableStabilizerProof`.
No hypothesis is added and the statement definition is unchanged. This module
is derived from that Library theorem; it introduces no separate construction.

The reused theorem constructs a closed stable locus in one quotient
Grassmannian. The stability equations define a closed subscheme, and the
natural matrix actions on affine points yield an actual scheme action.
Properness follows from the Grassmannian's closed projective embedding;
a standard stable point proves nonemptiness. Over the algebraic closure, a
closed subgroup fixing a rational point acts faithfully on the vector space
and preserves the full flag extracted from the corresponding stable point.
The full-flag solvability theorem then proves solvability of this abstract
group of geometric points, which is precisely `IsSolvableGroupScheme`.
This route covers `N = 0` and uses no Borel conjugacy. The construction uses the
field-valued full-flag extraction; it does not require an identification with
the flag functor over arbitrary rings.
