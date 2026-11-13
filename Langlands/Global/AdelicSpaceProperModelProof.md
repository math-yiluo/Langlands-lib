# Proper arithmetic models of proper field morphisms of algebraic spaces

Author: Worker 157. The imported arithmetic reduction is by Worker 129 and
Worker 157; its paired Markdown records the reused arguments of Workers 208
and 105.

`Langlands.Global.adelicSpaceProperModel` proves the published proposition
`Langlands.Global.AdelicSpaceProperModelStatement.{u}` in every common
universe `u`, with no additional hypotheses.

Given independently supplied separated finite-type models over rings of
`S`- and `U`-integers, identifications of their generic fibres with `Y` and
`W`, and a proper field morphism `g : Y ⟶ W`, the result supplies separated
finite-type models `M` and `N` over a common ring of `T`-integers,
generic-fibre isomorphisms `eT` and `fT`, and a proper morphism
`gm : M ⟶ N` satisfying the prescribed square
`baseChangeMap (…) gm ≫ fT.hom = eT.hom ≫ g`.

The function-field case retains finite constants, the compatible
rational-function-field action, and the nonemptiness conditions on `S`,
`U`, and `T`. The number-field case allows empty finite sets of finite
places. These are exactly the two conjuncts of
[`AdelicSpaceProperModelStatement`](AdelicSpaceProperInputsStatement.md);
the result imposes no containment relation on the final `T` and no
representability hypothesis on the proper field morphism.

## Implemented proof

The proof applies
`AdelicSpaceProperModelReduction.adelicSpaceProperModel_of_descent` to
two published proof terms in the same universe `u`:

- `spaceLimitMorphismDescent` from `SpaceLimitMorphismDescentProof`
  supplies `SpaceLimitMorphismDescent.{u}`.
- The third conjunct `(spaceLimitPropertyDescent.{u}).2.2.1`, from
  `SpaceLimitPropertyDescentProof`, supplies
  `SpaceLimitPropertyDescends.{u} (fun f => IsProperMorphism f)`.

The imported reduction first base changes the supplied models to the union
of their finite sets, uses morphism descent to spread the conjugated field
arrow, and then uses properness descent to obtain a proper arrow at a
further stage. Its comparison isomorphisms preserve the original field
arrow in the exact square. Both external premises of that reduction are
therefore discharged, and the entry theorem has exactly the unchanged
published target as its type.

## Provenance and scope

This module is an internal composition of published theorems. The
[reduction's documentation](AdelicSpaceProperModelReduction.md) explains
the geometric and arithmetic construction. The
[target's documentation](AdelicSpaceProperInputsStatement.md) records its
derivation from Conrad, *Weil and Grothendieck approaches to adelic
points*, December 31, 2011, printed pp.5–6, 11, 13, and 17.
The theorem proves proper arithmetic model replacement in both
characteristics. Finite-level topological properness and the final adelic
proper-map theorem are separate statements.
