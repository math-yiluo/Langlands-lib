# Naturality of canonical Lie base change

For every `S : AlgebraicGeometry.Scheme.{u}`, with arbitrary universe `u`,
`Langlands.AbelianScheme.lieBaseChangeNaturalityStatements S` proves the
unchanged published proposition
`Langlands.AbelianScheme.LieBaseChangeNaturalityStatements S`. It conjoins
naturality for every actual abelian-scheme homomorphism with the
endomorphism specialization. The theorem has no premise beyond `S`.

The target quantifies arbitrary `T : Scheme.{u}`, `b : T ⟶ S`, abelian
schemes `A,B` over `S`, and an actual homomorphism `f : A ⟶ B`. Given
comparison isomorphisms `ellA,ellB` for the actual Lie modules, it retains
both cotangent `IsIso` hypotheses and both canonical equations from
`LieBaseChangeStatement`. It concludes the equality of module-sheaf maps

```text
(pullback b).map (lieMap f) ≫ ellB.hom =
  ellA.hom ≫ lieMap ((baseChange b).map f).
```

Here `lieMap` and `baseChange` are the published abelian-scheme
constructions. These arrows act on the actual module sheaves, so the
conclusion is not restricted to global sections.

## Implemented proof

`lieBaseChangeNaturality_of_cotangent` first establishes the
all-homomorphism component from the existing abelian cotangent
naturality proposition. Let `k` denote the actual cotangent map
`GroupScheme.cotangentMap (groupHom f)`, `k_T` the cotangent map of the
base-changed homomorphism, and `c_A,c_B` the actual cotangent comparisons.
Applying `dualMap` to the cotangent equation
`b* k ≫ c_A = c_B ≫ k_T` and rewriting `dualMap_comp` gives
`dualMap c_A ≫ dualMap (b* k) = dualMap k_T ≫ dualMap c_B`.

The implementation installs the supplied invertibility of `c_B` and
obtains invertibility of its dual from the actual contravariant
`dualFunctor T`. It postcomposes both sides of the desired Lie square with
`dualMap c_B`. The canonical equation for `ellB`, the dualized cotangent
equation, and the canonical equation for `ellA` reduce this equality to
`dualPullbackComparison_naturality b k`. Cancellation proves the original
square. The other cotangent comparison's invertibility is not needed in
this cancellation, and both original invertibility hypotheses remain
in the unchanged target.

`lieBaseChangeEndomorphismNaturality_of_naturality` applies the same
square with `B = A`, both comparisons equal, and the invertibility and
canonical equation supplied twice. Thus it proves the exact
endomorphism component, applicable in particular to each endomorphism
of an actual order action. `lieBaseChangeNaturalityStatements_of_cotangent`
pairs the two conclusions.

The final theorem imports
`Langlands.AbelianScheme.CotangentBaseChangeNaturalityProof` and supplies
the second, abelian component of the independently proved
`Langlands.cotangentBaseChangeNaturalityStatements S`. It introduces no
cotangent-naturality assumption into the final theorem and does not
duplicate the cotangent proof.

## Provenance and scope

This is an internal derived compatibility proof for the existing actual
module-sheaf maps. Its provenance is `LieFunctor`, `LieBaseChange`, and
the duality and dual-pullback laws in `ModuleDual` and `ModuleDualPullback`;
it introduces no new source transcription. The base schemes and base
morphism are arbitrary in the same arbitrary universe, with no additional
geometric hypothesis. The target and all its imported Lean/Markdown
pairs are unchanged. The argument uses the stated canonical
characterization of any comparison isomorphisms and does not reprove
their existence. Determinant transport remains a separate result.

Worker 339 authored this proof and explanation, reusing Worker 310's
published cotangent naturality theorem by import.
