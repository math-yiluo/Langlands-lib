# Colimit preservation by actual cokernels of compatible local module maps

The theorem

```lean
Langlands.Algebra.localCokernelColimitPreservation.{uI, uA, uB, uE, uF, uR, uS, uM, uN} :
  Langlands.Algebra.LocalCokernelColimitPreservationStatement.{uI, uA, uB, uE, uF, uR, uS, uM, uN}
```

proves the published proposition at nine independent universes, in the displayed
order. It concerns compatible local module systems `E` and `F` over exactly one
local algebra system `D`, an ambient linear map `f : M →ₗ[S] N`, and a compatible
map `φ : LocalModuleSystem.CompatibleMap E F f`.

Assuming `Function.Surjective E.moduleColimitMap` and
`Function.Bijective F.moduleColimitMap`, it proves
`Function.Bijective φ.cokernelSystem.moduleColimitMap`. These are the actual
additive direct-limit comparisons. The cokernel system has components
`F.obj i ⧸ LinearMap.range (φ.component i)` and target
`N ⧸ LinearMap.range f`, with the published induced transitions and cocone.
There are no additional hypotheses on the ring colimit, approximation,
flatness or finite presentation.

## Implemented proof

The proof introduces every universally quantified parameter and instance of
`LocalCokernelColimitPreservationStatement`, followed by its hypotheses `hE` and
`hF`. The remaining goal is precisely the conclusion of the published helper

```lean
LocalModuleSystem.CompatibleMap.cokernelSystem_moduleColimitMap_bijective
```

at `φ`. The proof closes by the application
`φ.cokernelSystem_moduleColimitMap_bijective hE hF`. The helper's representative
argument is reused through its import from
`Langlands.Algebra.LocalCompatibleMapApproximation`.

When both input comparisons are bijective, the source hypothesis is supplied
by `hE.2`, the surjectivity projection of
`hE : Function.Bijective E.moduleColimitMap`; the target hypothesis is used
unchanged.

## Provenance and scope

This is an internal derived result packaging an already published helper as a
proof of the published proposition. The proposition is imported from
`Langlands.Algebra.LocalApproximationCokernelColimitStatement`. Its Markdown
explains how cokernel colimit preservation supports the final step of the
proof of Stacks Project tag 046Y. The present theorem proves that colimit
preservation claim; it does not establish the whole of 046Y or a flatness
theorem.
