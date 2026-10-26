# Actual cokernels of compatible local module maps

This module constructs the concrete range-quotient diagram of a
`LocalModuleSystem.CompatibleMap E F f` over the single supplied
`LocalAlgebraSystem D`. It also gives its canonical quotient maps and the
value of its actual additive comparison on component representatives.

## Source and provenance

The motivating source is the final proof paragraph of the Stacks Project,
Lemma 10.128.4 (tag [046Y](https://stacks.math.columbia.edu/tag/046Y)).
There the component maps eventually become injective and their cokernels
become flat over the component base rings. The proof then concludes the
target assertion. The registered original is
`stacks-algebra-flatness-criteria-2026-10-22`, content SHA256
`4bc1f2db6141508f6dad2132d4abc7963380cd71497ad20620c0e511b972a949`;
the statement and complete proof in `046Y.html` were read.

The definitions and elementary quotient equations here are an internal
construction supporting that passage, not a separately numbered source
theorem. They use Mathlib's actual semilinear `Submodule.mapQ` construction.
The directed and cocone laws are proved by quotient induction from the
given laws of `F`. No unpublished draft code is used.

## Concrete diagram and quotient maps

All names below lie in
`Langlands.Algebra.LocalModuleSystem.CompatibleMap`. For
`φ : CompatibleMap E F f`, the definition `φ.cokernelSystem` has type

```lean
LocalModuleSystem D (N ⧸ LinearMap.range f).
```

Its component `obj i` is definitionally
`F.obj i ⧸ LinearMap.range (φ.component i)`. The additive group and
`D.alg i`-module structures are the standard quotient structures, and the
target has the standard `S`-module quotient structure.

The semilinear transition `φ.cokernelMap i j h` is induced by `F.map i j h`.
Its range-containment proof sends the witness `m : E.obj i` to
`E.map i j h m` and uses `φ.map_comm`. The semilinear cocone
`φ.cokernelιM i` is induced by `F.ιM i`; its range-containment proof uses the
witness `E.ιM i m` and `φ.ιM_comm`. Thus these constructions use exactly the
given ring diagram, module transitions and target map.

The equations `cokernelMap_mk` and `cokernelιM_mk` are the representative
computation rules for these induced maps. The corresponding equations
`cokernelSystem_map_mk` and `cokernelSystem_ιM_mk` expose those rules directly
through the system:

```text
C.map i j h [n] = [F.map i j h n]
C.ιM i [n]      = [F.ιM i n].
```

The directed identity and composition laws reduce to those of `F` after
quotient induction. The cocone compatibility law similarly reduces to
`F.ιM_compat`.

The definition `φ.cokernelQuotient` is a
`CompatibleMap F φ.cokernelSystem (LinearMap.range f).mkQ`. Its component
maps are the actual quotient maps
`(LinearMap.range (φ.component i)).mkQ`; its target is the actual quotient
map `(LinearMap.range f).mkQ`. Both compatibility equations compute
definitionally. The lemma `cokernelQuotient_component` exposes its value
on a component element.

## Actual additive comparison and scope

The constructed system uses the existing
`LocalModuleSystem.moduleColimitMap`, which is Mathlib's additive
direct-limit lift of its supplied semilinear cocone. The theorem
`cokernelSystem_moduleColimitMap_of_mk` says that the canonical direct-limit
inclusion of `[n]` maps to `[F.ιM i n]`. Its proof applies the published
`moduleColimitMap_of` formula and then the quotient cocone formula.

All nine universe levels remain independent: `uI` for the index,
`uA,uB` for component rings, `uE,uF` for the two component module families,
and `uR,uS,uM,uN` for ambient carriers. Quotient components stay in `uF`
and the target quotient stays in `uN`. No scalar restriction or replacement
of quotient carriers is made.

The construction assumes no approximation, flatness, or injectivity
property. It asserts no colimit-preservation or flatness conclusion.
Bijectivity of the cokernel comparison from bijectivity of the two input
comparisons is a separate subsequent statement and proof. Generic flatness
ascent and the residue-fibre stabilization argument also remain separate.
