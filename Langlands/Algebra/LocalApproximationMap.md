# Compatible maps of local module approximation systems

This module packages a compatible family of component-linear maps between two
given `LocalModuleSystem`s over exactly the same `LocalAlgebraSystem`. It
constructs the induced map on their actual additive direct limits and proves
that it induces the specified target `S`-linear map.

## Source and provenance

The source motivation is the first proof paragraph of the Stacks Project,
Lemma 10.128.4 (tag [046Y](https://stacks.math.columbia.edu/tag/046Y)). That
paragraph obtains one system of local ring maps and module maps
`uᵢ : Mᵢ → Nᵢ`, with both module systems satisfying all six conclusions of
Lemma 10.127.13 (tag [00QX](https://stacks.math.columbia.edu/tag/00QX)), and with
the colimit of the component maps equal to the given `S`-module map.

The registered original is `stacks-algebra-flatness-criteria-2026-10-22`,
content SHA256
`4bc1f2db6141508f6dad2132d4abc7963380cd71497ad20620c0e511b972a949`.
The passages read are `00R3.html`, Lemma 10.128.4 and its proof, and
`00QL.html`, Lemma 10.127.13 and its proof. The preceding Remark 10.127.12
(00QW) warns that arbitrary finite-type approximation systems need not have
the required prime-localization property. Here the six conditions are retained
by using the existing approximation predicates verbatim.

The structure, predicate, names, and direct-limit equations in this module are
an internal API presentation of those compatible maps. They are not a separate
existence assertion extracted from the source. The additive construction is
Mathlib's `AddCommGroup.DirectLimit.map`. Its component formula and uniqueness
property give the elementary proofs below.

## Data on the supplied systems

All declarations lie in `Langlands.Algebra.LocalModuleSystem`. Given

```
D : LocalAlgebraSystem ι R S
E : LocalModuleSystem D M
F : LocalModuleSystem D N
f : M →ₗ[S] N
```

`CompatibleMap E F f` has the following fields.

| Field | Meaning |
| --- | --- |
| `component i` | An actual `D.alg i`-linear map `E.obj i →ₗ[D.alg i] F.obj i`. |
| `map_comm i j h m` | `component j (E.map i j h m) = F.map i j h (component i m)`. |
| `ιM_comm i m` | `F.ιM i (component i m) = f (E.ιM i m)`. |

Both component maps act on the supplied module actions, and both compatibility
equations use the supplied semilinear transitions and cocones. There are no
additional choices of component rings, ring maps, module diagrams, or cocones.
The target map is `S`-linear, as in 046Y.

## Simultaneous approximation and the induced map

For `φ : CompatibleMap E F f`, the proposition `φ.IsApproximation` is exactly
`E.IsApproximation ∧ F.IsApproximation`. In particular it retains both existing
six-clause predicates and their actual comparison, tensor-transition, and
prime-localization maps. It adds no flatness or injectivity assumption.

The following names are in `LocalModuleSystem.CompatibleMap`.

`φ.colimitMap` is an additive homomorphism from the Mathlib direct limit of
the underlying additive transitions of `E` to that of `F`. The definition uses
classical decidable equality on `ι`, exactly as the existing
`LocalModuleSystem.moduleColimitMap` does. It applies Mathlib's direct-limit
map to `(φ.component i).toAddMonoidHom`; pointwise `map_comm` supplies the
homomorphism compatibility required by that construction.

`φ.colimitMap_of i m` proves that the image of the canonical inclusion of
`m : E.obj i` is the canonical inclusion of `φ.component i m`. The proof is
Mathlib's `map_apply_of` computation rule.

`φ.moduleColimitMap_comp` is the equality of actual additive homomorphisms

```
F.moduleColimitMap.comp φ.colimitMap =
  f.toAddMonoidHom.comp E.moduleColimitMap.
```

The proof uses `AddCommGroup.DirectLimit.hom_ext`, evaluates both composites
on every canonical inclusion, simplifies the component formulas, and applies
`φ.ιM_comm`. The lemma `φ.moduleColimitMap_colimitMap x` is the pointwise
form obtained by evaluating this homomorphism equality. These equations hold
for every compatible map, without approximation hypotheses. When both
approximation predicates hold, their existing bijective comparison maps
identify this commuting square with the prescribed target map.

## Universes and scope

The module keeps nine independent universe levels: `uI` for the index, `uA`
and `uB` for the component base and algebra rings, `uE` and `uF` for the two
component module families, and `uR,uS,uM,uN` for the four ambient carriers.
Thus the additive direct limits can lie in the different universes
`max uI uE` and `max uI uF`, and `M` and `N` need not share a universe.
All ambient assumptions are those required by the existing systems, together
with the two `S`-module structures.

This unit constructs no approximating system and asserts no existence of a
compatible map. The intended later existence statement uses a local map
`R → S` that is essentially of finite presentation, finitely presented
`S`-modules `M,N`, and an `S`-linear map `f`. Those hypotheses are unnecessary
for the data and elementary equations here. Eventual flatness, eventual fibre
injectivity, and residue-fibre colimit assertions require further results.
The exposed component maps and equations can be used with the separately
defined residue-fibre modules without altering their definitions.
