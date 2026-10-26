# Actual residue fibres of local approximation systems

This module constructs the residue-field and residue-module diagrams of the
published `Langlands.Algebra.LocalAlgebraSystem` and `LocalModuleSystem`, together
with their extension to the target residue field. All maps use the specified
ring and module maps. The only proofs are scalar compatibility, computation,
identity, composition and cocone laws.

## Source and provenance

The registered original is `stacks-algebra-flatness-criteria-2026-10-22`, content
SHA256 `4bc1f2db6141508f6dad2132d4abc7963380cd71497ad20620c0e511b972a949`:

- `046Y.html`, Lemma 10.128.4, proof, the displayed residue-field extension maps
  Ψλ and Ψλ,λ′ and the subsequent localization argument;
- `00QL.html`, Lemma 10.127.13 (00QX), all six conditions and its proof.

The online originals are [046Y](https://stacks.math.columbia.edu/tag/046Y) and
[00QX](https://stacks.math.columbia.edu/tag/00QX). The source writes the component
residue module as `Mᵢ / 𝔪ᵢ Mᵢ`. Here it is represented by the actual tensor
`κᵢ ⊗[Rᵢ] Mᵢ`, the standard tensor presentation of that quotient. The outer
extension also uses scalar-first order, so its carrier is
`κ ⊗[κᵢ] (κᵢ ⊗[Rᵢ] Mᵢ)` rather than the source's quotient-first order.
No equivalence with a quotient presentation is proved in this module.

The declaration names, scoped instances, semilinear packaging and fixed-target-field
transition maps are an internal implementation of these source constructions.
Mathlib supplies `IsLocalRing.ResidueField.map`, `TensorProduct.map` and
`LinearMap.liftBaseChange`. The latter constructs Ψᵢ directly on the stated
carrier, so no change of tensor presentation or comparison equivalence is used.
The source's finite-stage Ψλ,λ′ motivates the semilinear component transitions;
a separate map on `κⱼ ⊗[κᵢ] (κᵢ ⊗[Rᵢ] Mᵢ)` is not exported here.

The source proves eventual injectivity using finite generation, colimits and
localization. None of that argument is implemented or assumed here. The six
00QX approximation properties are not hypotheses of this module's maps or laws.
Fibre rings, their module actions and comparison equivalences, localization and
colimit results, approximation existence, flatness and eventual injectivity
remain separate developments.

## Parameters, actions and universes

All names below are in `Langlands.Algebra`. The ambient parameters are

```
ι : Type uI, [Preorder ι] [Nonempty ι] [IsDirectedOrder ι]
R : Type uR, S : Type uS
[CommRing R] [CommRing S] [IsLocalRing R] [IsLocalRing S]
[Algebra R S] [IsLocalHom (algebraMap R S)]
D : LocalAlgebraSystem.{uI,uA,uB,uR,uS} ι R S
M : Type uM, [AddCommGroup M] [Module S M]
E : LocalModuleSystem.{uI,uA,uB,uN,uR,uS,uM} D M.
```

Write `Rᵢ = D.base i`, `Sᵢ = D.alg i`, `Mᵢ = E.obj i`,
`κᵢ = IsLocalRing.ResidueField Rᵢ` and `κ = IsLocalRing.ResidueField R`.
The component rings and modules have universes `uA,uB,uN`, independently of
`uI,uR,uS,uM`. `E.ResidueFiber i` lives in `Type (max uA uN)`,
`LocalModuleSystem.TargetResidueFiber R M` in `Type (max uR uM)`, and
`E.ResidueFiberExtension i` in `Type (max uR uA uN)`.

`LocalModuleSystem.objBaseModule E i` is the actual restriction

```
Module.compHom (E.obj i) (algebraMap (D.base i) (D.alg i)).
```

Its equation `objBaseModule_smul` reads
`r • m = algebraMap Rᵢ Sᵢ r • m`. The scoped instance
`objBaseScalarTower E i` proves `IsScalarTower Rᵢ Sᵢ Mᵢ` for this action.
Consumers can activate both instances with

```
open scoped Langlands.Algebra.LocalModuleSystem
```

No arbitrary component `Rᵢ`-action is accepted as a parameter. Conversely, the
maps into the target module retain the caller's given `[Module R M]` and require
`[IsScalarTower R S M]`; they do not replace this compatible target action.
These two additional assumptions occur in `baseι`, `residueFiberι`, `residueFiberΨ`
and their laws, but not in the component transitions or the fixed-κ extension
transitions. `TargetResidueFiber R M` itself needs only its displayed local ring,
additive group and `R`-module structures.

## The residue-field diagram

In namespace `LocalAlgebraSystem`:

| Declaration | Exact construction or law |
| --- | --- |
| `D.residueMap (h : i ≤ j) : κᵢ →+* κⱼ` | `IsLocalRing.ResidueField.map (D.baseMap i j h)`, using `D.baseMap_local`. |
| `D.residueι i : κᵢ →+* κ` | `IsLocalRing.ResidueField.map (D.baseι i)`, using `D.baseι_local`. |
| `residueMap_residue`, `residueι_residue` | Applying either map to a residue class gives the residue class of the corresponding base-ring image. |
| `residueMap_self` | `D.residueMap (le_refl i) a = a`. |
| `residueMap_comp` | `D.residueMap hjk (D.residueMap hij a) = D.residueMap (hij.trans hjk) a`. |
| `residueι_compat` | `D.residueι j (D.residueMap h a) = D.residueι i a`. |
| `residue_directed` | The `DirectedSystem` instance on the actual residue-field maps. |

The field laws are proved by choosing a representative using Mathlib's
`IsLocalRing.residue_surjective` and applying the original base diagram laws.

## The residue-module diagram

The remaining names are in namespace `LocalModuleSystem`.
`E.baseMap h : Mᵢ →ₛₗ[D.baseMap i j h] Mⱼ` and
`E.baseι i : Mᵢ →ₛₗ[D.baseι i] M` have exactly the underlying functions
`E.map i j h` and `E.ιM i`. Their `_apply` simp lemmas are definitional equalities.
Their semilinearity follows from the original module semilinearity, `D.map_comm`,
`D.ι_comm`, and, for the target, `IsScalarTower.algebraMap_smul`.

`E.ResidueFiber i` abbreviates `κᵢ ⊗[Rᵢ] Mᵢ`, with the restricted base action
just described and the usual residue action of `Rᵢ` on `κᵢ`.
`TargetResidueFiber R M` abbreviates `κ ⊗[R] M`. Each is a module over its
left field factor by Mathlib's tensor-product action.

The auxiliary definitions `residueBaseMap (D := D) h` and
`residueBaseι (D := D) i` package the residue-field maps as semilinear maps
with respect to the base-ring homomorphisms. Applying `TensorProduct.map` to
these and `baseMap` or `baseι` constructs the additive maps on tensors.
Tensor induction proves semilinearity over the residue fields, yielding

```
E.residueFiberMap h : E.ResidueFiber i →ₛₗ[D.residueMap h] E.ResidueFiber j
E.residueFiberι i : E.ResidueFiber i →ₛₗ[D.residueι i] TargetResidueFiber R M.
```

Their computation lemmas are

```
residueFiberMap_tmul: b ⊗ m ↦ D.residueMap h b ⊗ E.map i j h m
residueFiberι_tmul:   b ⊗ m ↦ D.residueι i b ⊗ E.ιM i m.
```

`residueFiberMap_self`, `residueFiberMap_comp` and `residueFiberι_compat`
state the identity, composition and cocone laws pointwise on all tensors.
They are proved by tensor induction from the field laws and the original
module diagram laws. `residueFiber_directed` packages the first two laws as a
`DirectedSystem` instance. No bijectivity or injectivity is asserted.

## Extension to the target residue field

`E.ResidueFiberExtension i` installs `letI := (D.residueι i).toAlgebra` and
abbreviates

```
κ ⊗[κᵢ] E.ResidueFiber i.
```

Thus its `κᵢ`-action on `κ` is multiplication by the image under the actual
residue cocone map. Its `κ`-module structure is the left tensor-factor action.
When writing pure tensors in this type, install the same `letI` explicitly.

`E.residueFiberΨ i : E.ResidueFiberExtension i →ₗ[κ] TargetResidueFiber R M`
restricts the target fibre's `κ`-action along `D.residueι i`, views
`E.residueFiberι i` as a `κᵢ`-linear map for this restriction, and applies
`LinearMap.liftBaseChange κ`. The scalar tower for the restriction is explicitly
constructed and passed to this lift. The computation lemmas state

```
residueFiberΨ_tmul:      Ψᵢ (a ⊗ x) = a • E.residueFiberι i x
residueFiberΨ_tmul_tmul: Ψᵢ (a ⊗ (b ⊗ m)) = (a * D.residueι i b) ⊗ E.ιM i m.
```

The second is exactly the desired double-pure-tensor formula, using the target's
given `R`-module structure.

`E.residueFiberExtensionMap h : E.ResidueFiberExtension i →ₗ[κ]
E.ResidueFiberExtension j` is constructed using `TensorProduct.map` on the
identity function of `κ` and `E.residueFiberMap h`. The identity function is
semilinear over `D.residueMap h` for the two induced field actions because
`D.residueι_compat` holds. Tensor induction then proves `κ`-linearity.
The theorem `residueFiberExtensionMap_tmul` gives

```
a ⊗ x ↦ a ⊗ E.residueFiberMap h x.
```

`residueFiberExtensionMap_self` and `residueFiberExtensionMap_comp` give the
pointwise identity and composition laws, and `residueFiberExtension_directed`
provides the corresponding `DirectedSystem`. Finally, `residueFiberΨ_compat`
states

```
E.residueFiberΨ j (E.residueFiberExtensionMap h x) = E.residueFiberΨ i x.
```

All three laws follow by tensor induction and the already-proved component
laws. They supply a genuine diagram of `κ`-modules with its specified cocone;
they make no assertion that this cocone is a colimit.
