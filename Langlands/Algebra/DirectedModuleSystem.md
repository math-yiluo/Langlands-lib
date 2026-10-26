# Directed varying-ring module cocones and canonical comparisons

This module supplies the internal interface
`Langlands.Algebra.DirectedModuleSystem` for a directed diagram of commutative
rings and modules, with a compatible cocone to a specified commutative ring `R`
and a specified `R`-module `M`. It defines the actual ring and additive
colimit comparisons and a predicate that both are bijective. It also provides
one adapter from the published local approximation module system to its base
rings.

## Internal provenance and reuse

The generic interface is an internal supporting definition, motivated by the
passage from stage modules to their limit in the later flatness criteria. It is
not a claim that a new existence or flatness result has been proved. The data
presentation follows the published
`Langlands.Algebra.LocalApproximationSystem`, while retaining only the ring,
module, transition and cocone data needed here. The local adapter imports that
module without modifying its declarations.

The original motivation for that published local interface is the registered
source `stacks-algebra-flatness-criteria-2026-10-22`, content SHA256
`4bc1f2db6141508f6dad2132d4abc7963380cd71497ad20620c0e511b972a949`:
`00QV.html`, Lemma 10.127.11 and its proof; `00QL.html`, Remark 10.127.12
(tag 00QW) and Lemma 10.127.13 (tag 00QX), including the proof; and
`00R3.html`, Lemma 10.128.3 (tag 00R6), for the later use. These passages were
read for this unit. In particular, 00QW warns that an arbitrary finite-type
approximation system need not have the desired localization transitions.
No such localization property is inferred by this adapter. The corrected
polynomial-quotient maps and prime localizations in 00QV remain in the existing
local interface and are not reconstructed here.

All universal constructions come from Mathlib at commit
`5ed2965256430c3649e86755f9576b54eca72435`:

- `Order/DirectedInverseSystem.lean`: `DirectedSystem` stores the identity and
  composition laws.
- `Algebra/Colimit/Ring.lean`: `Ring.DirectLimit`, `of`, `lift`, and `lift_of`.
- `Algebra/Colimit/Module.lean`: `AddCommGroup.DirectLimit`, `of`, `lift`, and
  `lift_of` on underlying additive maps.

Mathlib's `Algebra/Category/ModuleCat/Presheaf/ColimitFunctor.lean` was also
inspected. Its `PresheafOfModules.ModuleColimit` constructs a module action on a
categorical additive colimit, and gives scalar formulas and joint surjectivity.
Its ring, component modules and cocone carriers use a shared universe `w`.
The published `Langlands.Algebra.Modules.TensorColimit` supplies tensor and
balanced-map machinery with a shared carrier universe as well. This unit
therefore reuses the underlying algebraic direct-limit lifts directly, keeping
all five carrier/index universes independent and using the target's existing
action. It does not duplicate either categorical action construction or tensor
comparison.

## Generic data and laws

All declarations lie in `Langlands.Algebra`. The full generic parameter list is

```lean
DirectedModuleSystem.{uI, uA, uN, uR, uM} ι R M
```

with `ι : Type uI`, `[Preorder ι] [Nonempty ι] [IsDirectedOrder ι]`,
`R : Type uR`, `M : Type uM`, and `[CommRing R] [AddCommGroup M] [Module R M]`.
Antisymmetry is not required. The component rings `base i : Type uA` and
modules `obj i : Type uN` can have universes distinct from each other, the
index, and both target carriers.

For `D : DirectedModuleSystem ι R M`, the exposed fields are:

| Fields | Meaning |
| --- | --- |
| `base`, `obj` | Actual component rings and module carriers. |
| `baseCommRing`, `objAddCommGroup`, `objModule` | Their commutative ring, additive group and `base i`-module structures; registered as instances. |
| `baseMap i j h` | A ring homomorphism `base i →+* base j` for `h : i ≤ j`. |
| `map i j h` | A semilinear map `obj i →ₛₗ[baseMap i j h] obj j`. |
| `base_directed`, `directed` | Mathlib `DirectedSystem` laws for both families, registered as instances. |
| `baseι i`, `ιM i` | A ring map `base i →+* R` and a semilinear map `obj i →ₛₗ[baseι i] M`. |
| `baseι_compat`, `ιM_compat` | The ring and module cocone compatibility equations. |

For either transition family `f`, the directed laws say
`f i i le_rfl x = x` and
`f j k hjk (f i j hij x) = f i k (hij.trans hjk) x`.
Semilinearity gives

```text
map i j h (r • m) = baseMap i j h r • map i j h m
ιM i (r • m) = baseι i r • ιM i m.
```

The cocone laws are
`baseι j (baseMap i j h r) = baseι i r` and
`ιM j (map i j h m) = ιM i m`.
The target action in these equations is exactly the supplied `Module R M`.

## Canonical comparison maps

`D.RingColimit : Type (max uI uA)` abbreviates the actual
`Ring.DirectLimit D.base (fun i j h ↦ D.baseMap i j h)`.
`D.ModuleColimit : Type (max uI uN)` abbreviates the actual
`AddCommGroup.DirectLimit` of the underlying additive transition maps, fixing
`Classical.decEq ι` as its index equality decision.
Despite its name, this second abbreviation only supplies an additive group;
it introduces no action of `D.RingColimit`.

The maps

```text
D.ringColimitMap   : D.RingColimit →+* R
D.moduleColimitMap : D.ModuleColimit →+ M
```

are defined by `Ring.DirectLimit.lift` and
`AddCommGroup.DirectLimit.lift` on the specified cocones. There is no freely
chosen comparison map field. `ringColimitMap_of` and `moduleColimitMap_of`
prove that each map sends a canonical inclusion from component `i` to
`D.baseι i` and `D.ιM i`, respectively.

Writing `ofRing i` and `ofModule i` for Mathlib's canonical inclusions,
`moduleColimitMap_smul_of` proves the component equation

```text
D.moduleColimitMap (ofModule i (r • m)) =
  D.ringColimitMap (ofRing i r) • D.moduleColimitMap (ofModule i m).
```

Its proof uses the two inclusion formulas and the given cocone's
semilinearity. The scalar multiplication on the right is the existing target
action. The two inclusion formulas follow from Mathlib's `lift_of` rules.

`DirectedModuleSystem.IsColimit D : Prop` is exactly

```lean
Function.Bijective D.ringColimitMap ∧ Function.Bijective D.moduleColimitMap
```

Thus this predicate identifies the actual algebraic colimits with the targets
via their canonical maps. It does not assert that every cocone is a colimit.
Neither flatness nor any finite-type, finite-presentation, Noetherianity,
locality, approximation or tensor-transition property is a field or a clause of
this generic structure or predicate. Eventual flatness and its ascent to the
target remain a later statement and proof.

## Base-ring adapter for the local interface

For the published
`D : LocalAlgebraSystem.{uI,uA,uB,uR,uS} ι R S` and
`E : LocalModuleSystem.{uI,uA,uB,uN,uR,uS,uM} D M`, the definition

```lean
LocalModuleSystem.toDirectedModuleSystem E
```

requires the caller's `[Module R M]` and `[IsScalarTower R S M]` in addition to
the existing `[Module S M]`. Its result is
`DirectedModuleSystem.{uI,uA,uN,uR,uM} ι R M`.
The adapter uses `D.base i` as its ring, `E.obj i` as its module, and

```lean
Module.compHom (E.obj i) (algebraMap (D.base i) (D.alg i))
```

as the component action. It keeps the underlying additive transition and
cocone maps of `E`. Transition semilinearity over `D.baseMap` follows from
`E.map`'s semilinearity and `D.map_comm`; cocone semilinearity over `D.baseι`
follows from `E.ιM`'s semilinearity, `D.ι_comm` and
`IsScalarTower.algebraMap_smul`. The directed and cocone compatibility proofs
are inherited from `D` and `E`.

The theorems
`LocalModuleSystem.toDirectedModuleSystem_ringColimitMap` and
`LocalModuleSystem.toDirectedModuleSystem_moduleColimitMap` prove equalities of
the whole comparison homomorphisms with `D.baseColimitMap` and
`E.moduleColimitMap`. Both proofs are `rfl`: the underlying direct-limit types,
additive maps and canonical lifts are definitionally unchanged by restriction
of component scalars. The adapter assumes no `IsApproximation` or `IsColimit`
property, and proves no new colimit property. The separate regular-module
adapter and the later flatness-ascent result are outside this unit.
