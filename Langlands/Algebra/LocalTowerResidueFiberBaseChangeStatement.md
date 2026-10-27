# Residue-fibre transition localization and module base change

This module defines two named maps with their pure-tensor formulas and one
proposition, `Langlands.Algebra.LocalTowerResidueFiberBaseChangeStatement`.
It is a statement only. Nothing in this module proves the proposition, and no
proof or witness is assumed. The module imports only the published
`Langlands.Algebra.LocalTowerResidueFiberRings`.

## Setting and notation

The proposition quantifies over all of the following data:

- a nonempty directed preorder `ι : Type uI`;
- commutative local rings `R : Type uR`, `S : Type uS` and `T : Type uT`;
- algebras `R → S`, `S → T` and `R → T` with `IsScalarTower R S T`, where
  `R → S` and `S → T` are local (`IsLocalHom`);
- a synchronized tower `D : LocalAlgebraTowerSystem ι R S T`, with
  components `R_i = D.rs.base i : Type uA`, `S_i = D.rs.alg i : Type uB` and
  `T_i = D.top i : Type uC`.

Write `κ_i = ResidueField R_i` and use the published fibre rings

```text
F_i = D.rs.FiberRing i   = S_i ⊗[R_i] κ_i,
G_i = D.UpperFiberRing i = T_i ⊗[R_i] κ_i.
```

`G_i` is an `F_i`-algebra through exactly the published scoped instance
`ResidueFiberTensor.upperAlgebra R_i S_i κ_i T_i`. Its algebra map is
`D.fiberHom i`, given by `s ⊗ a ↦ algebraMap S_i T_i s ⊗ a`. For `h : i ≤ j`,
`D.rs.fiberRingMap h : F_i →+* F_j` and `D.upperFiberRingMap h : G_i →+* G_j`
are the published fibre transitions. The published `D.fiberHom_map h` says
that they commute with `D.fiberHom`.

For the module part, `M` is an additive commutative group in `Type uM` with
given `T`- and `S`-module structures and `IsScalarTower S T M`, and
`E : LocalModuleTowerSystem D M` has components `M_i = E.stModule.obj i`
in `Type uN`. Write

```text
N_i = E.rsModule.ResidueFiber i = κ_i ⊗[R_i] M_i,
```

where `R_i` acts on `M_i` by the published restriction of the actual
`T_i`-action. `N_i` keeps its published upper `G_i`-action, namely
`ResidueFiberTensor.rawModule R_i T_i κ_i M_i`. This action is determined by
`(t ⊗ a) • (b ⊗ m) = (a * b) ⊗ (t • m)`. No `R`-action on `M` is required.

## The two maps

Both maps are defined as standard tensor lifts of published maps. They are
not arbitrary isomorphisms, algebra structures or witness fields.

**Ring transition.** `LocalAlgebraTowerSystem.upperFiberBaseChangeMap h` is
a ring map

```text
G_i ⊗[F_i] F_j →+* G_j.
```

Here `F_j` is an `F_i`-algebra by `(D.rs.fiberRingMap h).toAlgebra`, and
`G_j` is an `F_i`-algebra through the common composite
`((D.fiberHom j).comp (D.rs.fiberRingMap h)).toAlgebra`. The map is
`Algebra.TensorProduct.lift` of two `F_i`-algebra maps. The left map is
`D.upperFiberRingMap h`, which is `F_i`-linear by `D.fiberHom_map h`. The
right map is `D.fiberHom j`. The simp lemma `upperFiberBaseChangeMap_tmul`
holds by `rfl`:

```text
g ⊗ f ↦ D.upperFiberRingMap h g * D.fiberHom j f.
```

**Module transition.**
`LocalModuleTowerSystem.upperResidueFiberBaseChangeMap h` is a `G_j`-linear
map

```text
G_j ⊗[G_i] N_i →ₗ[G_j] N_j.
```

Here `G_j` is a `G_i`-algebra by `(D.upperFiberRingMap h).toAlgebra`. The
existing upper action on `N_j` is restricted to `G_i` with `Module.compHom`,
and the corresponding scalar tower holds definitionally. The map is
`LinearMap.liftBaseChange` of the published upper-semilinear residue
transition `E.rtModule.residueFiberRingMap h`, viewed as a `G_i`-linear map.
The construction locally installs `LocalAlgebraTowerSystem.composite_local
R S T`, which the `rt` projection needs. The simp lemma
`upperResidueFiberBaseChangeMap_tmul` gives

```text
g ⊗ n ↦ g • E.rsModule.residueFiberMap h n.
```

Its proof uses the published `rtModule_residueFiberMap` to identify the
underlying function of the upper transition with the lower raw transition
`E.rsModule.residueFiberMap h`.

## Statement

The proposition is a conjunction, inside the quantification over the ring
data and `D`, of the following two claims.

1. For all `i j : ι` and `h : i ≤ j`, if `D.st.IsPrimeLocalization h` holds,
   then, with `F_j` an `F_i`-algebra as above and `G_j` an algebra over
   `G_i ⊗[F_i] F_j` by `(D.upperFiberBaseChangeMap h).toAlgebra`,

   ```text
   ∃ (p : Ideal (G_i ⊗[F_i] F_j)) (hp : p.IsPrime),
     IsLocalization.AtPrime G_j p.
   ```

   The hypothesis is the published predicate of the original upper
   transition: the map `T_i ⊗[S_i] S_j → T_j`,
   `t ⊗ s ↦ D.topMap i j h t * algebraMap S_j T_j s`, is a localization at a
   prime.

2. For every `M` and `E` as above, and all `i j : ι` and `h : i ≤ j`, if the
   published original upper module transition
   `E.stModule.moduleBaseChangeMap h : T_j ⊗[T_i] M_i → M_j`,
   `t ⊗ m ↦ t • E.stModule.map i j h m`, is bijective, then
   `E.upperResidueFiberBaseChangeMap h` is bijective.

The module claim does not use the localization hypothesis of the ring claim.
There are no other hypotheses. In particular there is no assumption of
colimits, approximation, finiteness, essential finite type or presentation,
Noetherianity, flatness, nontriviality, residue injectivity, locality of a
fibre tensor, or any other localization or bijectivity property. No fibre
transition conclusion is assumed.

The nine universe parameters `uI`, `uA`, `uB`, `uC`, `uN`, `uR`, `uS`, `uT`
and `uM` stay independent. Inspecting the complete declaration reports exactly
these level parameters, in this order, and a `Prop`-valued result.

A private development check, not part of this module, confirmed the following
by `rfl`. Install `composite_local R S T`, and for the module map also assume
compatible `R`-actions on `M`. Then the two maps are definitionally equal to
`D.fiberSystem.ringBaseChangeMap h` and
`E.fiberModuleSystem.moduleBaseChangeMap h` of the published package
`Langlands.Algebra.LocalTowerResidueFiberSystem`. The ring claim's conclusion
is `Iff.rfl` to `D.fiberSystem.IsPrimeLocalization h`. The same check confirmed
that the instances used are exactly `upperAlgebra` and `rawModule`. The
package itself is not imported here, because its module system requires an
`R`-action on `M`.

## Provenance

The source is the Stacks Project, Lemma 10.128.8, tag **00R7**, and its proof.
The registered source is `stacks-algebra-flatness-criteria-2026-10-22`,
content SHA256
`4bc1f2db6141508f6dad2132d4abc7963380cd71497ad20620c0e511b972a949`, file
`00R7.html`, lines 224–236 of the snapshot. No errata for this passage were
found in the project, the current Library or the central notes when checked on
2026-10-27. The source's upper ring `S'` is `T` here, and its `𝔭_λ` is the
maximal ideal of `R_λ`.

The proof of 00R7 first records three transition properties for
`λ ≤ μ`. Among them, `S'_λ ⊗_{S_λ} S_μ → S'_μ` is a localization and
`M_λ ⊗_{S'_λ} S'_μ → M_μ` is an isomorphism. These are the hypotheses of the
two claims here. The proof then says that, from these properties,

```text
S'_λ/𝔭_λS'_λ ⊗_{S_λ/𝔭_λS_λ} S_μ/𝔭_μS_μ → S'_μ/𝔭_μS'_μ   is a localization,
M_λ/𝔭_λM_λ ⊗_{S'_λ/𝔭_λS'_λ} S'_μ/𝔭_μS'_μ → M_μ/𝔭_μM_μ   is an isomorphism.
```

It uses these two facts to conclude that the fibre system is again a system
as in Lemma 10.127.13 (tag **00QX**). The two claims here are the project's
versions of these displayed maps. They are derived internal supporting
statements; the source does not state them as separate lemmas.

The source writes the fibres as quotients by `𝔭_λ`. The published fibre rings
use tensor presentations instead: `S_i ⊗[R_i] κ_i` and `T_i ⊗[R_i] κ_i` for
the rings, and `κ_i ⊗[R_i] M_i` for the module. No quotient-to-tensor
comparison is constructed or assumed. The ring map has the source's factor
order. The source writes the module map module-first,
`M_λ/𝔭_λM_λ ⊗ S'_μ/𝔭_μS'_μ`; here it is scalar-first, `G_j ⊗[G_i] N_i`, as
required by `LinearMap.liftBaseChange`. Over commutative rings these two
orders differ only by the tensor swap.

The source says only "a localization". Here the conclusion is localization at
a prime ideal, in the same form as the hypothesis `IsPrimeLocalization`. Since
`G_j` is local, the stronger form is expected to follow from localization at
some submonoid. This module does not prove that.

## Expected proof route (not proved here)

For the ring claim, base-change the original localization
`T_i ⊗[S_i] S_j → T_j` along `S_j → F_j`. Identify the source and target with
the displayed fibre tensors by tensor cancellation, and check the actual map
on pure tensors. This gives a localization at an image submonoid. Since `G_j`
is local, it can be enlarged to the complement of the inverse image of the
maximal ideal of `G_j`.

For the module claim, combine the published upper comparisons
`E.upperFiberModuleEquiv i : G_i ⊗[T_i] M_i ≃ₗ[G_i] N_i` and their naturality
`upperFiberModuleEquiv_map` with tensor cancellation. Then base-change the
original bijective module map along `T_j → G_j`, and check that the composite
agrees with the actual map on pure tensors.

None of this is proved here. In particular, this module does not prove the
two implications or construct the tensor comparisons they need.
