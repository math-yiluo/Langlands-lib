# Approximation of the actual synchronized residue-fibre system

This module defines one proposition,
`Langlands.Algebra.LocalTowerResidueFiberApproximationStatement`. It is a
statement only. Nothing in this module proves the proposition, and no proof,
witness or partial result is assumed. The module imports only the published
package `Langlands.Algebra.LocalTowerResidueFiberSystem` and changes no
existing declaration.

## Setting

The proposition quantifies over all of the following data:

- a nonempty directed preorder `ι : Type uI`;
- commutative local rings `R : Type uR`, `S : Type uS` and `T : Type uT`;
- algebras `R → S`, `S → T` and `R → T` with `IsScalarTower R S T`, where
  the adjacent maps `R → S` and `S → T` are local (`IsLocalHom`);
- an additive commutative group `M : Type uM` with given `R`-, `S`- and
  `T`-module structures that are compatible: `IsScalarTower R S M`,
  `IsScalarTower S T M` and `IsScalarTower R T M`;
- a synchronized tower `D : LocalAlgebraTowerSystem.{uI, uA, uB, uC} ι R S T`,
  with components `R_i = D.rs.base i : Type uA`, `S_i = D.rs.alg i : Type uB`
  and `T_i = D.top i : Type uC`;
- a module tower `E : LocalModuleTowerSystem.{uI, uA, uB, uC, uN} D M`, with
  components `M_i = E.stModule.obj i : Type uN`.

Locality of `R → T` is not a hypothesis. Inside the conclusion it is supplied
by `letI := LocalAlgebraTowerSystem.composite_local R S T`, the published
proof that `R → T` is local because it is the composite `R → S → T`. The
module opens the scoped instances of `ResidueFiberTensor`,
`LocalModuleSystem` and `LocalModuleTowerSystem`. These are needed for the
target `F`-algebra structure on `G` and the target `G`-module structure on
`N` below; no other instance is introduced.

## Notation

Write `κ_i = ResidueField R_i` and `κ = ResidueField R`. The objects are
exactly those of the published package:

| Symbol | Lean term |
| --- | --- |
| `F_i` | `D.rs.FiberRing i = D.rs.alg i ⊗[D.rs.base i] κ_i` |
| `G_i` | `D.UpperFiberRing i = D.top i ⊗[D.rs.base i] κ_i` |
| `N_i` | `E.rsModule.ResidueFiber i = κ_i ⊗[D.rs.base i] E.stModule.obj i` |
| `F` | `LocalAlgebraSystem.TargetFiberRing R S = S ⊗[R] κ` |
| `G` | `LocalAlgebraSystem.TargetFiberRing R T = T ⊗[R] κ` |
| `N` | `LocalModuleSystem.TargetResidueFiber R M = κ ⊗[R] M` |

The fibre-ring diagram is `D.fiberSystem`, a value of
`LocalAlgebraSystem ι F G`. Its component algebra `F_i → G_i` is
`ResidueFiberTensor.upperAlgebra`, with algebra map `D.fiberHom i`. Its
transitions are `D.rs.fiberRingMap h` and `D.upperFiberRingMap h`, and its
cocones are `D.rs.fiberRingι i` and `D.upperFiberRingι i`. The `F`-algebra
structure on `G` is the scoped `upperAlgebra R S κ T`, with algebra map
`targetFiberHom`.

The residue-module diagram is `E.fiberModuleSystem`, a value of
`LocalModuleSystem D.fiberSystem N`. The `G_i`-action on `N_i` is the
package's `ResidueFiberTensor.rawModule` action. Its transitions and cocone
maps are `E.rtModule.residueFiberRingMap h` and
`E.rtModule.residueFiberRingι i`; their underlying functions are
`E.rsModule.residueFiberMap h` and `E.rsModule.residueFiberι i`. The
`G`-module structure on `N` is the scoped `rawModule R T κ M`. All of these
identifications are the published projection equations of the package.

## Statement

Schematically, with the binders of the setting above abbreviated:

```text
def LocalTowerResidueFiberApproximationStatement : Prop :=
  ∀ ι R S T [...] M [...] D E,
    E.IsApproximation →
      letI := LocalAlgebraTowerSystem.composite_local R S T
      E.fiberModuleSystem.IsApproximation
```

The only premise after the quantified setting is `E.IsApproximation`, the
published simultaneous approximation property of the tower. It says that
`D.IsApproximation` holds, that the module colimit comparison
`E.stModule.moduleColimitMap` is bijective, that each `M_i` is finite over
`T_i`, and that each module transition after base change
`T_j ⊗[T_i] M_i → M_j` is bijective.

The conclusion is the existing definition `LocalModuleSystem.IsApproximation`,
used unchanged, for the package `E.fiberModuleSystem`. Spelled out, it is the
conjunction of the following six clauses.

1. Colimits: `E.fiberModuleSystem.IsColimit`. That is, the ring colimit
   comparisons `D.fiberSystem.baseColimitMap : colim F_i → F` and
   `D.fiberSystem.algebraColimitMap : colim G_i → G` are bijective, and the
   additive module comparison
   `E.fiberModuleSystem.moduleColimitMap : colim N_i → N` is bijective.
2. For every `i`, `Algebra.EssFiniteType ℤ F_i`.
3. For every `i`, `Algebra.EssFiniteType F_i G_i`, through `D.fiberHom i`.
4. For every `i`, `Module.Finite G_i N_i`, for the package action.
5. For all `h : i ≤ j`, `D.fiberSystem.IsPrimeLocalization h`. That is, the
   canonical map `D.fiberSystem.ringBaseChangeMap h : G_i ⊗[F_i] F_j → G_j`,
   `g ⊗ f ↦ D.upperFiberRingMap h g * D.fiberHom j f`, makes `G_j` the
   localization of `G_i ⊗[F_i] F_j` at some prime ideal.
6. For all `h : i ≤ j`, the canonical map
   `E.fiberModuleSystem.moduleBaseChangeMap h : G_j ⊗[G_i] N_i → N_j`,
   `g ⊗ n ↦ g • E.rsModule.residueFiberMap h n`, is bijective.

No other hypothesis is added. In particular there is no premise of ambient
or component essential finite presentation, ambient finite presentation of
`M`, flatness, nontriviality, injectivity of transitions, Noetherianity, or
any fibre colimit, fibre localization or fibre base-change property. No
replacement diagram, action or witness field is used.

## Provenance

The source is the Stacks Project, Lemma 10.128.8, tag **00R7**, and its proof.
The registered source is `stacks-algebra-flatness-criteria-2026-10-22`,
content SHA256
`4bc1f2db6141508f6dad2132d4abc7963380cd71497ad20620c0e511b972a949`, file
`00R7.html`, around lines 224–236 of the snapshot. The six clauses are those
of Lemma 10.127.13, tag **00QX**, in `00QL.html` of the same snapshot. The
project's current-version checks `stacks-00r7-current-check-2026-10-26` and
`stacks-046y-00qx-current-errata-check-2026-10-26` record no comments or
errata for these passages. The source's upper ring `S'` is `T` here, and its
`𝔭_λ` is the maximal ideal of `R_λ`.

In the proof of 00R7, the source first notes that the colimits
`S/𝔪S`, `S'/𝔪S'` and `M/𝔪M` are the colimits of the corresponding fibres
of the system. It then shows that the fibre ring transitions are
localizations and the fibre module transitions are isomorphisms. It
concludes:

> Hence the system (S_λ/𝔭_λS_λ → S'_λ/𝔭_λS'_λ, M_λ/𝔭_λM_λ) is a system as in
> Lemma 10.127.13 as well.

The present proposition is the project's version of this sentence. It is a
derived internal supporting statement: the source does not state it as a
separate lemma, and the Lean formulation is ours. The source writes the
fibres as quotients by `𝔭_λ`; the published package uses the tensor
presentations `S_i ⊗[R_i] κ_i`, `T_i ⊗[R_i] κ_i` and `κ_i ⊗[R_i] M_i`. No
quotient-to-tensor comparison is constructed or assumed. The source writes
the module transition module-first, `M_λ/𝔭_λM_λ ⊗ S'_μ/𝔭_μS'_μ`; the
published `moduleBaseChangeMap` is scalar-first, `G_j ⊗[G_i] N_i`. Over
commutative rings these differ only by the tensor swap. The source's
hypotheses on the system are those of the chosen system in its proof; here
they are packaged as the single premise `E.IsApproximation` on an arbitrary
synchronized tower.

## Relation to ambient finiteness

After this sentence the source applies Lemma 10.128.3 (tag **00R6**) a
second time, to the fibre system and the fibre data `S/𝔪S → S'/𝔪S'`,
`M/𝔪M`. That application also needs finiteness of the target fibre data:
essential finite presentation of `G` over `F` and finite presentation of `N`
over `G`. That is a separate assertion about the ambient rings, stated in the
published `Langlands.Algebra.ResidueFiberFinitenessStatement` under the
ambient hypotheses that `T` is essentially of finite presentation over `S`
and `M` is finitely presented over `T`. It is not part of this proposition:
neither its premises nor its conclusion appear here, and the six clauses
above concern only the varying components, colimits and transitions.

## What is not claimed

This module proves nothing. It does not prove the implication, any of its
six clauses, the residue-field or tensor colimit comparisons, the fibre
transition localizations or module base-change bijections, or the component
finiteness facts. These are expected to be assembled in a separate proof of
this exact proposition from the supporting statements
`LocalApproximationResidueColimitStatement` (colimits) and
`LocalTowerResidueFiberBaseChangeStatement` (transitions), once proved, and
from elementary component finiteness arguments.

## Universes

The nine universe parameters `uI`, `uA`, `uB`, `uC`, `uN`, `uR`, `uS`, `uT`
and `uM` stay independent. Inspecting the complete declaration reports
exactly these level parameters, in this order, and a `Prop`-valued result.
The fibre carriers keep the published universe maxima: `F_i` and `G_i` lie
in `max uB uA` and `max uC uA`, `N_i` in `max uA uN`, and `F`, `G`, `N` in
`max uS uR`, `max uT uR` and `max uR uM`. No index, component or ambient
universes are identified, and the rings are not restricted to a small
universe.
