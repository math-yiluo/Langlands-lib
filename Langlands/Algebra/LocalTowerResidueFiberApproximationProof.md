# Approximation of the actual synchronized residue-fibre system: proof

This module proves `Langlands.Algebra.LocalTowerResidueFiberApproximationStatement` as the
theorem `Langlands.Algebra.localTowerResidueFiberApproximation`, at the target's nine
universes `{uI,uA,uB,uC,uN,uR,uS,uT,uM}`.

The proof has two steps. First, `LocalTowerResidueFiberApproximationProof.of_supporting`
derives the target from two supporting statements, taken as hypotheses:

- `LocalApproximationResidueColimitStatement`, at universes `{uI,uA,uB,uN,uR,uS,uM}` (for
  `D.rs` and `E.rsModule`) and `{uI,uA,uC,uN,uR,uT,uM}` (for `D.rt`);
- `LocalTowerResidueFiberBaseChangeStatement`, at the nine universes of the target.

Second, `localTowerResidueFiberApproximation` applies `of_supporting` to the published proofs
of these statements:

- `Langlands.Algebra.localApproximationResidueColimit` (module
  `Langlands.Algebra.LocalApproximationResidueColimitProof`), used at both universe lists;
- `Langlands.Algebra.localTowerResidueFiberBaseChange` (module
  `Langlands.Algebra.LocalTowerResidueFiberBaseChangeProof`).

## Notation

`R_i = D.rs.base i`, `S_i = D.rs.alg i`, `T_i = D.top i`, `κ_i = ResidueField R_i`,
`F_i = S_i ⊗[R_i] κ_i` (`D.rs.FiberRing i`), `G_i = T_i ⊗[R_i] κ_i` (`D.UpperFiberRing i`),
`M_i = E.stModule.obj i`, `N_i = κ_i ⊗[R_i] M_i` (`E.rsModule.ResidueFiber i`).

## Unfolding the premise

`E.IsApproximation` unfolds to
`⟨⟨hrs, hst, hupper, hlocST, hlocRT⟩, hM, hfinite, hbc⟩`, where

- `hrs : D.rs.IsApproximation` (colimit, essential finite type of `R_i` over `ℤ` and of `S_i`
  over `R_i`, prime localization of the transitions),
- `hst : D.st.IsColimit`, `hupper` gives essential finite type of `T_i` over `S_i`,
- `hlocST` and `hlocRT` give prime localization of the `st` and `rt` transitions,
- `hM` is bijectivity of `E.stModule.moduleColimitMap`, `hfinite` is finiteness of `M_i` over
  `T_i`, and `hbc` is bijectivity of `E.stModule.moduleBaseChangeMap h`.

## Clause 1: colimits

Three lemmas show by `rfl` that the package's colimit maps are the lifts named in the colimit
statement:

- `fiberSystem_baseColimitMap_eq`: `D.fiberSystem.baseColimitMap` is the
  `Ring.DirectLimit.lift` of the cocone `D.rs.fiberRingι` out of the rings `D.rs.FiberRing`;
- `fiberSystem_algebraColimitMap_eq`: `D.fiberSystem.algebraColimitMap` is the same lift for
  the composite projection `D.rt`, out of `D.rt.FiberRing = D.UpperFiberRing`;
- `fiberModuleSystem_moduleColimitMap_eq`: with `Classical.decEq ι`,
  `E.fiberModuleSystem.moduleColimitMap` is the `AddCommGroup.DirectLimit.lift` of the cocone
  `E.rsModule.residueFiberι` out of `E.rsModule.ResidueFiber`.

After rewriting with these lemmas, bijectivity comes from the colimit statement:

- conjunct 2 for `D.rs`, with premise `hrs.1 : D.rs.IsColimit`;
- conjunct 2 for `D.rt`, with premise `D.rt.IsColimit = ⟨hrs.1.1, hst.2⟩` (the base colimit of
  `D.rs` and the algebra colimit of `D.st`);
- conjunct 3 for `E.rsModule`, with premise `E.rsModule.IsColimit = ⟨hrs.1, hM⟩` (the
  underlying additive colimit map of `E.rsModule` is that of `E.stModule`).

## Clauses 2–4: component finiteness

These lemmas follow the helpers `component_fiber_essFiniteType_int`,
`component_fiber_essFiniteType` and `component_fiber_finite` in Worker 214's shared draft for task
`8644bad3-d88e-4471-aa5e-c9c93babe680`.

- `fiberRing_essFiniteType_int`: `S_i` is essentially of finite type over `ℤ` (by composition
  through `R_i`), and `s ↦ s ⊗ 1 : S_i → F_i` is surjective because `R_i → κ_i` is. So `F_i` is
  essentially of finite type over `ℤ` (`Algebra.EssFiniteType.of_surjective`).
- `upperFiberRing_essFiniteType`: `T_i` is essentially of finite type over `R_i` (by
  composition through `S_i`). So is its quotient `G_i`, via the surjection `t ↦ t ⊗ 1`.
  `Algebra.EssFiniteType.of_comp` along `R_i → F_i → G_i` then gives the claim for the published
  `upperAlgebra` structure `F_i → G_i`.
- `residueFiber_finite`: `G_i ⊗[T_i] M_i` is finite over `G_i` by Mathlib's
  `Module.Finite.base_change`, and `E.upperFiberModuleEquiv i : G_i ⊗[T_i] M_i ≃ N_i` is
  `G_i`-linear for the package's `rawModule` action, so `Module.Finite.equiv` transports
  finiteness.

## Clauses 5 and 6: transitions

The two conjuncts of the transition statement are applied directly, with no rewriting:

- clause 5 is conjunct 1 of the transition statement at `hlocST i j h`;
- clause 6 is conjunct 2 at `hbc i j h`.

This works because, with the package's structures installed, `D.fiberSystem.RingBaseChange h`
together with its algebra `(D.fiberSystem.ringBaseChangeMap h).toAlgebra` unfolds
definitionally to `D.UpperFiberRing i ⊗[D.rs.FiberRing i] D.rs.FiberRing j` with
`(D.upperFiberBaseChangeMap h).toAlgebra`. In the same way,
`E.fiberModuleSystem.moduleBaseChangeMap h` unfolds to `E.upperResidueFiberBaseChangeMap h`. The
elaborator checks both identifications.

## Assembly

`fiberModuleSystem_isApproximation_of` combines the six clauses into
`E.fiberModuleSystem.IsApproximation`, after installing
`LocalAlgebraTowerSystem.composite_local R S T`. `of_supporting` introduces the binders of the
target statement and applies it. No hypothesis beyond `E.IsApproximation` and the two
supporting statements is used. `localTowerResidueFiberApproximation` then supplies the two
published proofs for those statements, so the final theorem has no hypotheses beyond the
target statement's own.
