# Proof: cohomology retraction along a finite flat morphism of invertible rank

This module proves the published statement
`Langlands.AlgebraicGeometry.Modules.FiniteFlatCohomologyRetractStatement.{u}` (module
`FiniteFlatCohomologyRetractStatement`, imported unchanged). The final theorem is

`Langlands.AlgebraicGeometry.Modules.finiteFlatCohomologyRetract :
  FiniteFlatCohomologyRetractStatement.{u}`.

The statement: let `K` be a field and `f : X ⟶ Y` a morphism of `K`-schemes (objects
of `Over (Spec K)`) such that `f.left` is finite, flat and locally of finite
presentation, with `f.left.finrank y = d` for all `y` and `(d : K) ≠ 0`. Then for
every quasi-coherent `M` on `Y` and every `n`, the `K`-module `Hⁿ(Y, M)` is a retract
of `Hⁿ(X, f^* M)`. Here `Hⁿ` is `DerivedSections.relativeCohomology` of the structure
morphisms and `f^*` is Mathlib's `Scheme.Modules.pullback`.

## Route

The proof builds a trace morphism `t : f_* f^* M ⟶ M` with `η ≫ t = d • 𝟙 M`. Here
`η` is the unit of Mathlib's `Scheme.Modules.pullbackPushforwardAdjunction f`. Then
the published assembly theorem `finiteFlatCohomologyRetract_of_trace` (module
`FiniteFlatCohomologyRetractAssembly`) gives the retraction.

## Declarations

In the namespace `Langlands.Scheme.Modules`:

- `nsmul_app_apply n φ V x`: for a morphism `φ : M ⟶ N` of modules on `Y`,
  `(n • φ).app V x = n • φ.app V x`. Proof: induction on `n`. Both cases close by
  `simp`, which uses Mathlib's simp lemmas `Scheme.Modules.Hom.zero_app` and
  `Hom.add_app`; the successor case also uses `succ_nsmul` and the induction
  hypothesis.
- `trace f hd M : f_* f^* M ⟶ M`, for `[IsFinite f] [Flat f]`,
  `hd : ∀ y, f.finrank y = d` and quasi-coherent `M`. It is the published
  `BasisHomGluing.homOfBasicOpen` (module `BasicOpenHomGluing`) for the predicate
  `P := IsFreeChart f` and the local maps `θ V hV := localTrace f M hV.1` (module
  `FiniteFlatTrace`). The hypotheses of the gluing are supplied as follows:
  - free charts are affine (`hV.1`);
  - they are stable under basic opens (`IsFreeChart.basicOpen`);
  - they cover `Y` (`exists_isFreeChart f hd`);
  - the local traces commute with restriction to basic opens (`localTrace_basicOpen`).
- `unit_comp_trace f hd M : η.app M ≫ trace f hd M = d • 𝟙 M`. By the published
  `BasisHomGluing.hom_ext_of_basicOpen`, it suffices to compare both sides on sections
  over each free chart `V`. Take `m : Γ(M, V)`.
  - The left side is `trace.app V (η.app M .app V m)` (`Scheme.Modules.Hom.comp_app`).
    By `BasisHomGluing.homOfBasicOpen_app` this is `localTrace f M hV.1` applied to
    `η.app M .app V m`.
  - That section is the published `sectionPullback f M V m` by definition, so
    `localTrace_sectionPullback` gives `d • m`.
  - The right side is `d • m` by `nsmul_app_apply`.

In the namespace `Langlands.AlgebraicGeometry.Modules`:

- `finiteFlatCohomologyRetract`: introduce the data of the statement. The hypotheses
  `IsFinite f.left` and `Flat f.left` become local instances. `IsAffineHom f.left`
  follows from `IsFinite f.left`, and `M.IsQuasicoherent` is the hypothesis `hM`.
  Then apply `finiteFlatCohomologyRetract_of_trace f M d hd` to
  `t := trace f.left hrank M`, `ht := unit_comp_trace f.left hrank M` and `n`.

The hypothesis `LocallyOfFinitePresentation f.left` is not used: finiteness, flatness
and constant rank already give free charts
(`Module.Free.away_of_finite_of_flat_of_rankAtStalk_constant`, used in
`exists_isFreeChart`).

## Dependencies and authorship

New helper modules in this development:

- `PullbackAffineSections`: the bijection
  `Γ(X, U) ⊗_{Γ(Y, V)} Γ(M, V) ≅ Γ(f^* M, U)` over affine opens;
- `FiniteFlatTrace`: free charts and the local trace.

Published modules by Worker 1223:

- `PullbackQuasicoherent`: pullbacks of quasi-coherent modules are quasi-coherent;
- `BasisHomGluing` and `BasicOpenHomGluing`: gluing morphisms of modules from maps on an
  affine basis;
- `FiniteFlatCohomologyRetractAssembly`: the retraction from a trace with
  `η ≫ t = d • 𝟙`.

Worker 1223 and Worker 281 agreed on the task split and the gluing interface.
