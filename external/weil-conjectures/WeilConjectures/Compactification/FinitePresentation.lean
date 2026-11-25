/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import WeilConjectures.Compactification.BaseChange
public import WeilConjectures.Compactification.Noetherian
public import WeilConjectures.Mathlib.AlgebraicGeometry.AffineTransitionLimit

/-!

# Nagata compactification for a morphism of finite presentation

This file proves **Nagata's compactification theorem for a separated, quasi-compact morphism of
finite presentation over a quasi-compact quasi-separated base**
(`AlgebraicGeometry.nagataCompactification_of_locallyOfFinitePresentation`): such a morphism
factors as an open immersion followed by a proper morphism.

The Noetherian hypothesis on the base of
`AlgebraicGeometry.nagataCompactification_of_isNoetherian` is removed by absolute Noetherian
approximation. Writing the qcqs base `S` as a cofiltered limit `S = lim Dᵢ` of Noetherian
stages with affine transition maps (Stacks Tag 01ZA,
`AlgebraicGeometry.Scheme.nonempty_noetherianApproximation`), a separated, quasi-compact
morphism `f : X ⟶ S` of finite presentation descends to a morphism `p : Y ⟶ Dᵢ` with the same
three properties over one of the stages (Stacks Tag 01ZQ,
`AlgebraicGeometry.Scheme.exists_isPullback_of_finitePresentation_of_isSeparated`). The stage
`Dᵢ` is Noetherian, so `p` has a compactification; base changing it back along `S ⟶ Dᵢ`
(`AlgebraicGeometry.HasCompactification.of_isPullback`) compactifies `f`.

The blueprint's compactification datum for `Rf_!` asks for more than mere existence: the
proper structure morphism `g` of the compactification must itself be *locally of finite
presentation*. Over a locally Noetherian base this is automatic, since `g` is proper, hence
locally of finite type (`AlgebraicGeometry.Compactification.locallyOfFinitePresentation_g`).
Over a general quasi-compact quasi-separated base we re-run the approximation argument above
while carrying this extra property: the compactification produced over the Noetherian stage
`Dᵢ` is of finite presentation, and its structure morphism stays so after base change to `S`,
because `AlgebraicGeometry.LocallyOfFinitePresentation` is stable under base change.

## Main results

- `AlgebraicGeometry.nagataCompactification_of_locallyOfFinitePresentation`: a separated,
  quasi-compact morphism of finite presentation to a quasi-compact quasi-separated scheme
  admits a compactification.
- `AlgebraicGeometry.Compactification.locallyOfFinitePresentation_g`: over a locally
  Noetherian base, the structure morphism of any compactification is locally of finite
  presentation.
- `AlgebraicGeometry.exists_compactification_locallyOfFinitePresentation`: such a morphism
  admits a compactification whose structure morphism is locally of finite presentation.
- `AlgebraicGeometry.finitelyPresentedCompactification`: a choice of such a compactification.

-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

/-- **Nagata compactification for a morphism of finite presentation** (blueprint:
`lemma:nagata-final-basechanged-compactification`).

The base is written as a cofiltered limit of Noetherian stages by absolute Noetherian
approximation, `f` is descended to one of the stages, compactified there by
`AlgebraicGeometry.nagataCompactification_of_isNoetherian` and the compactification is base
changed back to `S`. -/
theorem nagataCompactification_of_locallyOfFinitePresentation {X S : Scheme.{u}} (f : X ⟶ S)
    [CompactSpace S] [QuasiSeparatedSpace S] [IsSeparated f] [LocallyOfFinitePresentation f]
    [QuasiCompact f] : HasCompactification f := by
  obtain ⟨N⟩ := S.nonempty_noetherianApproximation
  obtain ⟨i, Y, p, hp₁, hp₂, hp₃, h, H⟩ :=
    Scheme.exists_isPullback_of_finitePresentation_of_isSeparated N.isLimit f
  have := hp₁; have := hp₂; have := hp₃
  have : HasCompactification p := nagataCompactification_of_isNoetherian p
  exact HasCompactification.of_isPullback H

/-- **Over a locally Noetherian base the structure morphism of a compactification is locally
of finite presentation.**

It is proper, hence locally of finite type, and over a locally Noetherian base locally of
finite type implies locally of finite presentation. -/
theorem Compactification.locallyOfFinitePresentation_g {X S : Scheme.{u}} {f : X ⟶ S}
    [IsLocallyNoetherian S] (c : Compactification f) : LocallyOfFinitePresentation c.g :=
  inferInstance

/-- **A compactification whose structure morphism is of finite presentation** (blueprint:
`proper_base_change.tex`, §A43, `BA43-RAW-DATA`).

This is `AlgebraicGeometry.nagataCompactification_of_locallyOfFinitePresentation` with the
finite presentation of the structure morphism carried along: `f` is descended to a Noetherian
stage `Dᵢ` of an absolute Noetherian approximation of `S`, compactified there — where the
structure morphism is automatically locally of finite presentation by
`AlgebraicGeometry.Compactification.locallyOfFinitePresentation_g` — and the result is base
changed back to `S`, which preserves finite presentation. -/
theorem exists_compactification_locallyOfFinitePresentation {X S : Scheme.{u}} (f : X ⟶ S)
    [IsSeparated f] [LocallyOfFinitePresentation f] [QuasiCompact f] [CompactSpace S]
    [QuasiSeparatedSpace S] :
    ∃ c : Compactification f, LocallyOfFinitePresentation c.g := by
  obtain ⟨N⟩ := S.nonempty_noetherianApproximation
  obtain ⟨i, Y, p, hp₁, hp₂, hp₃, h, H⟩ :=
    Scheme.exists_isPullback_of_finitePresentation_of_isSeparated N.isLimit f
  have := hp₁; have := hp₂; have := hp₃
  obtain ⟨c⟩ := (nagataCompactification_of_isNoetherian p).nonempty_compactification
  have : LocallyOfFinitePresentation c.g := c.locallyOfFinitePresentation_g
  refine ⟨Compactification.ofIsPullback H c, ?_⟩
  rw [Compactification.ofIsPullback_g]
  infer_instance

/-- A choice of compactification with structure morphism locally of finite presentation, for a
separated, quasi-compact morphism of finite presentation over a quasi-compact quasi-separated
base. Its defining property is
`AlgebraicGeometry.locallyOfFinitePresentation_finitelyPresentedCompactification_g`. -/
noncomputable def finitelyPresentedCompactification {X S : Scheme.{u}} (f : X ⟶ S)
    [IsSeparated f] [LocallyOfFinitePresentation f] [QuasiCompact f] [CompactSpace S]
    [QuasiSeparatedSpace S] : Compactification f :=
  (exists_compactification_locallyOfFinitePresentation f).choose

/-- The structure morphism of
`AlgebraicGeometry.finitelyPresentedCompactification` is locally of finite presentation. -/
instance locallyOfFinitePresentation_finitelyPresentedCompactification_g {X S : Scheme.{u}}
    (f : X ⟶ S) [IsSeparated f] [LocallyOfFinitePresentation f] [QuasiCompact f]
    [CompactSpace S] [QuasiSeparatedSpace S] :
    LocallyOfFinitePresentation (finitelyPresentedCompactification f).g :=
  (exists_compactification_locallyOfFinitePresentation f).choose_spec

/-! ### The explicit final assembly

The proof of `AlgebraicGeometry.nagataCompactification_of_locallyOfFinitePresentation` makes
three selections: an absolute Noetherian approximation of the base, a separated descended model
over one of its stages, and a compactification of that model. We record them as definitions,
following the blueprint's final assembly. -/

section FinalAssembly

/-- **The selected Noetherian base system** `N(S)` of a quasi-compact quasi-separated scheme:
a chosen absolute Noetherian approximation (Stacks Project Tag 01ZA), selected from
`AlgebraicGeometry.Scheme.nonempty_noetherianApproximation`.
(blueprint: `theorem-nagata-s-compactification-theorem--1`) -/
noncomputable def Scheme.noetherianBaseSystem (S : Scheme.{u}) [CompactSpace S]
    [QuasiSeparatedSpace S] : S.NoetherianApproximation :=
  Classical.choice S.nonempty_noetherianApproximation

/-- **Properties of the selected Noetherian base system**: every stage is Noetherian, quasi-compact
and locally of finite type over `ℤ`, every transition morphism is affine, and the comparison of
`S` with the limit of the stages is an isomorphism (`S` is a limit of the stages).
(blueprint: `theorem-nagata-s-compactification-theorem--1`) -/
theorem Scheme.noetherianBaseSystem_spec (S : Scheme.{u}) [CompactSpace S]
    [QuasiSeparatedSpace S] :
    (∀ i, IsNoetherian (S.noetherianBaseSystem.D.obj i)) ∧
      (∀ i, LocallyOfFiniteType (specULiftZIsTerminal.from (S.noetherianBaseSystem.D.obj i))) ∧
      (∀ {i j} (g : i ⟶ j), IsAffineHom (S.noetherianBaseSystem.D.map g)) ∧
      Nonempty (IsLimit (Cone.mk S S.noetherianBaseSystem.π)) :=
  ⟨fun _ ↦ inferInstance, fun _ ↦ inferInstance, fun _ ↦ inferInstance,
    ⟨S.noetherianBaseSystem.isLimit⟩⟩


variable {X S : Scheme.{u}} (f : X ⟶ S) [CompactSpace S] [QuasiSeparatedSpace S]
  [IsSeparated f] [LocallyOfFinitePresentation f] [QuasiCompact f]

lemma exists_descendedModel :
    ∃ (i : S.noetherianBaseSystem.I) (Y : Scheme.{u}) (p : Y ⟶ S.noetherianBaseSystem.D.obj i)
      (_ : LocallyOfFinitePresentation p) (_ : QuasiCompact p) (_ : IsSeparated p) (h : X ⟶ Y),
      IsPullback h f p (S.noetherianBaseSystem.π.app i) :=
  Scheme.exists_isPullback_of_finitePresentation_of_isSeparated
    S.noetherianBaseSystem.isLimit f

/-- The selected stage `λ_Y` of the Noetherian base system over which `f` descends
(blueprint: `theorem-nagata-s-compactification-theorem--1`). -/
noncomputable def descendedModelStage : S.noetherianBaseSystem.I :=
  (exists_descendedModel f).choose

/-- **The separated descended model** `Y_λ ⟶ S_λ` of `f` over the selected stage
(Stacks Project Tag 01ZQ; blueprint: `theorem-nagata-s-compactification-theorem--1`). -/
noncomputable def descendedModel : Scheme.{u} :=
  (exists_descendedModel f).choose_spec.choose

/-- The structure morphism `Y_λ ⟶ S_λ` of the separated descended model
(blueprint: `theorem-nagata-s-compactification-theorem--1`). -/
noncomputable def descendedModelHom :
    descendedModel f ⟶ S.noetherianBaseSystem.D.obj (descendedModelStage f) :=
  (exists_descendedModel f).choose_spec.choose_spec.choose

/-- The comparison morphism `X ⟶ Y_λ` exhibiting `f` as the base change of the descended model
(blueprint: `theorem-nagata-s-compactification-theorem--1`). -/
noncomputable def toDescendedModel : X ⟶ descendedModel f :=
  (exists_descendedModel f).choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec
    |>.choose

instance : LocallyOfFinitePresentation (descendedModelHom f) :=
  (exists_descendedModel f).choose_spec.choose_spec.choose_spec.choose

instance : QuasiCompact (descendedModelHom f) :=
  (exists_descendedModel f).choose_spec.choose_spec.choose_spec.choose_spec.choose

instance : IsSeparated (descendedModelHom f) :=
  (exists_descendedModel f).choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose

/-- `f` is the base change of the descended model along `S ⟶ S_λ`. -/
theorem isPullback_descendedModel :
    IsPullback (toDescendedModel f) f (descendedModelHom f)
      (S.noetherianBaseSystem.π.app (descendedModelStage f)) :=
  (exists_descendedModel f).choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec
    |>.choose_spec

/-- The base-change comparison `ε_Y : Y_λ ×_{S_λ} S ⟶ X` of the descended model
(blueprint: `theorem-nagata-s-compactification-theorem--1`). -/
noncomputable def descendedModelIso :
    pullback (descendedModelHom f) (S.noetherianBaseSystem.π.app (descendedModelStage f)) ≅ X :=
  (isPullback_descendedModel f).isoPullback.symm

@[reassoc (attr := simp)]
lemma descendedModelIso_hom_comp :
    (descendedModelIso f).hom ≫ f = pullback.snd _ _ := by
  simp [descendedModelIso]

/-- **Properties of the descended model**: `Y_λ ⟶ S_λ` is separated, quasi-compact and locally
of finite presentation, the stage `S_λ` is Noetherian, and `ε_Y` is an isomorphism over `S`.
(blueprint: `theorem-nagata-s-compactification-theorem--1`) -/
theorem descendedModel_spec :
    LocallyOfFinitePresentation (descendedModelHom f) ∧ QuasiCompact (descendedModelHom f) ∧
      IsSeparated (descendedModelHom f) ∧
      IsNoetherian (S.noetherianBaseSystem.D.obj (descendedModelStage f)) ∧
      IsIso (descendedModelIso f).hom ∧ (descendedModelIso f).hom ≫ f = pullback.snd _ _ :=
  ⟨inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    descendedModelIso_hom_comp f⟩


/-- **The selected Noetherian compactification** `C_{Y,λ}` of the descended model, given by the
recursive Noetherian construction `AlgebraicGeometry.noetherianCompactification`.
(blueprint: `theorem-nagata-s-compactification-theorem--1`) -/
noncomputable def descendedModelCompactification : Compactification (descendedModelHom f) :=
  noetherianCompactification (descendedModelHom f)

/-- **The selected Noetherian compactification is a compactification** of the descended model:
an open immersion followed by a proper morphism, composing to `Y_λ ⟶ S_λ`.
(blueprint: `theorem-nagata-s-compactification-theorem--1`) -/
theorem descendedModelCompactification_spec :
    IsOpenImmersion (descendedModelCompactification f).i ∧
      IsProper (descendedModelCompactification f).g ∧
      (descendedModelCompactification f).i ≫ (descendedModelCompactification f).g =
        descendedModelHom f :=
  ⟨(descendedModelCompactification f).isOpenImmersion,
    (descendedModelCompactification f).isProper, (descendedModelCompactification f).comm.symm⟩


/-- **The base-changed compactification** `C^fp(X/S)`: the base change of the Noetherian
compactification of the descended model along `S ⟶ S_λ`, composed with the identification
`X ≅ Y_λ ×_{S_λ} S`. It is a compactification of `f`; in particular `f` is compactifiable
(blueprint: `theorem-nagata-s-compactification-theorem--1`,
`theorem-nagata-s-compactification-theorem--1`). -/
noncomputable def finitePresentationCompactification : Compactification f :=
  (descendedModelCompactification f).ofIsPullback (isPullback_descendedModel f)

end FinalAssembly

end AlgebraicGeometry
