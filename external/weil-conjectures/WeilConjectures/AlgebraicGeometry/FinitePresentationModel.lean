/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import WeilConjectures.Compactification.FinitePresentation
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Immersion

/-!
# The finite presentation model system of a morphism of finite type

Let `S` be a quasi-compact quasi-separated scheme and `f : X ⟶ S` a morphism locally of finite
type with `X` quasi-compact and quasi-separated. Following the Nagata compactification
blueprint, we make the construction of the finite presentation model system `FP(X/S)` of
`f` explicit (Stacks Project Tags 01ZE, 01ZG and 09ZQ):

1. Choose Noetherian approximations `X = lim X_λ` and `S = lim S_μ`
   (`AlgebraicGeometry.Scheme.noetherianBaseSystem`). A *finite-stage datum*
   (`AlgebraicGeometry.Scheme.Hom.NoetherianStageData`) consists of stages `λ_X`, `λ_S` and a
   morphism `φ : X_{λ_X} ⟶ S_{λ_S}` compatible with `f`, such that the comparison
   `X ⟶ X_{λ_X} ×_{S_{λ_S}} S` is an immersion. One exists
   (`AlgebraicGeometry.Scheme.Hom.nonempty_noetherianStageData`).
2. The *immersion model* `Y^imm(X/S) = X_{λ_X} ×_{S_{λ_S}} S`
   (`AlgebraicGeometry.Scheme.Hom.immersionModel`) is of finite presentation over `S`, and
   `X` immerses into it.
3. An immersion with quasi-compact source is a closed immersion into a quasi-compact open
   `Y^cl` of its target (`AlgebraicGeometry.Scheme.Hom.closedShrink`).
4. `FP(X/S)` (`AlgebraicGeometry.Scheme.Hom.finitePresentationApproximation`) is the system of
   closed subschemes of `Y^cl(Y^imm(X/S))` cut out by the finite type subideals of the ideal
   of `X`.

-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

section ShrinkToClosed

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsImmersion f] [CompactSpace X]

/-- **The shrinking of an immersion to a closed immersion** `Y^cl(f)`: for an immersion
`f : X ⟶ Y` with `X` quasi-compact, a chosen quasi-compact open `W ⊆ Y` such that `f` factors
through a closed immersion `X ⟶ W` (selected by
`AlgebraicGeometry.Scheme.Hom.exists_isCompact_isClosedImmersion`).
(blueprint: `theorem-nagata-s-compactification-theorem--1`) -/
noncomputable def Scheme.Hom.closedShrink : Y.Opens :=
  f.exists_isCompact_isClosedImmersion.choose

/-- The closed immersion `X ⟶ Y^cl(f)` through which the immersion `f` factors.
(blueprint: `theorem-nagata-s-compactification-theorem--1`) -/
noncomputable def Scheme.Hom.toClosedShrink : X ⟶ f.closedShrink.toScheme :=
  f.exists_isCompact_isClosedImmersion.choose_spec.choose

/-- **The shrinking of an immersion to a closed immersion**: `Y^cl(f)` is a quasi-compact open of
`Y`, the morphism `X ⟶ Y^cl(f)` is a closed immersion, and it recovers `f` after composing with
the inclusion of `Y^cl(f)`; in particular `Y^cl(f)` contains the image of `f`.
(blueprint: `theorem-nagata-s-compactification-theorem--1`) -/
theorem Scheme.Hom.closedShrink_spec :
    IsCompact (f.closedShrink : Set Y) ∧ IsClosedImmersion f.toClosedShrink ∧
      f.toClosedShrink ≫ f.closedShrink.ι = f :=
  f.exists_isCompact_isClosedImmersion.choose_spec.choose_spec

lemma Scheme.Hom.isCompact_closedShrink : IsCompact (f.closedShrink : Set Y) :=
  f.closedShrink_spec.1

instance Scheme.Hom.isClosedImmersion_toClosedShrink : IsClosedImmersion f.toClosedShrink :=
  f.closedShrink_spec.2.1

@[reassoc (attr := simp)]
lemma Scheme.Hom.toClosedShrink_ι : f.toClosedShrink ≫ f.closedShrink.ι = f :=
  f.closedShrink_spec.2.2

instance Scheme.Hom.quasiCompact_closedShrink_ι [QuasiSeparatedSpace Y] :
    QuasiCompact f.closedShrink.ι :=
  f.closedShrink.quasiCompact_ι f.isCompact_closedShrink

lemma Scheme.Hom.range_subset_closedShrink : Set.range f ⊆ f.closedShrink := by
  rw [← Scheme.Opens.range_ι]
  rintro _ ⟨x, rfl⟩
  exact ⟨f.toClosedShrink x, by rw [← Scheme.Hom.comp_apply, f.toClosedShrink_ι]⟩

end ShrinkToClosed

section StageData

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- A **finite-stage datum** for a morphism `f : X ⟶ S`, relative to Noetherian approximations
`X = lim X_λ` and `S = lim S_μ`: stages `λ_X` and `λ_S`, a morphism
`φ : X_{λ_X} ⟶ S_{λ_S}` such that `X ⟶ S ⟶ S_{λ_S}` equals `X ⟶ X_{λ_X} ⟶ S_{λ_S}`, and such
that the induced comparison `X ⟶ X_{λ_X} ×_{S_{λ_S}} S` is an immersion.
(blueprint: `theorem-nagata-s-compactification-theorem--1`) -/
structure Scheme.Hom.NoetherianStageData (NX : X.NoetherianApproximation)
    (NS : S.NoetherianApproximation) where
  /-- The stage `λ_X` of the approximation of the source. -/
  iX : NX.I
  /-- The stage `λ_S` of the approximation of the target. -/
  iS : NS.I
  /-- The descended morphism `φ : X_{λ_X} ⟶ S_{λ_S}`. -/
  φ : NX.D.obj iX ⟶ NS.D.obj iS
  /-- The compatibility of `φ` with `f`. -/
  w : NX.π.app iX ≫ φ = f ≫ NS.π.app iS
  /-- The comparison `X ⟶ X_{λ_X} ×_{S_{λ_S}} S` is an immersion. -/
  isImmersion_lift : IsImmersion (pullback.lift (NX.π.app iX) f w)

attribute [instance] Scheme.Hom.NoetherianStageData.isImmersion_lift

namespace Scheme.Hom.NoetherianStageData

variable {f} {NX : X.NoetherianApproximation} {NS : S.NoetherianApproximation}
  (D : f.NoetherianStageData NX NS)

instance : LocallyOfFiniteType D.φ :=
  have : LocallyOfFiniteType (D.φ ≫ specULiftZIsTerminal.from _) := by
    rw [specULiftZIsTerminal.hom_ext (D.φ ≫ _) (specULiftZIsTerminal.from _)]
    infer_instance
  locallyOfFiniteType_of_comp D.φ (specULiftZIsTerminal.from _)

/-- The descended morphism is of finite presentation, since its source and target are of finite
type over `ℤ`. -/
instance : LocallyOfFinitePresentation D.φ :=
  LocallyOfFinitePresentation.iff_locallyOfFiniteType.mpr inferInstance

instance : QuasiCompact D.φ :=
  have : QuasiCompact (D.φ ≫ (NS.D.obj D.iS).toSpecΓ) :=
    (HasAffineProperty.iff_of_isAffine (P := @QuasiCompact)).mpr inferInstance
  QuasiCompact.of_comp D.φ (NS.D.obj D.iS).toSpecΓ

instance : QuasiSeparated D.φ := inferInstance

end Scheme.Hom.NoetherianStageData

/-- **Existence of a finite-stage datum**: if `X` and `S` are quasi-compact and quasi-separated
and `f : X ⟶ S` is locally of finite type, then for any Noetherian approximations of `X` and `S`
there is a finite-stage datum for `f`. The morphism `X ⟶ S ⟶ S_{λ_S}` descends to a stage of `X`
since `S_{λ_S}` is of finite presentation over `ℤ` (Stacks Project Tag 01ZC), and the comparison
with `X_{λ_X} ×_{S_{λ_S}} S` is an immersion for `λ_X` large (Stacks Project Tag 01ZE).
(blueprint: `theorem-nagata-s-compactification-theorem--1`) -/
theorem Scheme.Hom.nonempty_noetherianStageData [CompactSpace X] [QuasiSeparatedSpace X]
    [LocallyOfFiniteType f] (NX : X.NoetherianApproximation) (NS : S.NoetherianApproximation) :
    Nonempty (f.NoetherianStageData NX NS) := by
  obtain ⟨iS⟩ := IsCofiltered.nonempty (C := NS.I)
  have : LocallyOfFinitePresentation (specULiftZIsTerminal.from (NS.D.obj iS)) := inferInstance
  obtain ⟨j, g, hg, -⟩ := Scheme.exists_π_app_comp_eq_of_locallyOfFinitePresentation NX.D
    { app _ := specULiftZIsTerminal.from _ } (specULiftZIsTerminal.from (NS.D.obj iS))
    (Cone.mk X NX.π) NX.isLimit (f ≫ NS.π.app iS)
    (by ext; exact specULiftZIsTerminal.hom_ext _ _)
  obtain ⟨k, hk⟩ := f.exists_isImmersion_lift_noetherianApproximation NX
  let l := IsCofiltered.min j k
  have hw : NX.π.app l ≫ NX.D.map (IsCofiltered.minToLeft j k) ≫ g = f ≫ NS.π.app iS := by
    have h := NX.π.naturality (IsCofiltered.minToLeft j k)
    simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.id_comp] at h
    rw [← Category.assoc, ← h]
    exact hg
  refine ⟨⟨l, iS, NX.D.map (IsCofiltered.minToLeft j k) ≫ g, hw, ?_⟩⟩
  let M : pullback (NX.D.map (IsCofiltered.minToLeft j k) ≫ g) (NS.π.app iS) ⟶
      pullback (specULiftZIsTerminal.from (NX.D.obj k)) (specULiftZIsTerminal.from S) :=
    pullback.lift (pullback.fst _ _ ≫ NX.D.map (IsCofiltered.minToRight j k)) (pullback.snd _ _)
      (specULiftZIsTerminal.hom_ext _ _)
  have hM : pullback.lift (NX.π.app l) f hw ≫ M =
      pullback.lift (NX.π.app k) f (specULiftZIsTerminal.hom_ext _ _) := by
    apply pullback.hom_ext
    · simp only [M, Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc]
      simpa using (NX.π.naturality (IsCofiltered.minToRight j k)).symm
    · simp [M]
  have : IsImmersion (pullback.lift (NX.π.app l) f hw ≫ M) := by rw [hM]; exact hk
  exact IsImmersion.of_comp _ M

variable [CompactSpace X] [QuasiSeparatedSpace X] [CompactSpace S] [QuasiSeparatedSpace S]
  [LocallyOfFiniteType f]

/-- The chosen finite-stage datum of `f`, relative to the chosen Noetherian approximations
`AlgebraicGeometry.Scheme.noetherianBaseSystem` of `X` and of `S`.
(blueprint: `theorem-nagata-s-compactification-theorem--1`) -/
noncomputable def Scheme.Hom.noetherianStageData :
    f.NoetherianStageData X.noetherianBaseSystem S.noetherianBaseSystem :=
  Classical.choice (f.nonempty_noetherianStageData _ _)

/-- **The immersion model** `Y^imm(X/S) = X_{λ_X} ×_{S_{λ_S}} S` of a morphism `f : X ⟶ S`
locally of finite type between quasi-compact quasi-separated schemes, built from the chosen
finite-stage datum. (blueprint: `theorem-nagata-s-compactification-theorem--1`) -/
noncomputable def Scheme.Hom.immersionModel : Scheme.{u} :=
  pullback f.noetherianStageData.φ (S.noetherianBaseSystem.π.app f.noetherianStageData.iS)

/-- The structure morphism `Y^imm(X/S) ⟶ S`. (blueprint:
`theorem-nagata-s-compactification-theorem--1`) -/
noncomputable def Scheme.Hom.immersionModelHom : f.immersionModel ⟶ S :=
  pullback.snd _ _

/-- The immersion `i^imm : X ⟶ Y^imm(X/S)` over `S` induced by the compatibility of the
finite-stage datum. (blueprint: `theorem-nagata-s-compactification-theorem--1`) -/
noncomputable def Scheme.Hom.toImmersionModel : X ⟶ f.immersionModel :=
  pullback.lift _ f f.noetherianStageData.w

instance Scheme.Hom.isImmersion_toImmersionModel : IsImmersion f.toImmersionModel :=
  f.noetherianStageData.isImmersion_lift

@[reassoc (attr := simp)]
lemma Scheme.Hom.toImmersionModel_immersionModelHom :
    f.toImmersionModel ≫ f.immersionModelHom = f :=
  pullback.lift_snd _ _ _

instance Scheme.Hom.locallyOfFinitePresentation_immersionModelHom :
    LocallyOfFinitePresentation f.immersionModelHom :=
  MorphismProperty.pullback_snd _ _ inferInstance

instance Scheme.Hom.quasiCompact_immersionModelHom : QuasiCompact f.immersionModelHom :=
  MorphismProperty.pullback_snd _ _ inferInstance

instance Scheme.Hom.quasiSeparated_immersionModelHom : QuasiSeparated f.immersionModelHom :=
  MorphismProperty.pullback_snd _ _ inferInstance

/-- **The immersion model**: `Y^imm(X/S)` is quasi-compact, quasi-separated and locally of finite
presentation over `S`, and `i^imm : X ⟶ Y^imm(X/S)` is an immersion over `S`.
(blueprint: `theorem-nagata-s-compactification-theorem--1`) -/
theorem Scheme.Hom.immersionModel_spec :
    LocallyOfFinitePresentation f.immersionModelHom ∧ QuasiCompact f.immersionModelHom ∧
      QuasiSeparated f.immersionModelHom ∧ IsImmersion f.toImmersionModel ∧
      f.toImmersionModel ≫ f.immersionModelHom = f :=
  ⟨inferInstance, inferInstance, inferInstance, inferInstance,
    f.toImmersionModel_immersionModelHom⟩

end StageData

section FinitePresentationApproximation

variable {X S : Scheme.{u}} (f : X ⟶ S) [CompactSpace X] [QuasiSeparatedSpace X] [CompactSpace S]
  [QuasiSeparatedSpace S] [LocallyOfFiniteType f]

/-- The quasi-compact open `Y° = Y^cl(i^imm)` of the immersion model in which `X` is closed. -/
instance : QuasiSeparatedSpace f.immersionModel :=
  quasiSeparatedSpace_of_quasiSeparated f.immersionModelHom

noncomputable abbrev Scheme.Hom.closedModel : Scheme.{u} :=
  f.toImmersionModel.closedShrink.toScheme

/-- The structure morphism `Y° ⟶ S`. -/
noncomputable def Scheme.Hom.closedModelHom : f.closedModel ⟶ S :=
  f.toImmersionModel.closedShrink.ι ≫ f.immersionModelHom

instance : LocallyOfFinitePresentation f.closedModelHom := by
  unfold Scheme.Hom.closedModelHom; infer_instance

instance : QuasiCompact f.closedModelHom := by
  unfold Scheme.Hom.closedModelHom; infer_instance

instance : QuasiSeparated f.closedModelHom := by
  unfold Scheme.Hom.closedModelHom; infer_instance

@[reassoc (attr := simp)]
lemma Scheme.Hom.toClosedShrink_closedModelHom :
    f.toImmersionModel.toClosedShrink ≫ f.closedModelHom = f := by
  simp [Scheme.Hom.closedModelHom]

/-- **The finite presentation model system** `FP(X/S)` of a morphism `f : X ⟶ S` locally of
finite type between quasi-compact quasi-separated schemes: the closed immersion
`X ⟶ Y° = Y^cl(i^imm)` into the quasi-compact open of the immersion model, followed by the
system of closed subschemes of `Y°` cut out by the finite type subideals of the ideal of `X`
(`AlgebraicGeometry.Scheme.Hom.FinitePresentationApproximation.ofIsClosedImmersion`).
(blueprint: `theorem-nagata-s-compactification-theorem--1`) -/
noncomputable def Scheme.Hom.finitePresentationApproximation :
    f.FinitePresentationApproximation :=
  .ofIsClosedImmersion f.closedModelHom f.toImmersionModel.toClosedShrink
    f.toClosedShrink_closedModelHom

end FinitePresentationApproximation

end AlgebraicGeometry
