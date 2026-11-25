/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
public import WeilConjectures.Mathlib.CategoryTheory.Limits.Shapes.Kernels

/-!
# Quasi-coherent sheaves and sheaves of finite presentation

## Main results

- `SheafOfModules.isQuasicoherent_free`: a free sheaf of modules is quasi-coherent.
- `SheafOfModules.isQuasicoherent_unit`: the unit sheaf of modules is quasi-coherent.
- `SheafOfModules.Presentation.isFinitePresentation`: a sheaf of modules with a finite global
  presentation is of finite presentation.
- `SheafOfModules.isFinitePresentation_pushforward_of_isLeftAdjoint`: finite presentation is
  preserved by pushforward along a continuous, cocontinuous left adjoint.
- `SheafOfModules.IsFinitePresentation.of_coversTop`: finite presentation is local.
- `SheafOfModules.Presentation.sigma`, `SheafOfModules.Presentation.isFinite_sigma`: a
  presentation of a coproduct of sheaves of modules from presentations of the summands, finite
  if the summands are finitely many and finitely presented.
-/

@[expose] public section

universe u v₁ u₁

open CategoryTheory Limits

variable {C : Type u₁} [Category.{v₁} C] [HasBinaryProducts C] {J : GrothendieckTopology C}
  {R : Sheaf J RingCat.{u}}
  [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ X, HasSheafify (J.over X) AddCommGrpCat.{u}]
  [∀ X, (J.over X).WEqualsLocallyBijective AddCommGrpCat.{u}]

namespace SheafOfModules

/-- A free sheaf of modules is quasi-coherent: it is the cokernel of the zero map from the free
sheaf of modules on no generators. -/
instance isQuasicoherent_free (I : Type u) : (free (R := R) I).IsQuasicoherent :=
  (presentationOfIsCokernelFree (ι := PEmpty.{u + 1}) (0 : free _ ⟶ free (R := R) I) (𝟙 _)
    (by simp) (CokernelCofork.IsColimit.ofId _ rfl)).isQuasicoherent

/-- The unit sheaf of modules is quasi-coherent. -/
instance isQuasicoherent_unit : (unit R).IsQuasicoherent :=
  (isQuasicoherent R).prop_of_iso (freeUniqueIso PUnit.{u + 1}) (isQuasicoherent_free _)

end SheafOfModules

namespace SheafOfModules

section FinitePresentation

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}
  [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  {C' : Type u₂} [Category.{v₂} C'] {J' : GrothendieckTopology C'} {S : Sheaf J' RingCat.{u}}
  [HasSheafify J' AddCommGrpCat.{u}] [J'.WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- The image of a finite presentation under a colimit-preserving functor sending the unit to
the unit is finite. -/
instance Presentation.isFinite_map {M : SheafOfModules.{u} R} (P : Presentation M) [P.IsFinite]
    (F : SheafOfModules.{u} R ⥤ SheafOfModules.{u} S) [PreservesColimitsOfSize.{u, u} F]
    (η : unit S ≅ F.obj (unit R)) : (P.map F η).IsFinite where
  isFiniteType_generators := ⟨by rw [Presentation.map_generators_I]; infer_instance⟩
  isFiniteType_relations := ⟨by rw [Presentation.map_relations_I]; infer_instance⟩

end FinitePresentation

section QuasicoherentDataShrink

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}
  [∀ X, HasSheafify (J.over X) AddCommGrpCat.{u}]
  [∀ X, (J.over X).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- Shrinking the indexing type of quasi-coherent data preserves being a finite presentation. -/
instance QuasicoherentData.isFinitePresentation_shrink {M : SheafOfModules.{u} R}
    (σ : QuasicoherentData.{w} M) [σ.IsFinitePresentation] : σ.shrink.IsFinitePresentation where
  isFinite_presentation i := by
    dsimp only [QuasicoherentData.shrink]
    infer_instance

/-- A sheaf of modules admitting quasi-coherent data which is a finite presentation, indexed by
a type in any universe, is of finite presentation. -/
lemma QuasicoherentData.isFinitePresentation {M : SheafOfModules.{u} R}
    (σ : QuasicoherentData.{w} M) [σ.IsFinitePresentation] : M.IsFinitePresentation :=
  ⟨σ.shrink, inferInstance⟩

end QuasicoherentDataShrink

section FinitePresentationQuasicoherentData

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}
  [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ X, HasSheafify (J.over X) AddCommGrpCat.{u}]
  [∀ X, (J.over X).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- The quasi-coherent data on the trivial cover attached to a finite presentation is a finite
presentation. -/
instance Presentation.isFinitePresentation_quasicoherentData [HasBinaryProducts C]
    {M : SheafOfModules.{u} R} (P : Presentation M) [P.IsFinite] :
    P.quasicoherentData.IsFinitePresentation where
  isFinite_presentation _ := Presentation.isFinite_map _ _ _

/-- A sheaf of modules with a finite global presentation is of finite presentation. -/
theorem Presentation.isFinitePresentation [HasBinaryProducts C] {M : SheafOfModules.{u} R}
    (P : Presentation M) [P.IsFinite] : M.IsFinitePresentation :=
  P.quasicoherentData.isFinitePresentation

end FinitePresentationQuasicoherentData

section FinitePresentationPushforward

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}
  [∀ X, HasSheafify (J.over X) AddCommGrpCat.{u}]
  [∀ X, (J.over X).WEqualsLocallyBijective AddCommGrpCat.{u}]
  {D : Type u₂} [Category.{v₂, u₂} D] {K : GrothendieckTopology D}
  {S : Sheaf K RingCat.{u}} [∀ (X : D), (K.over X).WEqualsLocallyBijective AddCommGrpCat]
  [∀ (X : D), HasSheafify (K.over X) AddCommGrpCat.{u}]
  (G : D ⥤ C) [G.IsContinuous K J] [G.IsCocontinuous K J]
  (φ : S ⟶ (G.sheafPushforwardContinuous RingCat.{u} K J).obj R)

/-- The pushforward of quasi-coherent data which is a finite presentation is a finite
presentation. -/
instance QuasicoherentData.isFinitePresentation_pushforward
    (η : (SheafOfModules.pushforward φ).obj (unit R) ≅ unit S)
    [∀ (X : D), (Over.post G).IsContinuous (K.over X) (J.over _)]
    (h : ∀ (X : D) (Y : C) (f : G.obj X ⟶ Y),
      PreservesColimitsOfSize.{u, u} <|
      SheafOfModules.pushforward.{u} (R := (R.over Y)) (F := Over.post (X := X) G ⋙ Over.map f)
        (((Over.forget X).sheafPushforwardContinuous RingCat.{u} (K.over X) K).map φ))
    {M : SheafOfModules.{u} R} (P : M.QuasicoherentData) [P.IsFinitePresentation] :
    (P.pushforward G φ η h).IsFinitePresentation where
  isFinite_presentation i := by
    have := h i.1 (P.X i.2.1) i.2.2
    exact Presentation.isFinite_map _ _ _

/-- The pushforward of a sheaf of modules of finite presentation along a continuous and
cocontinuous functor is of finite presentation. This is the finite-presentation analogue of
`SheafOfModules.isQuasicoherent_pushforward`. -/
lemma isFinitePresentation_pushforward (η : (pushforward φ).obj (unit R) ≅ unit S)
    [∀ (X : D), (Over.post G).IsContinuous (K.over X) (J.over _)]
    (h : ∀ (X : D) (Y : C) (f : G.obj X ⟶ Y),
      PreservesColimitsOfSize.{u, u} <|
      pushforward.{u} (R := (R.over Y)) (F := Over.post (X := X) G ⋙ Over.map f)
        (((Over.forget X).sheafPushforwardContinuous RingCat.{u} (K.over X) K).map φ))
    {M : SheafOfModules.{u} R} [IsFinitePresentation M] :
    IsFinitePresentation ((pushforward φ).obj M) := by
  obtain ⟨P, _⟩ := IsFinitePresentation.exists_quasicoherentData M
  exact (P.pushforward G φ η h).isFinitePresentation

/-- The pushforward of a sheaf of modules of finite presentation along a continuous,
cocontinuous left adjoint functor `G`, with `φ` an isomorphism, is of finite presentation. This
is the finite-presentation analogue of
`SheafOfModules.isQuasicoherent_pushforward_of_isLeftAdjoint`. -/
lemma isFinitePresentation_pushforward_of_isLeftAdjoint
    (η : (pushforward φ).obj (unit R) ≅ unit S) [G.IsLeftAdjoint] [IsIso φ]
    [∀ X, Functor.IsContinuous (Over.post (X := X) G) (K.over _) (J.over _)]
    [HasPullbacks C] [HasPullbacks D]
    {M : SheafOfModules.{u} R} [IsFinitePresentation M] :
    IsFinitePresentation ((pushforward φ).obj M) := by
  apply +allowSynthFailures isFinitePresentation_pushforward G φ η _
  intro X Y f
  let G' := Over.post (X := X) G ⋙ Over.map f
  have : G'.IsContinuous (K.over X) (J.over Y) := Functor.isContinuous_comp _ _ _ (J.over _) _
  have : G'.IsCocontinuous (K.over X) (J.over Y) := isCocontinuous_comp _ _ _ (J.over _)
  let a : S.over X ⟶
      (G'.sheafPushforwardContinuous RingCat.{u} (K.over X) (J.over Y)).obj (R.over Y) :=
    ((Over.forget X).sheafPushforwardContinuous RingCat.{u} (K.over X) K).map φ
  have : (pushforward.{u} a).IsLeftAdjoint := isLeftAdjoint_pushforward_of_isIso a
  infer_instance

end FinitePresentationPushforward

section bind

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C}
  [∀ X, HasSheafify (J.over X) AddCommGrpCat.{u}]
  [∀ X, (J.over X).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ X Y, HasSheafify ((J.over X).over Y) AddCommGrpCat.{u}]
  [∀ X Y, ((J.over X).over Y).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- Gluing finite presentations along a cover gives a finite presentation. -/
instance QuasicoherentData.isFinitePresentation_bind {R : Sheaf J RingCat.{u}}
    (M : SheafOfModules.{u} R) {I : Type u} (X : I → C) (hX : J.CoversTop X)
    (D : Π i, QuasicoherentData (M.over (X i))) [∀ i, (D i).IsFinitePresentation] :
    (QuasicoherentData.bind M X hX D).IsFinitePresentation where
  isFinite_presentation i := by
    dsimp only [QuasicoherentData.bind]
    infer_instance

/-- Being of finite presentation is local: if `M.over (X i)` is of finite presentation for a
family `X` covering the terminal object, then so is `M`. This is the finite-presentation
analogue of `SheafOfModules.IsQuasicoherent.of_coversTop`. -/
lemma IsFinitePresentation.of_coversTop {R : Sheaf J RingCat.{u}}
    (M : SheafOfModules.{u} R) {I : Type u}
    (X : I → C) (hX : J.CoversTop X) [∀ i, IsFinitePresentation (M.over (X i))] :
    IsFinitePresentation M := by
  choose D hD using fun i ↦ IsFinitePresentation.exists_quasicoherentData (M.over (X i))
  exact (QuasicoherentData.bind M X hX D).isFinitePresentation

end bind

section Sigma

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}
  [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- **A presentation of a coproduct.** Presentations of the sheaves of modules `M i` give a
presentation of `∐ M`, with generators and relations the disjoint unions of those of the `M i`:
the cokernel of `∐ free (relations i) ⟶ ∐ free (generators i)` is `∐ M`. -/
noncomputable def Presentation.sigma {ι : Type u} (M : ι → SheafOfModules.{u} R)
    (P : ∀ i, (M i).Presentation) : (∐ M).Presentation :=
  letI eI := (freeFunctor (R := R)).mapIso (Types.coproductIso fun i ↦ (P i).generators.I).symm ≪≫
    PreservesCoproduct.iso (freeFunctor (R := R)) fun i ↦ (P i).generators.I
  letI eJ := (freeFunctor (R := R)).mapIso (Types.coproductIso fun i ↦ (P i).relations.I).symm ≪≫
    PreservesCoproduct.iso (freeFunctor (R := R)) fun i ↦ (P i).relations.I
  presentationOfIsCokernelFree
    (eJ.hom ≫ Limits.Sigma.map (fun i ↦ (freeHomEquiv _).symm (P i).relations.s ≫ kernel.ι _) ≫
      eI.inv)
    (eI.hom ≫ Limits.Sigma.map fun i ↦ (P i).generators.π) (by
      simp only [Category.assoc, Iso.inv_hom_id_assoc]
      rw [Sigma.map_comp_map]
      convert comp_zero
      exact Sigma.hom_ext _ _ fun i ↦ by simp)
    (IsCokernel.ofIso _ (isColimitCokernelCoforkSigmaMap _ _ _ fun i ↦ (P i).isColimit) _ eJ.symm
      eI.symm (Iso.refl _) (by simp) (by simp))

instance Presentation.isFinite_sigma {ι : Type u} [Finite ι] (M : ι → SheafOfModules.{u} R)
    (P : ∀ i, (M i).Presentation) [∀ i, (P i).IsFinite] : (Presentation.sigma M P).IsFinite where
  isFiniteType_generators := ⟨inferInstanceAs (Finite (Σ i, (P i).generators.I))⟩
  isFiniteType_relations := ⟨inferInstanceAs (Finite (Σ i, (P i).relations.I))⟩

end Sigma

end SheafOfModules
