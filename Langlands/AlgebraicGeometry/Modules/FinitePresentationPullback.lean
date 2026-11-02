import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
import Langlands.AlgebraicGeometry.Picard.LineBundlePullback

/-! # Ordinary pullback of locally finitely presented module sheaves -/

noncomputable section

universe u v₁ v₂ u₁ u₂

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite

namespace Langlands.AlgebraicGeometry.Modules

section Map

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C}
  {R : Sheaf J RingCat.{u}} [HasSheafify J AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  {D : Type u₂} [Category.{v₂} D] {K : GrothendieckTopology D}
  {S : Sheaf K RingCat.{u}} [HasSheafify K AddCommGrpCat.{u}]
  [K.WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- A colimit preserving functor carrying the ring sheaf to the ring sheaf
preserves finiteness of a given free presentation. -/
instance finitePresentation_map {M : SheafOfModules.{u} R} (P : M.Presentation)
    [P.IsFinite] (F : SheafOfModules.{u} R ⥤ SheafOfModules.{u} S)
    [PreservesColimitsOfSize.{u, u} F] (η : SheafOfModules.unit S ≅ F.obj (.unit R)) :
    (P.map F η).IsFinite where
  isFiniteType_generators := ⟨by
    simpa only [SheafOfModules.Presentation.map_generators_I] using
      (inferInstance : Finite P.generators.I)⟩
  isFiniteType_relations := ⟨by
    simpa only [SheafOfModules.Presentation.map_relations_I] using
      (inferInstance : Finite P.relations.I)⟩

end Map

variable {X Y : Scheme.{u}}

/-- A free presentation on the over-site is a presentation on the open subscheme. -/
def presentationRestrictOfOver (M : X.Modules) (U : X.Opens)
    (P : (M.over U).Presentation) : (M.restrict U.ι).Presentation :=
  (P.map (Scheme.Modules.overEquiv U).functor
    (U.sheafOfModulesEquivOverUnit X.ringCatSheaf).symm).ofIsIso
      ((Scheme.Modules.overFunctorEquiv U).app M).hom

instance (M : X.Modules) (U : X.Opens) (P : (M.over U).Presentation) [P.IsFinite] :
    (presentationRestrictOfOver M U P).IsFinite := by
  dsimp [presentationRestrictOfOver]
  infer_instance

/-- A presentation on an open subscheme is a presentation on its over-site. -/
def presentationOverOfRestrict (M : X.Modules) (U : X.Opens)
    (P : (M.restrict U.ι).Presentation) : (M.over U).Presentation := by
  let E := Scheme.Modules.overEquiv U
  let e : E.inverse.obj (M.restrict U.ι) ≅ M.over U :=
    E.inverse.mapIso ((Scheme.Modules.overFunctorEquiv U).app M).symm ≪≫
      (E.unitIso.app (M.over U)).symm
  exact (P.map E.inverse (U.sheafOfModulesEquivOverInverseUnit X.ringCatSheaf).symm).ofIsIso
    e.hom

instance (M : X.Modules) (U : X.Opens) (P : (M.restrict U.ι).Presentation) [P.IsFinite] :
    (presentationOverOfRestrict M U P).IsFinite := by
  dsimp [presentationOverOfRestrict]
  infer_instance

/-- Actual pullback transports a given free presentation. -/
def presentationPullback (f : X ⟶ Y) {M : Y.Modules} (P : M.Presentation) :
    ((Scheme.Modules.pullback f).obj M).Presentation := by
  have : PreservesColimitsOfSize.{u, u} (Scheme.Modules.pullback f) := inferInstance
  exact P.map (Scheme.Modules.pullback f) (Langlands.Scheme.Modules.pullbackUnitIso f).symm

instance (f : X ⟶ Y) {M : Y.Modules} (P : M.Presentation) [P.IsFinite] :
    (presentationPullback f P).IsFinite := by
  dsimp [presentationPullback]
  infer_instance

/-- A finite presentation on a target open pulls back to its inverse image. -/
def presentationPullbackOver (f : X ⟶ Y) (M : Y.Modules) (U : Y.Opens)
    (P : (M.over U).Presentation) :
    (((Scheme.Modules.pullback f).obj M).over (f ⁻¹ᵁ U)).Presentation :=
  presentationOverOfRestrict _ _ <|
    (presentationPullback (f ∣_ U) (presentationRestrictOfOver M U P)).ofIsIso
      (Picard.restrictPullbackIso f U M).inv

instance (f : X ⟶ Y) (M : Y.Modules) (U : Y.Opens)
    (P : (M.over U).Presentation) [P.IsFinite] :
    (presentationPullbackOver f M U P).IsFinite := by
  dsimp [presentationPullbackOver]
  infer_instance

/-- Ordinary module pullback preserves local finite presentation over arbitrary schemes. -/
lemma isFinitePresentation_pullback (f : X ⟶ Y) (M : Y.Modules)
    [M.IsFinitePresentation] : ((Scheme.Modules.pullback f).obj M).IsFinitePresentation := by
  obtain ⟨q, hq⟩ := SheafOfModules.IsFinitePresentation.exists_quasicoherentData M
  let p : ((Scheme.Modules.pullback f).obj M).QuasicoherentData :=
    { I := q.I
      X := fun i => f ⁻¹ᵁ q.X i
      coversTop := by
        apply (_root_.Opens.coversTop_iff X _).2
        apply top_le_iff.mp
        intro x _
        have hx : f x ∈ ⨆ i, q.X i :=
          (_root_.Opens.coversTop_iff Y q.X).mp q.coversTop ▸
            (show f x ∈ (⊤ : Y.Opens) from trivial)
        obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hx
        exact Opens.mem_iSup.mpr ⟨i, hi⟩
      presentation := fun i => presentationPullbackOver f M (q.X i) (q.presentation i) }
  refine SheafOfModules.IsFinitePresentation.mk.{u, u, u}
    (M := (Scheme.Modules.pullback f).obj M) ⟨p, ?_⟩
  constructor
  intro i
  dsimp [p]
  infer_instance

end Langlands.AlgebraicGeometry.Modules

