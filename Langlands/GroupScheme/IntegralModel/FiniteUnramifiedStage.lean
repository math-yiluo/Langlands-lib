import Langlands.GroupScheme.Descent.FiniteUnramifiedSpectralModel
import Langlands.GroupScheme.Descent.FiniteUnramifiedIso
import Langlands.GroupScheme.IntegralModel.Iso
import Langlands.AlgebraicGeometry.SchemeFlatPropertyDescent

/-! # Finite unramified stages of specified smooth integral models -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Langlands.LocalGalois Langlands.LocalGalois.Separable

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 100000

namespace Langlands.GroupScheme.Descent.FiniteUnramified

private def squareComparison {S T U V : Scheme.{u}}
    (f : T ⟶ S) (q : V ⟶ T) (g : U ⟶ S) (p : V ⟶ U)
    (r : V ⟶ S) (hf : q ≫ f = r) (hg : p ≫ g = r)
    (H : GroupScheme S) :
    (baseChange q).obj ((baseChange f).obj H) ≅
      (baseChange p).obj ((baseChange g).obj H) :=
  pullbackComparison f q r hf H ≪≫ (pullbackComparison g p r hg H).symm

@[reassoc] private theorem squareComparison_fst {S T U V : Scheme.{u}}
    (f : T ⟶ S) (q : V ⟶ T) (g : U ⟶ S) (p : V ⟶ U)
    (r : V ⟶ S) (hf : q ≫ f = r) (hg : p ≫ g = r)
    (H : GroupScheme S) :
    (squareComparison f q g p r hf hg H).hom.hom.hom.left ≫
        pullback.fst ((baseChange g).obj H).X.hom p ≫ pullback.fst H.X.hom g =
      pullback.fst ((baseChange f).obj H).X.hom q ≫ pullback.fst H.X.hom f := by
  simp only [squareComparison, Iso.trans_hom, Iso.symm_hom, Grp.comp_hom_hom,
    Over.comp_left, Category.assoc, pullbackComparison_inv_fst,
    pullbackComparison_hom_fst]

@[reassoc] private theorem map_fst {S T : Scheme.{u}} (p : T ⟶ S)
    {G H : GroupScheme S} (f : G ⟶ H) :
    ((baseChange p).map f).hom.hom.left ≫ pullback.fst H.X.hom p =
      pullback.fst G.X.hom p ≫ f.hom.hom.left :=
  pullback.lift_fst _ _ _

variable (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]

local instance integralStageNormedField : NontriviallyNormedField F := localNormedField F
local instance integralStageUltrametric : IsUltrametricDist F := localNormedField_ultrametric F
local instance integralStageComplete : CompleteSpace F := localNormedField_complete F

/-- The integer inclusion induced by an inclusion of intermediate fields. -/
def stageIntegerInclusion {E E' : IntermediateField F (SeparableClosure F)}
    (h : E ≤ E') : extensionIntegers F E →+* extensionIntegers F E' where
  toFun x := ⟨IntermediateField.inclusion h x, by
    change spectralNorm F E' (IntermediateField.inclusion h (x : E)) ≤ 1
    rw [spectralNorm.eq_of_tower (L := SeparableClosure F)]
    change spectralNorm F (SeparableClosure F) (algebraMap E (SeparableClosure F) (x : E)) ≤ 1
    rw [← spectralNorm.eq_of_tower (K := F) (L := SeparableClosure F) (x : E)]
    exact x.property⟩
  map_zero' := rfl
  map_one' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl

/-- The spectrum of the actual inclusion of the finite integer rings. -/
abbrev stageIntegerMap {E E' : IntermediateField F (SeparableClosure F)}
    (h : E ≤ E') :
    Spec (CommRingCat.of (extensionIntegers F E')) ⟶
      Spec (CommRingCat.of (extensionIntegers F E)) :=
  Spec.map (CommRingCat.ofHom (stageIntegerInclusion F h))

@[reassoc]
theorem stageIntegerMap_generic {E E' : IntermediateField F (SeparableClosure F)}
    (h : E ≤ E') :
    Spec.algebraMap (extensionIntegers F E') E' ≫ stageIntegerMap F h =
      fieldSpecMap F h ≫ Spec.algebraMap (extensionIntegers F E) E := by
  rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
    ← CommRingCat.ofHom_comp]
  rfl

@[reassoc]
theorem stageIntegerMap_inertia {E E' : IntermediateField F (SeparableClosure F)}
    (h : E ≤ E') (hE' : E' ≤ inertiaFixedField F) :
    spectralIntegerMap F E' hE' ≫ stageIntegerMap F h =
      spectralIntegerMap F E (h.trans hE') := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  rfl

@[reassoc]
theorem spectralIntegerMap_generic
    (E : IntermediateField F (SeparableClosure F)) (hE : E ≤ inertiaFixedField F) :
    Spec.algebraMap (fixedFieldIntegers F) (inertiaFixedField F) ≫
        spectralIntegerMap F E hE =
      fieldSpecMap F hE ≫ Spec.algebraMap (extensionIntegers F E) E := by
  rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
    ← CommRingCat.ofHom_comp]
  rfl

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
@[reassoc]
theorem fieldSpecMap_base {E E' : IntermediateField F (SeparableClosure F)}
    (h : E ≤ E') :
    fieldSpecMap F h ≫ Spec.algebraMap F E = Spec.algebraMap F E' := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  rfl


/-- The integral pullback comparison for an enlarged finite field. -/
abbrev stageIntegralComparison
    {E E' : IntermediateField F (SeparableClosure F)}
    (h : E ≤ E') (hE : E ≤ inertiaFixedField F) (hE' : E' ≤ inertiaFixedField F)
    (H : GroupScheme (Spec (CommRingCat.of (extensionIntegers F E)))) :
    (baseChange (spectralIntegerMap F E' hE')).obj
        ((baseChange (stageIntegerMap F h)).obj H) ≅
      (baseChange (spectralIntegerMap F E hE)).obj H :=
  pullbackComparison (stageIntegerMap F h) (spectralIntegerMap F E' hE')
    (spectralIntegerMap F E hE) (stageIntegerMap_inertia F h hE') H

@[reassoc (attr := simp)]
theorem stageIntegralComparison_fst
    {E E' : IntermediateField F (SeparableClosure F)}
    (h : E ≤ E') (hE : E ≤ inertiaFixedField F) (hE' : E' ≤ inertiaFixedField F)
    (H : GroupScheme (Spec (CommRingCat.of (extensionIntegers F E)))) :
    (stageIntegralComparison F h hE hE' H).hom.hom.hom.left ≫
        pullback.fst H.X.hom (spectralIntegerMap F E hE) =
      pullback.fst ((baseChange (stageIntegerMap F h)).obj H).X.hom
        (spectralIntegerMap F E' hE') ≫ pullback.fst H.X.hom (stageIntegerMap F h) := by
  simp only [stageIntegralComparison, pullbackComparison_hom_fst]


/-- Compare the generic fibre of the inertia integer extension with the field extension. -/
abbrev inertiaGenericSquare
    (E : IntermediateField F (SeparableClosure F)) (hE : E ≤ inertiaFixedField F)
    (H : GroupScheme (Spec (CommRingCat.of (extensionIntegers F E)))) :
    (baseChange (Spec.algebraMap (fixedFieldIntegers F) (inertiaFixedField F))).obj
        ((baseChange (spectralIntegerMap F E hE)).obj H) ≅
      (baseChange (fieldSpecMap F hE)).obj
        ((baseChange (Spec.algebraMap (extensionIntegers F E) E)).obj H) :=
  squareComparison (spectralIntegerMap F E hE)
    (Spec.algebraMap (fixedFieldIntegers F) (inertiaFixedField F))
    (Spec.algebraMap (extensionIntegers F E) E) (fieldSpecMap F hE)
    (fieldSpecMap F hE ≫ Spec.algebraMap (extensionIntegers F E) E)
    (spectralIntegerMap_generic F E hE) rfl H

@[reassoc]
theorem inertiaGenericSquare_fst
    (E : IntermediateField F (SeparableClosure F)) (hE : E ≤ inertiaFixedField F)
    (H : GroupScheme (Spec (CommRingCat.of (extensionIntegers F E)))) :
    (inertiaGenericSquare F E hE H).hom.hom.hom.left ≫
        pullback.fst ((baseChange (Spec.algebraMap (extensionIntegers F E) E)).obj H).X.hom
          (fieldSpecMap F hE) ≫ pullback.fst H.X.hom
            (Spec.algebraMap (extensionIntegers F E) E) =
      pullback.fst ((baseChange (spectralIntegerMap F E hE)).obj H).X.hom
        (Spec.algebraMap (fixedFieldIntegers F) (inertiaFixedField F)) ≫
          pullback.fst H.X.hom (spectralIntegerMap F E hE) := by
  simp only [inertiaGenericSquare, squareComparison, Iso.trans_hom, Iso.symm_hom,
    Grp.comp_hom_hom, Over.comp_left, Category.assoc, pullbackComparison_inv_fst,
    pullbackComparison_hom_fst]


/-- Compare the generic fibre of a finite integer extension with its field extension. -/
abbrev enlargementGenericSquare
    {E E' : IntermediateField F (SeparableClosure F)} (h : E ≤ E')
    (H : GroupScheme (Spec (CommRingCat.of (extensionIntegers F E)))) :
    (baseChange (Spec.algebraMap (extensionIntegers F E') E')).obj
        ((baseChange (stageIntegerMap F h)).obj H) ≅
      (baseChange (fieldSpecMap F h)).obj
        ((baseChange (Spec.algebraMap (extensionIntegers F E) E)).obj H) :=
  squareComparison (stageIntegerMap F h) (Spec.algebraMap (extensionIntegers F E') E')
    (Spec.algebraMap (extensionIntegers F E) E) (fieldSpecMap F h)
    (fieldSpecMap F h ≫ Spec.algebraMap (extensionIntegers F E) E)
    (stageIntegerMap_generic F h) rfl H

@[reassoc]
theorem enlargementGenericSquare_fst
    {E E' : IntermediateField F (SeparableClosure F)} (h : E ≤ E')
    (H : GroupScheme (Spec (CommRingCat.of (extensionIntegers F E)))) :
    (enlargementGenericSquare F h H).hom.hom.hom.left ≫
        pullback.fst ((baseChange (Spec.algebraMap (extensionIntegers F E) E)).obj H).X.hom
          (fieldSpecMap F h) ≫ pullback.fst H.X.hom
            (Spec.algebraMap (extensionIntegers F E) E) =
      pullback.fst ((baseChange (stageIntegerMap F h)).obj H).X.hom
        (Spec.algebraMap (extensionIntegers F E') E') ≫
          pullback.fst H.X.hom (stageIntegerMap F h) := by
  simp only [enlargementGenericSquare, squareComparison, Iso.trans_hom, Iso.symm_hom,
    Grp.comp_hom_hom, Over.comp_left, Category.assoc, pullbackComparison_inv_fst,
    pullbackComparison_hom_fst]


variable {G : GroupScheme (Spec (CommRingCat.of F))}
    (N : IntegralModel (fixedFieldIntegers F) (inertiaFixedField F)
      ((baseChange (Spec.algebraMap F (inertiaFixedField F))).obj G))

include N in
private theorem originalGroup_affine : IsAffineHom G.X.hom := by
  let : IsAffineHom N.genericFibre.X.hom :=
    MorphismProperty.pullback_snd _ _ N.affine
  have hu : IsAffineHom
      ((baseChange (Spec.algebraMap F (inertiaFixedField F))).obj G).X.hom := by
    rw [← Over.w N.genericIso.inv.hom.hom]
    infer_instance
  exact MorphismProperty.of_pullback_snd_of_descendsAlong
    (P := @IsAffineHom) (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact)
    (f := G.X.hom) (g := Spec.algebraMap F (inertiaFixedField F))
    ⟨⟨(fieldExtension_fpqc F (inertiaFixedField F)).1,
      (fieldExtension_fpqc F (inertiaFixedField F)).2.1⟩,
      (fieldExtension_fpqc F (inertiaFixedField F)).2.2⟩ hu

variable (D : SpectralGroupModel F N.group)

/-- The finite group model and the prescribed generic identification give a
specified isomorphism of generic fibres over the inertia fixed field. -/
def stageGenericComparison :
    (baseChange (fieldSpecMap F D.inertia)).obj
        ((baseChange (Spec.algebraMap F D.field)).obj G) ≅
      (baseChange (fieldSpecMap F D.inertia)).obj
        ((baseChange (Spec.algebraMap (extensionIntegers F D.field) D.field)).obj D.group) :=
  pullbackComparison _ _ _ (fieldSpecMap_base F D.inertia) G ≪≫
    N.genericIso.symm ≪≫
    (baseChange (Spec.algebraMap (fixedFieldIntegers F) (inertiaFixedField F))).mapIso D.iso ≪≫
    inertiaGenericSquare F D.field D.inertia D.group

private theorem stageSource_affine :
    IsAffineHom ((baseChange (Spec.algebraMap F D.field)).obj G).X.hom := by
  let : IsAffineHom G.X.hom := originalGroup_affine F N
  exact MorphismProperty.pullback_snd _ _ inferInstance

private theorem stageTarget_smooth :
    Smooth
      ((baseChange (Spec.algebraMap (extensionIntegers F D.field) D.field)).obj D.group).X.hom :=
  MorphismProperty.pullback_snd _ _ D.smooth

/-- Existence of a finite enlargement retaining the prescribed generic map. -/
theorem nonempty_modelIsoStage :
    Nonempty (IsoStage F D.field D.inertia
      (G := (baseChange (Spec.algebraMap F D.field)).obj G)
      (H := (baseChange (Spec.algebraMap (extensionIntegers F D.field) D.field)).obj D.group)
      (stageGenericComparison F N D)) := by
  let : FiniteDimensional F D.field := D.finite
  let : IsAffineHom ((baseChange (Spec.algebraMap F D.field)).obj G).X.hom :=
    stageSource_affine F N D
  let : Smooth
      ((baseChange (Spec.algebraMap (extensionIntegers F D.field) D.field)).obj D.group).X.hom :=
    stageTarget_smooth F N D
  exact nonempty_isoStage F D.field D.inertia
    (G := (baseChange (Spec.algebraMap F D.field)).obj G)
    (H := (baseChange (Spec.algebraMap (extensionIntegers F D.field) D.field)).obj D.group)
    (stageGenericComparison F N D)

/-- Choose a finite enlargement retaining the prescribed generic map. -/
def modelIsoStage :
    IsoStage F D.field D.inertia
      (G := (baseChange (Spec.algebraMap F D.field)).obj G)
      (H := (baseChange (Spec.algebraMap (extensionIntegers F D.field) D.field)).obj D.group)
      (stageGenericComparison F N D) :=
  Classical.choice (nonempty_modelIsoStage F N D)

variable (A : IsoStage F D.field D.inertia
  (G := (baseChange (Spec.algebraMap F D.field)).obj G)
  (H := (baseChange (Spec.algebraMap (extensionIntegers F D.field) D.field)).obj D.group)
  (stageGenericComparison F N D))

/-- The generic identification of the enlarged integral group. -/
def enlargedGenericIso :
    (baseChange (Spec.algebraMap (extensionIntegers F A.field) A.field)).obj
        ((baseChange (stageIntegerMap F A.contains)).obj D.group) ≅
      (baseChange (Spec.algebraMap F A.field)).obj G :=
  enlargementGenericSquare F A.contains D.group ≪≫
      A.iso.symm ≪≫ pullbackComparison _ _ _ (fieldSpecMap_base F A.contains) G

/-- The actual enlarged integer model with its generic identification. -/
def enlargedModel :
    IntegralModel (extensionIntegers F A.field) A.field
      ((baseChange (Spec.algebraMap F A.field)).obj G) where
  group := (baseChange (stageIntegerMap F A.contains)).obj D.group
  affine := MorphismProperty.pullback_snd _ _ D.affine
  flat := by
    let := D.smooth
    exact MorphismProperty.pullback_snd _ _ (inferInstance : Flat D.group.X.hom)
  finiteType := by
    let := D.smooth
    exact MorphismProperty.pullback_snd _ _ (inferInstance : LocallyOfFiniteType D.group.X.hom)
  genericIso := enlargedGenericIso F N D A

theorem enlargedModel_smooth : (enlargedModel F N D A).IsSmooth := by
  let := D.smooth
  change Smooth (pullback.snd D.group.X.hom (stageIntegerMap F A.contains))
  infer_instance

/-- The enlarged model recovers the supplied integral group. -/
def enlargedModelIso :
    (baseChange (spectralIntegerMap F A.field A.inertia)).obj
        ((baseChange (stageIntegerMap F A.contains)).obj D.group) ≅ N.group :=
  stageIntegralComparison F A.contains D.inertia A.inertia D.group ≪≫ D.iso.symm

end Langlands.GroupScheme.Descent.FiniteUnramified
