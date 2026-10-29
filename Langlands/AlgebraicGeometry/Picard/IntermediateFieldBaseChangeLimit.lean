import Mathlib.AlgebraicGeometry.AffineTransitionLimit
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Connected
import Mathlib.FieldTheory.IntermediateField.Algebraic
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.Picard

variable (K Ω : Type u) [Field K] [Field Ω] [Algebra K Ω]

/-- The finite-dimensional intermediate fields of `Ω / K`, ordered by inclusion. -/
abbrev FinIntermediateField : Type u := {E : IntermediateField K Ω // FiniteDimensional K E}

instance : IsDirected (FinIntermediateField K Ω) (· ≤ ·) where
  directed E₁ E₂ := by
    have := E₁.2
    have := E₂.2
    exact ⟨⟨E₁.1 ⊔ E₂.1, inferInstance⟩, le_sup_left (a := E₁.1), le_sup_right (a := E₁.1)⟩

instance : Nonempty (FinIntermediateField K Ω) := ⟨⟨⊥, inferInstance⟩⟩

/-- The ring map `E ⟶ E'` of an inclusion of intermediate fields. -/
abbrev inclusionHom {E E' : IntermediateField K Ω} (h : E ≤ E') :
    CommRingCat.of E ⟶ CommRingCat.of E' :=
  CommRingCat.ofHom (IntermediateField.inclusion h).toRingHom

lemma inclusionHom_eq_id {E : IntermediateField K Ω} (h : E ≤ E) :
    inclusionHom K Ω h = 𝟙 _ := by
  ext; rfl

@[reassoc (attr := simp)]
lemma inclusionHom_comp_inclusionHom {E E' E'' : IntermediateField K Ω} (h : E ≤ E')
    (h' : E' ≤ E'') : inclusionHom K Ω h ≫ inclusionHom K Ω h' = inclusionHom K Ω (h.trans h') := by
  ext; rfl

@[reassoc (attr := simp)]
lemma algebraMap_comp_inclusionHom {E E' : IntermediateField K Ω} (h : E ≤ E') :
    CommRingCat.ofHom (algebraMap K E) ≫ inclusionHom K Ω h =
      CommRingCat.ofHom (algebraMap K E') := by
  ext; rfl

@[reassoc (attr := simp)]
lemma inclusionHom_comp_algebraMap {E E' : IntermediateField K Ω} (h : E ≤ E') :
    inclusionHom K Ω h ≫ CommRingCat.ofHom (algebraMap E' Ω) =
      CommRingCat.ofHom (algebraMap E Ω) := by
  ext; rfl

@[reassoc (attr := simp)]
lemma algebraMap_comp_algebraMap (E : IntermediateField K Ω) :
    CommRingCat.ofHom (algebraMap K E) ≫ CommRingCat.ofHom (algebraMap E Ω) =
      CommRingCat.ofHom (algebraMap K Ω) := by
  ext; rfl

/-- The diagram of the finite-dimensional intermediate fields, as commutative rings. -/
@[simps]
def finIntermediateFieldDiagram : FinIntermediateField K Ω ⥤ CommRingCat.{u} where
  obj E := CommRingCat.of E.1
  map f := inclusionHom K Ω (leOfHom f)
  map_id _ := inclusionHom_eq_id K Ω _
  map_comp _ _ := (inclusionHom_comp_inclusionHom K Ω _ _).symm

/-- The cocone of inclusions `E ⟶ Ω`. -/
@[simps]
def finIntermediateFieldCocone : Cocone (finIntermediateFieldDiagram K Ω) where
  pt := CommRingCat.of Ω
  ι :=
    { app E := CommRingCat.ofHom (algebraMap E.1 Ω)
      naturality _ _ _ := by ext; rfl }

/-- An algebraic extension is the filtered colimit of its finite-dimensional intermediate
fields. -/
noncomputable def isColimitFinIntermediateFieldCocone [Algebra.IsAlgebraic K Ω] :
    IsColimit (finIntermediateFieldCocone K Ω) := by
  have : ReflectsFilteredColimits (forget CommRingCat.{u}) :=
    ⟨fun _ ↦ reflectsColimitsOfShape_of_reflectsIsomorphisms⟩
  refine isColimitOfReflects (forget _) (Types.FilteredColimit.isColimitOf' _ _ ?_ ?_)
  · intro (x : Ω)
    exact ⟨⟨IntermediateField.adjoin K {x},
      IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral x)⟩,
      ⟨x, IntermediateField.mem_adjoin_simple_self K x⟩, rfl⟩
  · intro E x y h
    exact ⟨E, 𝟙 E, congrArg _ (Subtype.ext h)⟩

variable {K Ω}

set_option backward.isDefEq.respectTransparency false in
/-- A base-change square: `X ×_S T' ⟶ X ×_S T` is the base change of `φ : T' ⟶ T`. -/
lemma isPullback_pullback_map {X S T T' : Scheme.{u}} (p : X ⟶ S) (g : T ⟶ S) (g' : T' ⟶ S)
    (φ : T' ⟶ T) (h : φ ≫ g = g') :
    IsPullback (pullback.map p g' p g (𝟙 X) φ (𝟙 S) (by simp) (by simp [h]))
      (pullback.snd p g') (pullback.snd p g) φ := by
  subst h
  refine IsPullback.of_right (h₁₂ := pullback.fst p g) (v₁₃ := p) (h₂₂ := g) ?_
    (pullback.lift_snd _ _ _) (IsPullback.of_hasPullback p g)
  simpa using IsPullback.of_hasPullback p (φ ≫ g)

variable (X : Scheme.{u}) (p : X ⟶ Spec (CommRingCat.of K))

set_option backward.isDefEq.respectTransparency false in
/-- The cofiltered diagram of base changes `X_E = X ×_K E` over finite intermediate fields. -/
noncomputable def baseChangeDiagram : (FinIntermediateField K Ω)ᵒᵖ ⥤ Scheme.{u} where
  obj E := pullback p (Spec.map (CommRingCat.ofHom (algebraMap K E.unop.1)))
  map {E E'} f := pullback.map _ _ _ _ (𝟙 X) (Spec.map (inclusionHom K Ω (leOfHom f.unop)))
    (𝟙 _) (by simp) (by rw [Category.comp_id, ← Spec.map_comp, algebraMap_comp_inclusionHom])
  map_id E := by
    ext <;> simp [inclusionHom_eq_id]
  map_comp f g := by
    ext <;> simp [← Spec.map_comp]

lemma baseChangeDiagram_map_snd {E E' : (FinIntermediateField K Ω)ᵒᵖ} (f : E ⟶ E') :
    (baseChangeDiagram X p).map f ≫ pullback.snd _ _ =
      pullback.snd _ _ ≫ Spec.map (inclusionHom K Ω (leOfHom f.unop)) :=
  pullback.lift_snd _ _ _

/-- The diagram of the spectra `Spec E`. -/
noncomputable abbrev specDiagram : (FinIntermediateField K Ω)ᵒᵖ ⥤ Scheme.{u} :=
  (finIntermediateFieldDiagram K Ω).op ⋙ Scheme.Spec

/-- The structure maps `X_E ⟶ Spec E`. -/
@[simps]
noncomputable def baseChangeDiagramToSpec :
    baseChangeDiagram X p ⟶ specDiagram (K := K) (Ω := Ω) where
  app _ := pullback.snd _ _
  naturality _ _ f := baseChangeDiagram_map_snd X p f

set_option backward.isDefEq.respectTransparency false in
/-- The cone of base-change maps `X_Ω ⟶ X_E`. -/
@[simps]
noncomputable def baseChangeCone : Cone (baseChangeDiagram (Ω := Ω) X p) where
  pt := pullback p (Spec.map (CommRingCat.ofHom (algebraMap K Ω)))
  π :=
    { app E := pullback.map _ _ _ _ (𝟙 X) (Spec.map (CommRingCat.ofHom (algebraMap E.unop.1 Ω)))
        (𝟙 _) (by simp) (by rw [Category.comp_id, ← Spec.map_comp, algebraMap_comp_algebraMap])
      naturality E E' f := by
        apply pullback.hom_ext
        · simp [baseChangeDiagram]
        · simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.id_comp,
            Category.assoc, baseChangeDiagram_map_snd]
          simp [← Spec.map_comp] }

lemma isPullback_baseChangeCone_π_app (E : (FinIntermediateField K Ω)ᵒᵖ) :
    IsPullback ((baseChangeCone X p).π.app E) (pullback.snd _ _) (pullback.snd _ _)
      (Spec.map (CommRingCat.ofHom (algebraMap E.unop.1 Ω))) :=
  isPullback_pullback_map _ _ _ _ (by rw [← Spec.map_comp, algebraMap_comp_algebraMap])

lemma isPullback_baseChangeDiagram_map {E E' : (FinIntermediateField K Ω)ᵒᵖ} (f : E ⟶ E') :
    IsPullback ((baseChangeDiagram X p).map f) (pullback.snd _ _) (pullback.snd _ _)
      (Spec.map (inclusionHom K Ω (leOfHom f.unop))) :=
  isPullback_pullback_map _ _ _ _
    (by rw [← Spec.map_comp, algebraMap_comp_inclusionHom])

/-- `X_Ω` is the limit of the `X_E`. -/
noncomputable def isLimitBaseChangeCone [Algebra.IsAlgebraic K Ω] :
    IsLimit (baseChangeCone (Ω := Ω) X p) := by
  have := IsCofiltered.isConnected (FinIntermediateField K Ω)ᵒᵖ
  exact isLimitOfIsPullbackOfIsConnected (baseChangeDiagramToSpec X p) _
    (Scheme.Spec.mapCone (finIntermediateFieldCocone K Ω).op)
    { hom := pullback.snd _ _
      w E := (pullback.lift_snd _ _ _).symm } (fun E ↦ isPullback_baseChangeCone_π_app X p E)
    (isLimitOfPreserves Scheme.Spec (isColimitFinIntermediateFieldCocone K Ω).op)

instance (E : IntermediateField K Ω) :
    Surjective (Spec.map (CommRingCat.ofHom (algebraMap E Ω))) :=
  ⟨fun _ ↦ ⟨default, Subsingleton.elim _ _⟩⟩

instance (E : IntermediateField K Ω) :
    IsSchemeTheoreticallyDominant (Spec.map (CommRingCat.ofHom (algebraMap E Ω))) :=
  .of_isDominant _

instance {E E' : (FinIntermediateField K Ω)ᵒᵖ} (f : E ⟶ E') :
    IsAffineHom ((baseChangeDiagram X p).map f) :=
  MorphismProperty.of_isPullback (P := @IsAffineHom) (isPullback_baseChangeDiagram_map X p f).flip
    inferInstance

instance [QuasiCompact p] (E : (FinIntermediateField K Ω)ᵒᵖ) :
    CompactSpace ((baseChangeDiagram X p).obj E) :=
  @QuasiCompact.compactSpace_of_compactSpace _ _
    (pullback.snd p (Spec.map (CommRingCat.ofHom (algebraMap K E.unop.1))))
    (MorphismProperty.of_isPullback (P := @QuasiCompact) (IsPullback.of_hasPullback _ _) ‹_›)
    inferInstance

instance [QuasiSeparated p] (E : (FinIntermediateField K Ω)ᵒᵖ) :
    QuasiSeparatedSpace ((baseChangeDiagram X p).obj E) :=
  @quasiSeparatedSpace_of_quasiSeparated _ _
    (pullback.snd p (Spec.map (CommRingCat.ofHom (algebraMap K E.unop.1)))) inferInstance
    (MorphismProperty.of_isPullback (P := @QuasiSeparated) (IsPullback.of_hasPullback _ _) ‹_›)

/-- The projections `X_Ω ⟶ X_E` are injective on sections. -/
lemma baseChangeCone_π_app_app_injective (E : (FinIntermediateField K Ω)ᵒᵖ)
    (V : ((baseChangeDiagram X p).obj E).Opens) :
    Function.Injective (((baseChangeCone (Ω := Ω) X p).π.app E).app V) := by
  have H := (isPullback_baseChangeCone_π_app X p E).flip
  have hflat : Flat (pullback.snd p (Spec.map (CommRingCat.ofHom (algebraMap K E.unop.1)))) :=
    inferInstance
  have : QuasiCompact ((baseChangeCone X p).π.app E) :=
    MorphismProperty.of_isPullback (P := @QuasiCompact) H inferInstance
  have : IsSchemeTheoreticallyDominant ((baseChangeCone X p).π.app E) :=
    @IsSchemeTheoreticallyDominant.of_isPullback _ _ _ _ _ _ _ _ H inferInstance inferInstance hflat
  exact Scheme.Hom.app_injective _ V

/-- The projections `X_Ω ⟶ X_E` are surjective. -/
lemma baseChangeCone_π_app_surjective (E : (FinIntermediateField K Ω)ᵒᵖ) :
    Function.Surjective ((baseChangeCone (Ω := Ω) X p).π.app E).base :=
  (MorphismProperty.of_isPullback (P := @Surjective)
    (isPullback_baseChangeCone_π_app X p E).flip inferInstance).surj

end Langlands.AlgebraicGeometry.Picard
