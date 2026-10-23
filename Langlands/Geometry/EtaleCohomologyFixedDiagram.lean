import Langlands.Geometry.EtaleCohomologyDiagramFunctor

/-!
# Fixed-scheme coefficient diagrams inside varying-scheme diagrams
-/

noncomputable section

namespace Langlands.Geometry.EtalePullback

open CategoryTheory AlgebraicGeometry Opposite

universe u v w

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable (X : Scheme.{u}) (R : Type u) [CommRing R]
variable (J : Type v) [Category.{w} J]

/-- The constant opposite-scheme diagram used for fixed-scheme coefficients. -/
abbrev fixedSchemeDiagram : J ⥤ Scheme.{u}ᵒᵖ :=
  (Functor.const J).obj (op X)

instance {i j : J} (a : i ⟶ j) : Etale ((fixedSchemeDiagram X J).map a).unop :=
  inferInstanceAs (Etale (𝟙 X))

/-- Identity restriction identifies the coefficient identity at a fixed scheme. -/
theorem fixedSchemeDiagram_restrictionId (i : J) :
    diagramRestrictionId R (fixedSchemeDiagram X J) i =
      restrictionId (X := X) (ModuleCat.{u} R) := by
  ext F
  simp [diagramRestrictionId, restrictionCongr]

/-- The composition constraint of the constant scheme diagram is compatible
with the identity restriction identification. -/
theorem fixedSchemeDiagram_restrictionComp {i j k : J} (a : i ⟶ j) (b : j ⟶ k)
    (F : EtaleDerivedSections.ModuleSheaf X R) :
    (diagramRestrictionComp R (fixedSchemeDiagram X J) a b).hom.app F ≫
        (restrictionId (X := X) (ModuleCat.{u} R)).hom.app F =
      (restriction (𝟙 X) (ModuleCat.{u} R)).map
          ((restrictionId (X := X) (ModuleCat.{u} R)).hom.app F) ≫
        (restrictionId (X := X) (ModuleCat.{u} R)).hom.app F := by
  apply congrArg (fun t => t ≫
    (restrictionId (X := X) (ModuleCat.{u} R)).hom.app F)
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  rfl

namespace CoefficientDiagram

/-- An ordinary diagram of sheaves on one scheme gives compatible coefficients
on the constant scheme diagram. -/
def ofFixed (D : J ⥤ EtaleDerivedSections.ModuleSheaf X R) :
    CoefficientDiagram R (fixedSchemeDiagram X J) where
  obj i := D.obj i
  map a := (restrictionId (X := X) (ModuleCat.{u} R)).hom.app (D.obj _) ≫ D.map a
  map_id i := by
    rw [D.map_id, fixedSchemeDiagram_restrictionId]
    erw [Category.comp_id]
  map_comp {i j k} a b := by
    have h := (restrictionId (X := X) (ModuleCat.{u} R)).hom.naturality (D.map a)
    change (restriction (𝟙 X) (ModuleCat.{u} R)).map (D.map a) ≫
      (restrictionId (X := X) (ModuleCat.{u} R)).hom.app (D.obj j) =
      (restrictionId (X := X) (ModuleCat.{u} R)).hom.app (D.obj i) ≫ D.map a at h
    rw [D.map_comp, ← Category.assoc,
      fixedSchemeDiagram_restrictionComp, Category.assoc]
    calc
      _ = (restriction (𝟙 X) (ModuleCat.{u} R)).map
          ((restrictionId (X := X) (ModuleCat.{u} R)).hom.app (D.obj i)) ≫
          ((restrictionId (X := X) (ModuleCat.{u} R)).hom.app (D.obj i) ≫ D.map a) ≫
            D.map b := by simp only [Category.assoc]
      _ = (restriction (𝟙 X) (ModuleCat.{u} R)).map
          ((restrictionId (X := X) (ModuleCat.{u} R)).hom.app (D.obj i)) ≫
          ((restriction (𝟙 X) (ModuleCat.{u} R)).map (D.map a) ≫
            (restrictionId (X := X) (ModuleCat.{u} R)).hom.app (D.obj j)) ≫
              D.map b := congrArg (fun t =>
                (restriction (𝟙 X) (ModuleCat.{u} R)).map
                  ((restrictionId (X := X) (ModuleCat.{u} R)).hom.app (D.obj i)) ≫
                    t ≫ D.map b) h.symm
      _ = _ := by
        simp only [CategoryTheory.Functor.map_comp, Category.assoc]
        rfl

/-- Compatible maps between ordinary sheaf diagrams give maps between their
constant-scheme coefficient diagrams. -/
def ofFixedMap {D E : J ⥤ EtaleDerivedSections.ModuleSheaf X R} (α : D ⟶ E) :
    ofFixed X R J D ⟶ ofFixed X R J E where
  app i := α.app i
  comm {i j} a := by
    dsimp only [ofFixed]
    have h := (restrictionId (X := X) (ModuleCat.{u} R)).hom.naturality (α.app i)
    change (restriction (𝟙 X) (ModuleCat.{u} R)).map (α.app i) ≫
      (restrictionId (X := X) (ModuleCat.{u} R)).hom.app (E.obj i) =
      (restrictionId (X := X) (ModuleCat.{u} R)).hom.app (D.obj i) ≫ α.app i at h
    calc
      _ = (restrictionId (X := X) (ModuleCat.{u} R)).hom.app (D.obj i) ≫
          (α.app i ≫ E.map a) := by rw [Category.assoc, α.naturality]
      _ = _ := by rw [← Category.assoc, ← h]; rfl

/-- Ordinary fixed-scheme sheaf diagrams embed functorially into compatible
coefficients on the constant opposite-scheme diagram. -/
def ofFixedFunctor : (J ⥤ EtaleDerivedSections.ModuleSheaf X R) ⥤
    CoefficientDiagram R (fixedSchemeDiagram X J) where
  obj := ofFixed X R J
  map := ofFixedMap X R J
  map_id D := by apply Hom.ext; rfl
  map_comp α β := by apply Hom.ext; rfl

/-- The induced cohomology transition is exactly cohomology of the original
fixed-scheme sheaf transition. -/
theorem ofFixed_cohomology_map (D : J ⥤ EtaleDerivedSections.ModuleSheaf X R)
    (q : ℕ) {i j : J} (a : i ⟶ j) :
    ((ofFixed X R J D).cohomology q).map a =
      (EtaleDerivedSections.cohomology X R q).map (D.map a) := by
  dsimp only [cohomology, cohomologyMapWithCoefficients, ofFixed]
  rw [CategoryTheory.Functor.map_comp, ← Category.assoc]
  erw [EtalePullback.cohomologyMap_id R q (D.obj i)]
  erw [Category.id_comp]
  rfl

/-- The varying-scheme cohomology diagram specializes to the published
fixed-scheme construction, with identity components. -/
def ofFixedCohomologyIso (D : J ⥤ EtaleDerivedSections.ModuleSheaf X R) (q : ℕ) :
    (ofFixed X R J D).cohomology q ≅ D ⋙ EtaleDerivedSections.cohomology X R q :=
  NatIso.ofComponents (fun i => Iso.refl _) (fun {i j} a => by
    calc
      _ = ((ofFixed X R J D).cohomology q).map a := Category.comp_id _
      _ = (EtaleDerivedSections.cohomology X R q).map (D.map a) :=
        ofFixed_cohomology_map X R J D q a
      _ = _ := (Category.id_comp _).symm)

/-- The fixed-scheme comparison is natural in the entire coefficient diagram. -/
def ofFixedCohomologyFunctorIso (q : ℕ) :
    ofFixedFunctor X R J ⋙ cohomologyFunctor q ≅
      EtaleDerivedSections.diagramFunctor X R J q :=
  NatIso.ofComponents (fun D => ofFixedCohomologyIso X R J D q) (fun {D E} α => by
    apply NatTrans.ext
    funext i
    exact (Category.comp_id _).trans (Category.id_comp _).symm)

end CoefficientDiagram

end Langlands.Geometry.EtalePullback
