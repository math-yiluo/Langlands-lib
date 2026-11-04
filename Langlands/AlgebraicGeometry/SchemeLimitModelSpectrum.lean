import Langlands.AlgebraicGeometry.SchemeLimitModelColimit
import Langlands.AlgebraicGeometry.PointTopology.FilteredRingPoints

/-! # Actual model morphisms along a diagram of commutative algebras -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.SchemeLimitModel

open PointTopology

variable (R : Type u) [CommRing R]
variable {J : Type u} [SmallCategory J] (F : J ⥤ CommAlgCat.{u} R)

/-- The actual diagram of spectra underlying a diagram of `R`-algebras. -/
def spectrumDiagram : Jᵒᵖ ⥤ Scheme.{u} :=
  (F.op ⋙ algSpec (CommRingCat.of R)) ⋙ Over.forget _

instance spectrumDiagram_obj_isAffine (j : Jᵒᵖ) :
    IsAffine ((spectrumDiagram R F).obj j) := by
  change IsAffine (Spec (CommRingCat.of (F.obj j.unop)))
  infer_instance

/-- Its structural maps to the spectrum of the fixed coefficient ring. -/
def spectrumStructure :
    spectrumDiagram R F ⟶ (Functor.const Jᵒᵖ).obj (Spec (CommRingCat.of R)) :=
  NatTrans.mk (fun i => ((F.op ⋙ algSpec (CommRingCat.of R)).obj i).hom) (by
    intro i j f
    change ((F.op ⋙ algSpec (CommRingCat.of R)).map f).left ≫
      ((F.op ⋙ algSpec (CommRingCat.of R)).obj j).hom =
      ((F.op ⋙ algSpec (CommRingCat.of R)).obj i).hom ≫ 𝟙 _
    rw [Category.comp_id]
    exact Over.w _)

variable (c : Cocone F)

/-- The actual scheme cone obtained from the algebra cocone. -/
def spectrumCone : Cone (spectrumDiagram R F) :=
  (Over.forget _).mapCone (ringTestCone R F c)

/-- The cone's structural map is the actual `R`-algebra spectrum map. -/
def spectrumBaseMap : (spectrumCone R F c).pt ⟶ Spec (CommRingCat.of R) :=
  ((algSpec (CommRingCat.of R)).obj (op c.pt)).hom

@[simp]
lemma spectrumCone_π_app (j : J) :
    (spectrumCone R F c).π.app (op j) =
      Spec.map (CommRingCat.ofHom (c.ι.app j).hom.toRingHom) := rfl

lemma spectrumCone_compat (j : Jᵒᵖ) :
    (spectrumCone R F c).π.app j ≫ (spectrumStructure R F).app j =
      spectrumBaseMap R F c :=
  Over.w ((ringTestCone R F c).π.app j)

/-- A filtered algebra colimit gives the limit of the actual spectra. -/
def spectrumConeIsLimit [IsFiltered J] (hc : IsColimit c) :
    IsLimit (spectrumCone R F c) :=
  isLimitOfPreserves (Over.forget _) (ringTestConeIsLimit R F c hc)

variable (X Y : Over (Spec (CommRingCat.of R)))

/-- Actual relative morphisms between the two models after base change to a
stage algebra. -/
abbrev SpectrumLevelHom (j : J) :=
  LevelHom (spectrumDiagram R F) (spectrumStructure R F) X.hom Y.hom (op j)

/-- The actual level Hom functor indexed covariantly by the algebra diagram. -/
def spectrumHomFunctor : J ⥤ Type u :=
  opOp J ⋙ homFunctor (spectrumDiagram R F) (spectrumStructure R F) X.hom Y.hom

@[simp]
lemma spectrumHomFunctor_map {i j : J} (r : i ⟶ j)
    (f : SpectrumLevelHom R F X Y i) :
    (spectrumHomFunctor R F X Y).map r f =
      restrict (spectrumDiagram R F) (spectrumStructure R F) X.hom Y.hom r.op f := rfl

/-- The concrete quotient colimit of the actual stage model morphisms. -/
def SpectrumHomColimit : Type u := (spectrumHomFunctor R F X Y).ColimitType

def spectrumHomColimitι (j : J) :
    SpectrumLevelHom R F X Y j → SpectrumHomColimit R F X Y :=
  (spectrumHomFunctor R F X Y).ιColimitType j

@[simp]
lemma spectrumHomColimitι_restrict {i j : J} (r : i ⟶ j)
    (f : SpectrumLevelHom R F X Y i) :
    spectrumHomColimitι R F X Y j
      (restrict (spectrumDiagram R F) (spectrumStructure R F) X.hom Y.hom r.op f) =
        spectrumHomColimitι R F X Y i f :=
  (spectrumHomFunctor R F X Y).ιColimitType_map r f

/-- Reindexing the generic scheme quotient by the algebra index changes no
stage representative. -/
def spectrumHomColimitEquiv :
    SpectrumHomColimit R F X Y ≃
      HomColimit (spectrumDiagram R F) (spectrumStructure R F) X.hom Y.hom where
  toFun := (spectrumHomFunctor R F X Y).descColimitType
    { pt := HomColimit (spectrumDiagram R F) (spectrumStructure R F) X.hom Y.hom
      ι j := homColimitι (spectrumDiagram R F) (spectrumStructure R F) X.hom Y.hom (op j)
      ι_naturality r := by
        funext f
        exact homColimitι_restrict (spectrumDiagram R F) (spectrumStructure R F)
          X.hom Y.hom r.op f }
  invFun := (homFunctor (spectrumDiagram R F) (spectrumStructure R F) X.hom Y.hom).descColimitType
    { pt := SpectrumHomColimit R F X Y
      ι i := spectrumHomColimitι R F X Y i.unop.unop
      ι_naturality r := by
        funext f
        exact (spectrumHomFunctor R F X Y).ιColimitType_map r.unop.unop f }
  left_inv z := by
    obtain ⟨j, f, rfl⟩ := (spectrumHomFunctor R F X Y).ιColimitType_jointly_surjective z
    rfl
  right_inv z := by
    obtain ⟨j, f, rfl⟩ := homColimitι_jointly_surjective
      (spectrumDiagram R F) (spectrumStructure R F) X.hom Y.hom z
    rfl

@[simp]
lemma spectrumHomColimitEquiv_ι (j : J) (f : SpectrumLevelHom R F X Y j) :
    spectrumHomColimitEquiv R F X Y (spectrumHomColimitι R F X Y j f) =
      homColimitι (spectrumDiagram R F) (spectrumStructure R F) X.hom Y.hom (op j) f :=
  rfl

/-- The actual base-change cocone, now indexed by the algebra diagram. -/
def spectrumHomCoconeTypes : (spectrumHomFunctor R F X Y).CoconeTypes :=
  (homCoconeTypes (spectrumDiagram R F) (spectrumStructure R F) X.hom Y.hom
    (spectrumCone R F c) (spectrumBaseMap R F c) (spectrumCone_compat R F c)).precomp
      (opOp J)

/-- Its categorical cocone of actual relative Hom sets. -/
def spectrumHomCocone : Cocone (spectrumHomFunctor R F X Y) :=
  (spectrumHomFunctor R F X Y).coconeTypesEquiv (spectrumHomCoconeTypes R F c X Y)

/-- The canonical comparison to actual morphisms after base change to the
algebra cocone's ring. -/
def spectrumHomColimitMap :
    SpectrumHomColimit R F X Y → LimitHom X.hom Y.hom (spectrumBaseMap R F c) :=
  (spectrumHomFunctor R F X Y).descColimitType (spectrumHomCoconeTypes R F c X Y)

@[simp]
lemma spectrumHomColimitMap_ι (j : J) (f : SpectrumLevelHom R F X Y j) :
    spectrumHomColimitMap R F c X Y (spectrumHomColimitι R F X Y j f) =
      toLimit (spectrumDiagram R F) (spectrumStructure R F) X.hom Y.hom
        (spectrumCone R F c) (spectrumBaseMap R F c) (spectrumCone_compat R F c) (op j) f :=
  rfl

/-- The actual algebra-index comparison commutes with the proved quotient
reindexing equivalence and the generic scheme comparison. -/
lemma spectrumHomColimitMap_eq (z : SpectrumHomColimit R F X Y) :
    spectrumHomColimitMap R F c X Y z =
      homColimitMap (spectrumDiagram R F) (spectrumStructure R F) X.hom Y.hom
        (spectrumCone R F c) (spectrumBaseMap R F c) (spectrumCone_compat R F c)
          (spectrumHomColimitEquiv R F X Y z) := by
  obtain ⟨j, f, rfl⟩ := (spectrumHomFunctor R F X Y).ιColimitType_jointly_surjective z
  rfl

end Langlands.AlgebraicGeometry.SchemeLimitModel
