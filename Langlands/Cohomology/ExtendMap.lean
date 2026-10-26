import Langlands.Cohomology.DerivedPlus

/-!
# Extension by zero and functors

The inverse of `DerivedPlus.mapExtendIso` is natural in both the complex and
in the functor. These declarations were moved unchanged from
`DivisibleSystem.InvariantComparison` so generic cohomology infrastructure
can reuse them without importing the divisible-system development.
-/

noncomputable section

namespace Langlands.Cohomology

open CategoryTheory CategoryTheory.Limits Opposite

universe u₁ v₁ u₂ v₂

section ExtendMap

open HomologicalComplex

variable {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'} (e : c.Embedding c')
  {C : Type u₁} [Category.{v₁} C] [HasZeroMorphisms C] [HasZeroObject C]
  {D : Type u₂} [Category.{v₂} D] [HasZeroMorphisms D] [HasZeroObject D]
  (F : C ⥤ D) [F.PreservesZeroMorphisms]

lemma extendXMapIso_inv_mapX {K L : HomologicalComplex C c} (φ : K ⟶ L) (i : Option ι) :
    F.map (extend.mapX φ i) ≫ (DerivedPlus.extendXMapIso F L i).inv =
      (DerivedPlus.extendXMapIso F K i).inv ≫
        extend.mapX ((F.mapHomologicalComplex c).map φ) i :=
  match i with
  | none => (extend.isZero_X _ rfl).eq_of_tgt _ _
  | some _ => (Category.comp_id _).trans (Category.id_comp _).symm

/-- Extending a complex along an embedding of complex shapes commutes with applying a functor
preserving zero morphisms: the inverse of the Library's `DerivedPlus.mapExtendIso`. -/
def extendMapIso (K : HomologicalComplex C c) :
    (F.mapHomologicalComplex c').obj (K.extend e) ≅
      ((F.mapHomologicalComplex c).obj K).extend e :=
  (DerivedPlus.mapExtendIso F K e).symm

lemma extendMapIso_hom_f (K : HomologicalComplex C c) (i' : ι') :
    (extendMapIso e F K).hom.f i' = (DerivedPlus.extendXMapIso F K (e.r i')).inv :=
  rfl

lemma extendMapIso_hom_naturality {K L : HomologicalComplex C c} (φ : K ⟶ L) :
    (F.mapHomologicalComplex c').map (extendMap φ e) ≫ (extendMapIso e F L).hom =
      (extendMapIso e F K).hom ≫ extendMap ((F.mapHomologicalComplex c).map φ) e := by
  ext i'
  exact extendXMapIso_inv_mapX F φ (e.r i')

variable {F} {G : C ⥤ D} [G.PreservesZeroMorphisms]

lemma extendXMapIso_inv_app (α : F ⟶ G) (K : HomologicalComplex C c) (i : Option ι) :
    α.app (extend.X K i) ≫ (DerivedPlus.extendXMapIso G K i).inv =
      (DerivedPlus.extendXMapIso F K i).inv ≫
        extend.mapX ((NatTrans.mapHomologicalComplex α c).app K) i :=
  match i with
  | none => (extend.isZero_X _ rfl).eq_of_tgt _ _
  | some _ => (Category.comp_id _).trans (Category.id_comp _).symm

lemma extendMapIso_hom_app (α : F ⟶ G) (K : HomologicalComplex C c) :
    (NatTrans.mapHomologicalComplex α c').app (K.extend e) ≫ (extendMapIso e G K).hom =
      (extendMapIso e F K).hom ≫
        extendMap ((NatTrans.mapHomologicalComplex α c).app K) e := by
  ext i'
  exact extendXMapIso_inv_app α K (e.r i')

end ExtendMap

end Langlands.Cohomology
