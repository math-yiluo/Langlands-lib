import Langlands.Sheaf.Equivariant.AnalyticOpenEtaleRestriction.Conditional
import Langlands.Sheaf.Equivariant.AnalyticEtaleCohomology

/-! # Additivity and global sections of ordinary restriction -/

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u v uL uA vA

namespace Langlands.Sheaf.Equivariant.Analytic.OpenEtaleRestriction

open CategoryTheory Opposite TopologicalSpace
open Langlands.Analytic Langlands.Analytic.SaturatedAtlasPresentation
open Langlands.Sheaf.Equivariant.TwistedOver

/-- Ordinary sheaves inherit the canonical pointwise addition on the open-set site. -/
instance (priority := low) topCatSheaf_preadditive {Y : TopCat.{v}} {A : Type uA} [Category.{vA} A]
    [Preadditive A] : Preadditive (TopCat.Sheaf A Y) :=
  inferInstanceAs (Preadditive (Sheaf (Opens.grothendieckTopology Y) A))

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable (X : LocalizedCategory.{u, v, v} (K := K))
variable (hOpen : EtaleOpenDomainStatement X)

/-- The canonical arrow of an actual open domain to the identity étale object. -/
def openEtaleToSelf (U : Opens (localizedSpaceFunctor.obj X)) :
    openEtaleObject X hOpen U ⟶ etaleSelf X :=
  MorphismProperty.Over.homMk
    (domainι X ((presentationOf X).openDomain (U : Set (localizedSpaceFunctor.obj X)) U.isOpen))
    (Category.comp_id _)

/-- The full open analytic domain is canonically the original identity object. -/
def openEtaleTopIso : openEtaleObject X hOpen ⊤ ≅ etaleSelf X where
  hom := openEtaleToSelf X hOpen ⊤
  inv := openEtaleLift X hOpen ⊤ (etaleSelf X) (fun _ => trivial)
  hom_inv_id := Subsingleton.elim _ _
  inv_hom_id := by
    apply MorphismProperty.Over.Hom.ext
    exact (Category.comp_id _).symm.trans
      (MorphismProperty.Over.w
        (openEtaleLift X hOpen ⊤ (etaleSelf X) (fun _ => trivial) ≫ openEtaleToSelf X hOpen ⊤))

/-- Inclusion of opens commutes with their canonical arrows to the identity object. -/
theorem openEtaleMap_comp_openEtaleToSelf
    {U V : Opens (localizedSpaceFunctor.obj X)} (f : U ⟶ V) :
    openEtaleMap X hOpen f ≫ openEtaleToSelf X hOpen V = openEtaleToSelf X hOpen U := by
  apply MorphismProperty.Over.Hom.ext
  apply (cancel_mono (𝟙 X)).1
  exact (MorphismProperty.Over.w (openEtaleMap X hOpen f ≫ openEtaleToSelf X hOpen V)).trans
    (MorphismProperty.Over.w (openEtaleToSelf X hOpen U)).symm

variable {A : Type uA} [Category.{vA} A]

/-- Ordinary restriction identifies the two global section objects. -/
def etaleUnderlyingGlobalIso (F : Sheaf (etaleTopology X) A) :
    F.obj.obj (op (etaleSelf X)) ≅
      ((etaleUnderlyingSheaf X hOpen A).obj F).obj.obj (op ⊤) :=
  F.obj.mapIso (openEtaleTopIso X hOpen).op

/-- Ordinary restriction from the full open agrees with the original étale restriction. -/
theorem etaleUnderlyingGlobalIso_restrict (F : Sheaf (etaleTopology X) A)
    (U : Opens (localizedSpaceFunctor.obj X)) :
    (etaleUnderlyingGlobalIso X hOpen F).hom ≫
        ((etaleUnderlyingSheaf X hOpen A).obj F).obj.map (homOfLE le_top : U ⟶ ⊤).op =
      F.obj.map (openEtaleToSelf X hOpen U).op := by
  change F.obj.map (openEtaleToSelf X hOpen ⊤).op ≫
    F.obj.map (openEtaleMap X hOpen (homOfLE le_top : U ⟶ ⊤)).op = _
  rw [← F.obj.map_comp, ← op_comp, openEtaleMap_comp_openEtaleToSelf]

section Additive

variable [Preadditive A]

/-- Ordinary restriction is additive by pointwise precomposition. -/
instance etaleUnderlyingSheaf_additive : (etaleUnderlyingSheaf X hOpen A).Additive where
  map_add := rfl

end Additive

/-- The same addition is used when the ordinary sheaf category is abelian. -/
instance etaleUnderlyingSheaf_additive_of_hasSheafify [Abelian A]
    [HasSheafify (Opens.grothendieckTopology (localizedSpaceFunctor.obj X)) A] :
    (etaleUnderlyingSheaf X hOpen A).Additive :=
  etaleUnderlyingSheaf_additive X hOpen

variable (R : Type (max u (v + 1) uL)) [CommRing R]

/-- The ordinary global sections after restriction are naturally the étale global sections. -/
def etaleUnderlyingGlobalNatIso :
    etaleSections.{u, v, uL} X R ≅
      etaleUnderlyingSheaf X hOpen (ModuleCat.{max u (v + 1) uL} R) ⋙
        sheafSectionsModule (Opens.grothendieckTopology (localizedSpaceFunctor.obj X)) R ⊤ :=
  NatIso.ofComponents (fun F => etaleUnderlyingGlobalIso X hOpen F)
    (fun α => (α.hom.naturality (openEtaleToSelf X hOpen ⊤).op).symm)

/-- The forward comparison is restriction along the canonical full-domain inclusion. -/
theorem etaleUnderlyingGlobalNatIso_hom_app
    (F : Sheaf (etaleTopology X) (ModuleCat.{max u (v + 1) uL} R)) :
    (etaleUnderlyingGlobalNatIso.{u, v, uL} X hOpen R).hom.app F =
      F.obj.map (openEtaleToSelf X hOpen ⊤).op :=
  rfl

end Langlands.Sheaf.Equivariant.Analytic.OpenEtaleRestriction
