import Langlands.Cohomology.GaloisGerms
import Langlands.Sheaf.Equivariant.AnalyticOpenEtaleGerms

/-! # The ordinary neighbourhood system of a point as a germ system on the étale site -/

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Sheaf.Equivariant.Analytic

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Langlands.Analytic Langlands.Analytic.SaturatedAtlasPresentation
open Langlands.Cohomology

universe u v uL

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable (X : LocalizedCategory.{u, v, v} (K := K))

/-- The open neighbourhoods of `y`, as the `max u (v + 1) uL`-small copy of the category of
elements of the fiber functor of the ordinary point at `y`. -/
def nbhdIndex (y : localizedSpaceFunctor.obj X) : Type (max u (v + 1) uL) :=
  AsSmall.{max u (v + 1) uL} (underlyingTopologyPoint.{u, v, uL} X y).fiber.Elements

instance (y : localizedSpaceFunctor.obj X) : SmallCategory (nbhdIndex.{u, v, uL} X y) :=
  inferInstanceAs (SmallCategory
    (AsSmall.{max u (v + 1) uL} (underlyingTopologyPoint.{u, v, uL} X y).fiber.Elements))

instance (y : localizedSpaceFunctor.obj X) : IsCofiltered (nbhdIndex.{u, v, uL} X y) :=
  IsCofiltered.of_equivalence
    (AsSmall.equiv : (underlyingTopologyPoint.{u, v, uL} X y).fiber.Elements ≌
      AsSmall.{max u (v + 1) uL} (underlyingTopologyPoint.{u, v, uL} X y).fiber.Elements)

variable {X} in
/-- The neighbourhood index of an open set containing `y`. -/
def nbhdIndex.mk {y : localizedSpaceFunctor.obj X} (U : Opens (localizedSpaceFunctor.obj X))
    (hy : y ∈ U) : nbhdIndex.{u, v, uL} X y :=
  AsSmall.up.obj ((underlyingTopologyPoint.{u, v, uL} X y).fiber.elementsMk U ⟨⟨hy⟩⟩)

/-- The open sets of the neighbourhood system of `y`. -/
def nbhdOpen (y : localizedSpaceFunctor.obj X) :
    nbhdIndex.{u, v, uL} X y ⥤ Opens (localizedSpaceFunctor.obj X) :=
  AsSmall.down ⋙ Functor.Elements.π _

@[simp]
theorem nbhdOpen_obj_mk (y : localizedSpaceFunctor.obj X) (U : Opens (localizedSpaceFunctor.obj X))
    (hy : y ∈ U) : (nbhdOpen.{u, v, uL} X y).obj (nbhdIndex.mk U hy) = U :=
  rfl

theorem mem_nbhdOpen (y : localizedSpaceFunctor.obj X) (i : nbhdIndex.{u, v, uL} X y) :
    y ∈ (nbhdOpen.{u, v, uL} X y).obj i :=
  (ULift.down i).2.down.down

/-- The neighbourhood system of `y`, as open-domain objects of the actual étale site. -/
def nbhdEtale (y : localizedSpaceFunctor.obj X) : nbhdIndex.{u, v, uL} X y ⥤ EtaleSite X :=
  nbhdOpen.{u, v, uL} X y ⋙ openEtaleFunctor X

@[simp]
theorem nbhdEtale_obj (y : localizedSpaceFunctor.obj X) (i : nbhdIndex.{u, v, uL} X y) :
    (nbhdEtale.{u, v, uL} X y).obj i = openEtaleObject X ((nbhdOpen.{u, v, uL} X y).obj i) :=
  rfl

/-- The passage from the small copy back to the category of elements is final. -/
instance nbhdIndex_down_op_final (y : localizedSpaceFunctor.obj X) :
    (AsSmall.down : AsSmall.{max u (v + 1) uL} (underlyingTopologyPoint.{u, v, uL} X y).fiber.Elements ⥤
      (underlyingTopologyPoint.{u, v, uL} X y).fiber.Elements).op.Final :=
  Functor.final_of_adjunction
    (AsSmall.equiv : (underlyingTopologyPoint.{u, v, uL} X y).fiber.Elements ≌
      AsSmall.{max u (v + 1) uL} (underlyingTopologyPoint.{u, v, uL} X y).fiber.Elements).op.toAdjunction

variable (R : Type (max u (v + 1) uL)) [CommRing R]

/-- The ordinary point fiber of the restriction of an étale sheaf to the ordinary topology is
the germ along the neighbourhood system of open-domain objects. -/
def germOpenIso (y : localizedSpaceFunctor.obj X) :
    etaleUnderlyingSheaf X (ModuleCat.{max u (v + 1) uL} R) ⋙
        (underlyingTopologyPoint.{u, v, uL} X y).sheafFiber ≅
      GaloisGerms.germ (etaleTopology X) R (nbhdEtale.{u, v, uL} X y) :=
  Functor.isoWhiskerLeft
    (sheafToPresheaf (etaleTopology X) (ModuleCat.{max u (v + 1) uL} R) ⋙
      (Functor.whiskeringLeft _ _ _).obj
        ((Functor.Elements.π (underlyingTopologyPoint.{u, v, uL} X y).fiber).op ⋙
          (openEtaleFunctor X).op))
    (Functor.Final.colimIso
      (AsSmall.down : AsSmall.{max u (v + 1) uL} (underlyingTopologyPoint.{u, v, uL} X y).fiber.Elements ⥤
        (underlyingTopologyPoint.{u, v, uL} X y).fiber.Elements).op (E := ModuleCat.{max u (v + 1) uL} R)).symm

theorem germOpenIso_hom_app (y : localizedSpaceFunctor.obj X)
    (F : Sheaf (etaleTopology X) (ModuleCat.{max u (v + 1) uL} R)) :
    (germOpenIso X R y).hom.app F =
      (Functor.Final.colimitIso
        (AsSmall.down : AsSmall.{max u (v + 1) uL}
          (underlyingTopologyPoint.{u, v, uL} X y).fiber.Elements ⥤
            (underlyingTopologyPoint.{u, v, uL} X y).fiber.Elements).op
        ((Functor.Elements.π (underlyingTopologyPoint.{u, v, uL} X y).fiber).op ⋙
          ((etaleUnderlyingSheaf X (ModuleCat.{max u (v + 1) uL} R)).obj F).obj)).inv :=
  rfl

/-- The comparison sends the ordinary germ of a section over a neighbourhood to its germ along
the neighbourhood system. -/
@[reassoc (attr := simp)]
theorem toPresheafFiber_germOpenIso_hom (y : localizedSpaceFunctor.obj X)
    (F : Sheaf (etaleTopology X) (ModuleCat.{max u (v + 1) uL} R)) (i : nbhdIndex.{u, v, uL} X y) :
    (underlyingTopologyPoint.{u, v, uL} X y).toPresheafFiber ((nbhdOpen.{u, v, uL} X y).obj i)
        ⟨⟨mem_nbhdOpen.{u, v, uL} X y i⟩⟩
        ((etaleUnderlyingSheaf X (ModuleCat.{max u (v + 1) uL} R)).obj F).obj ≫
        (germOpenIso X R y).hom.app F =
      GaloisGerms.germι (etaleTopology X) R (nbhdEtale.{u, v, uL} X y) F i := by
  rw [germOpenIso_hom_app, Iso.comp_inv_eq]
  exact (Functor.Final.ι_colimitIso_hom
    (AsSmall.down : AsSmall.{max u (v + 1) uL}
      (underlyingTopologyPoint.{u, v, uL} X y).fiber.Elements ⥤
        (underlyingTopologyPoint.{u, v, uL} X y).fiber.Elements).op
    ((Functor.Elements.π (underlyingTopologyPoint.{u, v, uL} X y).fiber).op ⋙
      ((etaleUnderlyingSheaf X (ModuleCat.{max u (v + 1) uL} R)).obj F).obj) (op i)).symm

/-- The inverse comparison sends the germ along the neighbourhood system back to the
ordinary germ. -/
@[reassoc (attr := simp)]
theorem germι_germOpenIso_inv (y : localizedSpaceFunctor.obj X)
    (F : Sheaf (etaleTopology X) (ModuleCat.{max u (v + 1) uL} R)) (i : nbhdIndex.{u, v, uL} X y) :
    GaloisGerms.germι (etaleTopology X) R (nbhdEtale.{u, v, uL} X y) F i ≫
        (germOpenIso X R y).inv.app F =
      (underlyingTopologyPoint.{u, v, uL} X y).toPresheafFiber ((nbhdOpen.{u, v, uL} X y).obj i)
        ⟨⟨mem_nbhdOpen.{u, v, uL} X y i⟩⟩
        ((etaleUnderlyingSheaf X (ModuleCat.{max u (v + 1) uL} R)).obj F).obj := by
  rw [← toPresheafFiber_germOpenIso_hom, Category.assoc, Iso.hom_inv_id_app]
  exact Category.comp_id _

/-- Elementwise form of `toPresheafFiber_germOpenIso_hom`. -/
@[simp]
theorem germOpenIso_hom_app_toPresheafFiber_apply (y : localizedSpaceFunctor.obj X)
    (F : Sheaf (etaleTopology X) (ModuleCat.{max u (v + 1) uL} R)) (i : nbhdIndex.{u, v, uL} X y)
    (s : F.obj.obj (op (openEtaleObject X ((nbhdOpen.{u, v, uL} X y).obj i)))) :
    (germOpenIso X R y).hom.app F
        ((underlyingTopologyPoint.{u, v, uL} X y).toPresheafFiber ((nbhdOpen.{u, v, uL} X y).obj i)
          ⟨⟨mem_nbhdOpen.{u, v, uL} X y i⟩⟩
          ((etaleUnderlyingSheaf X (ModuleCat.{max u (v + 1) uL} R)).obj F).obj s) =
      GaloisGerms.germι (etaleTopology X) R (nbhdEtale.{u, v, uL} X y) F i s := by
  exact (ConcreteCategory.comp_apply _ _ s).symm.trans
    (ConcreteCategory.congr_hom (toPresheafFiber_germOpenIso_hom X R y F i) s)

/-- Elementwise form of `germι_germOpenIso_inv`. -/
@[simp]
theorem germOpenIso_inv_app_germι_apply (y : localizedSpaceFunctor.obj X)
    (F : Sheaf (etaleTopology X) (ModuleCat.{max u (v + 1) uL} R)) (i : nbhdIndex.{u, v, uL} X y)
    (s : F.obj.obj (op (openEtaleObject X ((nbhdOpen.{u, v, uL} X y).obj i)))) :
    (germOpenIso X R y).inv.app F (GaloisGerms.germι (etaleTopology X) R (nbhdEtale.{u, v, uL} X y) F i s) =
      (underlyingTopologyPoint.{u, v, uL} X y).toPresheafFiber ((nbhdOpen.{u, v, uL} X y).obj i)
        ⟨⟨mem_nbhdOpen.{u, v, uL} X y i⟩⟩
        ((etaleUnderlyingSheaf X (ModuleCat.{max u (v + 1) uL} R)).obj F).obj s := by
  exact (ConcreteCategory.comp_apply _ _ s).symm.trans
    (ConcreteCategory.congr_hom (germι_germOpenIso_inv X R y F i) s)

/-- `toPresheafFiber_germOpenIso_hom` at the index of an explicit open neighbourhood. -/
@[reassoc (attr := simp)]
theorem toPresheafFiber_germOpenIso_hom_mk (y : localizedSpaceFunctor.obj X)
    (F : Sheaf (etaleTopology X) (ModuleCat.{max u (v + 1) uL} R))
    (U : Opens (localizedSpaceFunctor.obj X)) (hy : y ∈ U) :
    (underlyingTopologyPoint.{u, v, uL} X y).toPresheafFiber U ⟨⟨hy⟩⟩
        ((etaleUnderlyingSheaf X (ModuleCat.{max u (v + 1) uL} R)).obj F).obj ≫
        (germOpenIso X R y).hom.app F =
      GaloisGerms.germι (etaleTopology X) R (nbhdEtale.{u, v, uL} X y) F (nbhdIndex.mk U hy) :=
  toPresheafFiber_germOpenIso_hom X R y F (nbhdIndex.mk U hy)

/-- Elementwise form of `toPresheafFiber_germOpenIso_hom_mk`. -/
@[simp]
theorem germOpenIso_hom_app_toPresheafFiber_mk_apply (y : localizedSpaceFunctor.obj X)
    (F : Sheaf (etaleTopology X) (ModuleCat.{max u (v + 1) uL} R))
    (U : Opens (localizedSpaceFunctor.obj X)) (hy : y ∈ U)
    (s : F.obj.obj (op (openEtaleObject X U))) :
    (germOpenIso X R y).hom.app F
        ((underlyingTopologyPoint.{u, v, uL} X y).toPresheafFiber U ⟨⟨hy⟩⟩
          ((etaleUnderlyingSheaf X (ModuleCat.{max u (v + 1) uL} R)).obj F).obj s) =
      GaloisGerms.germι (etaleTopology X) R (nbhdEtale.{u, v, uL} X y) F (nbhdIndex.mk U hy) s :=
  germOpenIso_hom_app_toPresheafFiber_apply X R y F (nbhdIndex.mk U hy) s

/-- Ordinary germ cohomology is the right derived functor of the germ along the
neighbourhood system of open-domain objects. -/
def germCohomologyIso (y : localizedSpaceFunctor.obj X) (q : ℕ) :
    haveI := etale_hasSheafify.{u, v, uL} X R
    haveI := etale_enoughInjectives.{u, v, uL} X R
    etaleUnderlyingGermCohomology.{u, v, uL} X R y q ≅
      (GaloisGerms.germ (etaleTopology X) R (nbhdEtale.{u, v, uL} X y)).rightDerived q :=
  haveI := etale_hasSheafify.{u, v, uL} X R
  haveI := underlyingTopology_hasSheafify.{u, v, uL} X R
  haveI := etale_enoughInjectives.{u, v, uL} X R
  letI : (etaleUnderlyingSheaf X (ModuleCat.{max u (v + 1) uL} R)).Additive :=
    etaleUnderlyingSheaf_additive.{u, v, uL} X R
  haveI : ((underlyingTopologyPoint.{u, v, uL} X y).sheafFiber
      (A := ModuleCat.{max u (v + 1) uL} R)).Additive :=
    Functor.additive_of_preserves_binary_products _
  GaloisCartan.GaloisCechSystem.rightDerivedIsoOfIso (germOpenIso X R y) q

end Langlands.Sheaf.Equivariant.Analytic
