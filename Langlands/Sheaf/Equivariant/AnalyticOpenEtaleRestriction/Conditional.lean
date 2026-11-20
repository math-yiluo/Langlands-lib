import Langlands.Geometry.Analytic.EtaleOpenDomains.Statement
import Mathlib.CategoryTheory.Sites.CoverPreserving
import Mathlib.Topology.Sheaves.Sheaf

/-! # Ordinary restriction given étaleness of the canonical open domains -/

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u v uA vA

namespace Langlands.Sheaf.Equivariant.Analytic.OpenEtaleRestriction

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Langlands.Analytic Langlands.Analytic.SaturatedAtlasPresentation

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable (X : LocalizedCategory.{u, v, v} (K := K))
variable (hOpen : EtaleOpenDomainStatement X)

/-- An actual open analytic domain, regarded as an object of the étale site. -/
def openEtaleObject (U : Opens (localizedSpaceFunctor.obj X)) : EtaleSite X :=
  MorphismProperty.Over.mk ⊤
    (domainι X ((presentationOf X).openDomain (U : Set (localizedSpaceFunctor.obj X)) U.isOpen))
    (hOpen U U.isOpen)

/-- A morphism into an open domain is determined by its map to the base. -/
instance openEtaleObject_hom_subsingleton (W : EtaleSite X)
    (U : Opens (localizedSpaceFunctor.obj X)) :
    Subsingleton (W ⟶ openEtaleObject X hOpen U) where
  allEq f g := by
    apply MorphismProperty.Over.Hom.ext
    apply (cancel_mono
      (domainι X ((presentationOf X).openDomain (U : Set (localizedSpaceFunctor.obj X)) U.isOpen))).1
    exact (MorphismProperty.Over.w f).trans (MorphismProperty.Over.w g).symm

/-- Factor an actual étale object through an open domain containing its image. -/
def openEtaleLift (U : Opens (localizedSpaceFunctor.obj X)) (W : EtaleSite X)
    (hW : ∀ y, localizedSpaceFunctor.map W.hom y ∈ U) :
    W ⟶ openEtaleObject X hOpen U :=
  MorphismProperty.Over.homMk
    (domainLift ((presentationOf X).openDomain (U : Set (localizedSpaceFunctor.obj X)) U.isOpen)
      W.hom hW)
    (domainLift_comp _ _ _)

/-- Every map to the open-domain object has image in that open. -/
theorem mem_open_of_openEtale_hom {U : Opens (localizedSpaceFunctor.obj X)}
    {W : EtaleSite X} (f : W ⟶ openEtaleObject X hOpen U)
    (y : localizedSpaceFunctor.obj W.left) :
    localizedSpaceFunctor.map W.hom y ∈ U := by
  have hw := congrArg (fun k => localizedSpaceFunctor.map k y)
    (MorphismProperty.Over.w f)
  change localizedSpaceFunctor.map
    (f.left ≫ domainι X ((presentationOf X).openDomain (U : Set (localizedSpaceFunctor.obj X)) U.isOpen)) y =
      localizedSpaceFunctor.map W.hom y at hw
  rw [CategoryTheory.Functor.map_comp, TopCat.comp_app] at hw
  have hv := domainι_apply
    ((presentationOf X).openDomain (U : Set (localizedSpaceFunctor.obj X)) U.isOpen)
    (localizedSpaceFunctor.map f.left y)
  exact (hv.symm.trans hw) ▸ (localizedSpaceFunctor.map f.left y).property

/-- Inclusion of open sets is the canonical factorization of domain inclusions. -/
def openEtaleMap {U V : Opens (localizedSpaceFunctor.obj X)} (f : U ⟶ V) :
    openEtaleObject X hOpen U ⟶ openEtaleObject X hOpen V :=
  openEtaleLift X hOpen V (openEtaleObject X hOpen U) (fun y => by
    change localizedSpaceFunctor.map
      (domainι X ((presentationOf X).openDomain (U : Set (localizedSpaceFunctor.obj X)) U.isOpen)) y ∈ V
    rw [domainι_apply]
    exact f.le y.property)

/-- The actual ordinary-open site maps into the actual étale site. -/
def openEtaleFunctor : Opens (localizedSpaceFunctor.obj X) ⥤ EtaleSite X where
  obj := openEtaleObject X hOpen
  map := openEtaleMap X hOpen
  map_id _ := Subsingleton.elim _ _
  map_comp _ _ := Subsingleton.elim _ _

/-- The map between two open-domain spaces retains the ambient point. -/
theorem openEtaleMap_apply_val {U V : Opens (localizedSpaceFunctor.obj X)} (f : U ⟶ V)
    (y : localizedSpaceFunctor.obj (openEtaleObject X hOpen U).left) :
    (localizedSpaceFunctor.map (openEtaleMap X hOpen f).left y).val = y.val := by
  have hw := congrArg (fun k => localizedSpaceFunctor.map k y)
    (MorphismProperty.Over.w (openEtaleMap X hOpen f))
  change localizedSpaceFunctor.map
    ((openEtaleMap X hOpen f).left ≫
      domainι X ((presentationOf X).openDomain (V : Set (localizedSpaceFunctor.obj X)) V.isOpen)) y =
      localizedSpaceFunctor.map
        (domainι X ((presentationOf X).openDomain (U : Set (localizedSpaceFunctor.obj X)) U.isOpen)) y at hw
  rw [CategoryTheory.Functor.map_comp, TopCat.comp_app] at hw
  have hV := domainι_apply
    ((presentationOf X).openDomain (V : Set (localizedSpaceFunctor.obj X)) V.isOpen)
    (localizedSpaceFunctor.map (openEtaleMap X hOpen f).left y)
  have hU := domainι_apply
    ((presentationOf X).openDomain (U : Set (localizedSpaceFunctor.obj X)) U.isOpen) y
  exact (hV.symm.trans hw).trans hU

/-- The underlying map of an open inclusion is the usual inclusion of subtypes. -/
theorem openEtaleMap_apply {U V : Opens (localizedSpaceFunctor.obj X)} (f : U ⟶ V)
    (y : localizedSpaceFunctor.obj (openEtaleObject X hOpen U).left) :
    localizedSpaceFunctor.map (openEtaleMap X hOpen f).left y = Opens.inclusion f.le y :=
  Subtype.ext (openEtaleMap_apply_val X hOpen f y)

/-- Images of actual opens preserve finite cones of maps from every étale object. -/
instance openEtaleFunctor_representablyFlat : RepresentablyFlat (openEtaleFunctor X hOpen) where
  cofiltered W := by
    have : Nonempty (StructuredArrow W (openEtaleFunctor X hOpen)) :=
      ⟨StructuredArrow.mk (Y := ⊤) (openEtaleLift X hOpen ⊤ W (fun _ => trivial))⟩
    refine
      { cone_objs := fun A B => ?_
        cone_maps := fun {A B} f g => ?_ }
    · let C : StructuredArrow W (openEtaleFunctor X hOpen) :=
        StructuredArrow.mk (Y := A.right ⊓ B.right)
          (openEtaleLift X hOpen (A.right ⊓ B.right) W (fun y =>
            ⟨mem_open_of_openEtale_hom X hOpen A.hom y,
              mem_open_of_openEtale_hom X hOpen B.hom y⟩))
      exact ⟨C,
        StructuredArrow.homMk (homOfLE inf_le_left)
          ((openEtaleObject_hom_subsingleton X hOpen W A.right).allEq _ _),
        StructuredArrow.homMk (homOfLE inf_le_right)
          ((openEtaleObject_hom_subsingleton X hOpen W B.right).allEq _ _), trivial⟩
    · refine ⟨A, 𝟙 A, ?_⟩
      apply StructuredArrow.hom_ext
      exact Subsingleton.elim _ _

/-- A covering family of ordinary opens jointly covers their actual domain spaces. -/
theorem openEtaleFunctor_coverPreserving :
    CoverPreserving (Opens.grothendieckTopology (localizedSpaceFunctor.obj X))
      (etaleTopology X) (openEtaleFunctor X hOpen) where
  cover_preserve {U S} hS := by
    apply mem_etaleTopology_of_jointlySurjective
    intro y
    obtain ⟨V, f, hf, hy⟩ := hS y.val y.property
    refine ⟨openEtaleObject X hOpen V, openEtaleMap X hOpen f,
      Sieve.image_mem_functorPushforward (openEtaleFunctor X hOpen) S hf, ?_⟩
    refine ⟨⟨y.val, hy⟩, ?_⟩
    apply Subtype.ext
    exact openEtaleMap_apply_val X hOpen f _

/-- Precomposition with canonical open domains takes actual étale sheaves to sheaves. -/
instance openEtaleFunctor_isContinuous :
    (openEtaleFunctor X hOpen).IsContinuous
      (Opens.grothendieckTopology (localizedSpaceFunctor.obj X)) (etaleTopology X) :=
  Functor.isContinuous_of_coverPreserving (compatiblePreservingOfFlat _ _)
    (openEtaleFunctor_coverPreserving X hOpen)

variable (A : Type uA) [Category.{vA} A]

/-- The actual étale sheaf restricted to the ordinary underlying topology. -/
def etaleUnderlyingSheaf :
    Sheaf (etaleTopology X) A ⥤ TopCat.Sheaf A (localizedSpaceFunctor.obj X) :=
  (openEtaleFunctor X hOpen).sheafPushforwardContinuous A
    (Opens.grothendieckTopology (localizedSpaceFunctor.obj X)) (etaleTopology X)

/-- The underlying presheaf is precomposition by the opposite of the open-domain functor. -/
theorem etaleUnderlyingSheaf_presheaf (F : Sheaf (etaleTopology X) A) :
    ((etaleUnderlyingSheaf X hOpen A).obj F).obj = (openEtaleFunctor X hOpen).op ⋙ F.obj :=
  rfl

/-- The ordinary-open sections are the original sections over the actual analytic domain. -/
theorem etaleUnderlyingSheaf_obj_obj (F : Sheaf (etaleTopology X) A)
    (U : Opens (localizedSpaceFunctor.obj X)) :
    ((etaleUnderlyingSheaf X hOpen A).obj F).obj.obj (op U) =
      F.obj.obj (op (openEtaleObject X hOpen U)) := rfl

/-- Ordinary restrictions evaluate the original étale presheaf on the domain factorization. -/
theorem etaleUnderlyingSheaf_obj_map (F : Sheaf (etaleTopology X) A)
    {U V : Opens (localizedSpaceFunctor.obj X)} (f : U ⟶ V) :
    ((etaleUnderlyingSheaf X hOpen A).obj F).obj.map f.op =
      F.obj.map (openEtaleMap X hOpen f).op := rfl

end Langlands.Sheaf.Equivariant.Analytic.OpenEtaleRestriction
