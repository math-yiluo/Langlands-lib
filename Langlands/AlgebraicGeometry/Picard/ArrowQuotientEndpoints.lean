import Langlands.AlgebraicGeometry.Picard.SmoothArrowRelation
import Langlands.AlgebraicGeometry.AlgebraicSpace.SmoothRelationQuotientDescent
import Langlands.AlgebraicGeometry.Sites.EtaleFppfComparison
import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono

/-! # Endpoints of the canonical sheaf of Picard arrow classes -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

noncomputable section

namespace Langlands.AlgebraicGeometry.Picard.PicardGroupoid

open AlgebraicSpace.SmoothRelationQuotient

variable {S X : Scheme.{u}}

/-- Endpoint pairs are represented by the actual product of the object atlas
with itself over the base. -/
def atlasEndpointIso (U : Over S) :
    (AlgebraicSpace.schemeYoneda S).obj (Limits.prod U U) ≅ atlasEndpointPresheaf U where
  hom :=
    { app := fun _ ↦ ↾fun x ↦ ULift.up
        (x.down ≫ Limits.prod.fst, x.down ≫ Limits.prod.snd)
      naturality := by
        intro T V g
        apply ConcreteCategory.hom_ext
        intro x
        exact congrArg ULift.up
          (Prod.ext (Category.assoc _ _ _) (Category.assoc _ _ _)) }
  inv :=
    { app := fun _ ↦ ↾fun x ↦ ULift.up (Limits.prod.lift x.down.1 x.down.2)
      naturality := by
        intro T V g
        apply ConcreteCategory.hom_ext
        intro x
        apply congrArg ULift.up
        change Limits.prod.lift (g.unop ≫ x.down.1) (g.unop ≫ x.down.2) =
          g.unop ≫ Limits.prod.lift x.down.1 x.down.2
        apply Limits.prod.hom_ext <;> simp }
  hom_inv_id := by
    ext T x
    apply congrArg ULift.up
    change Limits.prod.lift (x.down ≫ Limits.prod.fst) (x.down ≫ Limits.prod.snd) = x.down
    apply Limits.prod.hom_ext <;> simp
  inv_hom_id := by
    ext T x
    apply congrArg ULift.up
    exact Prod.ext (Limits.prod.lift_fst _ _) (Limits.prod.lift_snd _ _)

/-- Complete endpoint pairs form an etale sheaf. -/
lemma atlasEndpointPresheaf_isSheaf (U : Over S) :
    CategoryTheory.Presheaf.IsSheaf (Scheme.etaleTopology.over S)
      (atlasEndpointPresheaf U) :=
  (CategoryTheory.Presheaf.isSheaf_of_iso_iff (atlasEndpointIso U)).mp
    ((((AlgebraicSpace.schemeSheaf S).obj (Limits.prod U U)).property).of_le
      (Sites.etaleTopologyOver_le_fppfTopologyOver S))

/-- The first component of the complete endpoint pair. -/
def atlasEndpointFst (U : Over S) :
    atlasEndpointPresheaf U ⟶ (AlgebraicSpace.schemeYoneda S).obj U where
  app _ := ↾fun x ↦ ULift.up x.down.1
  naturality _ _ _ := rfl

/-- The second component of the complete endpoint pair. -/
def atlasEndpointSnd (U : Over S) :
    atlasEndpointPresheaf U ⟶ (AlgebraicSpace.schemeYoneda S).obj U where
  app _ := ↾fun x ↦ ULift.up x.down.2
  naturality _ _ _ := rfl

variable (f : X ⟶ S) {U : Over S} (L : LineBundle ((relativeSpace f).obj U))
  {A R : Over S} (r s : R ⟶ A)
  (eA : (AlgebraicSpace.schemeYoneda S).obj A ≅ atlasArrowPresheaf f L)
  (h : IsPullback ((AlgebraicSpace.schemeYoneda S).map r)
    ((AlgebraicSpace.schemeYoneda S).map s)
    (eA.hom ≫ atlasArrowEndpoint f L) (eA.hom ≫ atlasArrowEndpoint f L))

/-- Both actual endpoints descend through the fixed canonical etale quotient,
including sections with only local representatives. -/
def arrowKernelQuotientEndpoint :
    (arrowKernelQuotientSheaf f L r s eA h).obj ⟶ atlasEndpointPresheaf U :=
  quotientSheafDesc ((AlgebraicSpace.schemeToSpace S).obj R)
    ((AlgebraicSpace.schemeYoneda S).map r) ((AlgebraicSpace.schemeYoneda S).map s)
    (representedKernel_isEquivalenceRelation r s _ h)
    (eA.hom ≫ atlasArrowEndpoint f L) h.w (atlasEndpointPresheaf_isSheaf U)

/-- The descended pair agrees with the actual endpoints on the entire arrow
presheaf. -/
@[simp]
lemma arrowKernelQuotientMap_endpoint :
    arrowKernelQuotientMap f L r s eA h ≫
        arrowKernelQuotientEndpoint f L r s eA h =
      eA.hom ≫ atlasArrowEndpoint f L :=
  quotientMap_desc _ _ _ _ _ _ _

/-- The endpoint map on pointwise arrow classes is a monomorphism because the
relation is the full endpoint kernel. -/
lemma arrowKernelQuotientPresheafEndpoint_mono :
    Mono (quotientPresheafDesc ((AlgebraicSpace.schemeToSpace S).obj R)
      ((AlgebraicSpace.schemeYoneda S).map r) ((AlgebraicSpace.schemeYoneda S).map s)
      (representedKernel_isEquivalenceRelation r s _ h)
      (eA.hom ≫ atlasArrowEndpoint f L) h.w) := by
  apply (NatTrans.mono_iff_mono_app _).mpr
  intro T
  apply (mono_iff_injective _).mpr
  intro x y hxy
  induction x using Quotient.ind with
  | _ a =>
    induction y using Quotient.ind with
    | _ b =>
      exact Quotient.sound (Types.exists_of_isPullback (h.app T) a b hxy)

/-- Left exact etale sheafification retains endpoint injectivity on every
section of the canonical arrow-class sheaf. -/
lemma arrowKernelQuotientEndpoint_mono :
    Mono (arrowKernelQuotientEndpoint f L r s eA h) := by
  let c := quotientPresheafDesc ((AlgebraicSpace.schemeToSpace S).obj R)
    ((AlgebraicSpace.schemeYoneda S).map r) ((AlgebraicSpace.schemeYoneda S).map s)
    (representedKernel_isEquivalenceRelation r s _ h)
    (eA.hom ≫ atlasArrowEndpoint f L) h.w
  let : Mono c := arrowKernelQuotientPresheafEndpoint_mono f L r s eA h
  let : Mono (sheafifyMap (Scheme.etaleTopology.over S) c) :=
    inferInstanceAs (Mono ((sheafification (Scheme.etaleTopology.over S)
      (Type (u + 1))).map c))
  have heq : arrowKernelQuotientEndpoint f L r s eA h =
      sheafifyMap (Scheme.etaleTopology.over S) c ≫
        (isoSheafify (Scheme.etaleTopology.over S) (atlasEndpointPresheaf_isSheaf U)).inv := by
    rw [isoSheafify_inv, sheafifyMap_sheafifyLift, Category.comp_id]
    rfl
  rw [heq]
  exact mono_comp'
    (inferInstanceAs (Mono (sheafifyMap (Scheme.etaleTopology.over S) c)))
    (inferInstanceAs (Mono
      (isoSheafify (Scheme.etaleTopology.over S) (atlasEndpointPresheaf_isSheaf U)).inv))

/-- The descended first endpoint. -/
def arrowKernelQuotientFst :
    (arrowKernelQuotientSheaf f L r s eA h).obj ⟶
      (AlgebraicSpace.schemeYoneda S).obj U :=
  arrowKernelQuotientEndpoint f L r s eA h ≫ atlasEndpointFst U

/-- The descended second endpoint. -/
def arrowKernelQuotientSnd :
    (arrowKernelQuotientSheaf f L r s eA h).obj ⟶
      (AlgebraicSpace.schemeYoneda S).obj U :=
  arrowKernelQuotientEndpoint f L r s eA h ≫ atlasEndpointSnd U

/-- The two descended endpoints recover the original first endpoint. -/
@[simp]
lemma arrowKernelQuotientMap_fst :
    arrowKernelQuotientMap f L r s eA h ≫ arrowKernelQuotientFst f L r s eA h =
      eA.hom ≫ atlasArrowFst f L := by
  rw [arrowKernelQuotientFst, ← Category.assoc, arrowKernelQuotientMap_endpoint,
    Category.assoc]
  rfl

/-- The two descended endpoints recover the original second endpoint. -/
@[simp]
lemma arrowKernelQuotientMap_snd :
    arrowKernelQuotientMap f L r s eA h ≫ arrowKernelQuotientSnd f L r s eA h =
      eA.hom ≫ atlasArrowSnd f L := by
  rw [arrowKernelQuotientSnd, ← Category.assoc, arrowKernelQuotientMap_endpoint,
    Category.assoc]
  rfl

end Langlands.AlgebraicGeometry.Picard.PicardGroupoid
