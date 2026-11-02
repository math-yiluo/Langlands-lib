import Langlands.AlgebraicGeometry.ProperLocalClosedFibreCover
import Langlands.AlgebraicGeometry.Picard.SmoothValuationGenericLocality
import Langlands.AlgebraicGeometry.Picard.SelfProductBaseChange
import Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_exists_isFrameOn_of_pullback_iso_unit

/-! # Affine total neighbourhoods carrying generic frames -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.AlgebraicGeometry.Picard

variable {X Y : Scheme.{u}} (q : Y ⟶ X) (D : LineBundle Y)

/-- Total trivializing neighbourhoods can be refined to affine total opens
with actual frame sections on their inverse images. -/
theorem exists_affine_generic_frame
    (h : HasGenericTrivializingNeighbourhoods q D) (x : X) :
    ∃ U : X.Opens, IsAffineOpen U ∧ x ∈ U ∧
      ∃ e : Γ(D.obj, q ⁻¹ᵁ U), Scheme.Modules.IsFrameOn e (q ⁻¹ᵁ U) := by
  obtain ⟨a⟩ := h x
  obtain ⟨U, hU, hx, hUa⟩ := Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens a.mem
  obtain ⟨e, he⟩ := Scheme.Modules.exists_isFrameOn_of_pullback_iso_unit
    (q ⁻¹ᵁ a.neighbourhood)
    (((Scheme.Modules.restrictFunctorIsoPullback
      (q ⁻¹ᵁ a.neighbourhood).ι).app D.obj).symm ≪≫ a.trivialization)
  have hpre : q ⁻¹ᵁ U ≤ q ⁻¹ᵁ a.neighbourhood := fun y hy => hUa hy
  exact ⟨U, hU, hx, D.obj.presheaf.map (homOfLE hpre).op e,
    (he.map (homOfLE hpre)).mono hpre⟩

section LocalRing

variable {R : Type u} [CommRing R] [IsLocalRing R]
    (p : X ⟶ Spec (CommRingCat.of R))

/-- An affine neighbourhood of each actual closed-fibre point, together
with an actual frame of the given generic sheaf above that neighbourhood. -/
structure ClosedFibreGenericFrames where
  opens : p.fiber (IsLocalRing.closedPoint R) → X.Opens
  affine : ∀ x, IsAffineOpen (opens x)
  mem : ∀ x, p.fiberι (IsLocalRing.closedPoint R) x ∈ opens x
  frame : ∀ x, Γ(D.obj, q ⁻¹ᵁ opens x)
  isFrame : ∀ x, Scheme.Modules.IsFrameOn (frame x) (q ⁻¹ᵁ opens x)

/-- Choose affine total neighbourhoods and their generic frames from the
pointwise total-neighbourhood result. -/
def closedFibreGenericFramesOfNeighbourhoods
    (h : HasGenericTrivializingNeighbourhoods q D) :
    ClosedFibreGenericFrames q D p := by
  choose U hU hx e he using
    fun x : p.fiber (IsLocalRing.closedPoint R) =>
      exists_affine_generic_frame q D h (p.fiberι (IsLocalRing.closedPoint R) x)
  exact ⟨U, hU, hx, e, he⟩

namespace ClosedFibreGenericFrames

variable {q D p} (F : ClosedFibreGenericFrames q D p)

/-- Under universal closedness, these affine total opens cover the total scheme. -/
theorem iSup_eq_top [UniversallyClosed p] : (⨆ x, F.opens x) = ⊤ :=
  Langlands.AlgebraicGeometry.iSup_eq_top_of_closedFibre_neighbourhoods p F.opens F.mem

/-- The actual total open cover determined by the chosen affine neighbourhoods. -/
def openCover [UniversallyClosed p] : X.OpenCover :=
  Langlands.AlgebraicGeometry.closedFibreNeighbourhoodCover p F.opens F.mem

/-- All chosen total opens contain the same generic point of the closed fibre. -/
theorem commonPoint_mem [Smooth p] [GeometricallyConnected p]
    (x : p.fiber (IsLocalRing.closedPoint R)) :
    Langlands.AlgebraicGeometry.closedFibreGenericPoint p ∈ F.opens x := by
  apply Langlands.AlgebraicGeometry.closedFibreGenericPoint_mem p
  refine ⟨p.fiberι (IsLocalRing.closedPoint R) x, ?_, F.mem x⟩
  exact (p.range_fiberι _).le ⟨x, rfl⟩

end ClosedFibreGenericFrames

end LocalRing

variable {R : Type u} [CommRing R] [IsDomain R] [ValuationRing R]
    (p : X ⟶ Spec (CommRingCat.of R))
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]

/-- Actual generic frames above affine total neighbourhoods of every
closed-fibre point of a smooth valuation scheme. -/
def smoothClosedFibreGenericFrames [Smooth p]
    (D : LineBundle (pullback p (Spec.map (CommRingCat.ofHom (algebraMap R K))))) :
    ClosedFibreGenericFrames (pullback.fst _ _) D p :=
  closedFibreGenericFramesOfNeighbourhoods _ D p
    (hasGenericTrivializingNeighbourhoods_of_smooth K p D)

end Langlands.AlgebraicGeometry.Picard

namespace Langlands.AbelianScheme

open Langlands.AlgebraicGeometry.Picard

variable {R : Type u} [CommRing R] [IsDomain R] [ValuationRing R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    (A : AbelianScheme (Spec (CommRingCat.of R)))

local instance : Smooth (mumfordProduct A).hom := by
  change Smooth (pullback.fst A.X.hom A.X.hom ≫ A.X.hom)
  infer_instance

local instance : UniversallyClosed (mumfordProduct A).hom := by
  change UniversallyClosed (pullback.fst A.X.hom A.X.hom ≫ A.X.hom)
  infer_instance

local instance : GeometricallyConnected (mumfordProduct A).hom := by
  change GeometricallyConnected (pullback.fst A.X.hom A.X.hom ≫ A.X.hom)
  exact GeometricallyConnected.comp (pullback.fst A.X.hom A.X.hom) A.X.hom

/-- The total-neighbourhood result holds for the exact canonical product
map used in the two-axis extension statement and the supplied fraction field. -/
theorem hasGenericTrivializingNeighbourhoods_mumfordProduct
    (D : LineBundle (mumfordProduct
      ((baseChange (Spec.map (CommRingCat.ofHom (algebraMap R K)))).obj A)).left) :
    HasGenericTrivializingNeighbourhoods
      (mumfordProductBaseChangeMap A (Spec.map (CommRingCat.ofHom (algebraMap R K)))) D := by
  let b := Spec.map (CommRingCat.ofHom (algebraMap R K))
  let p := (mumfordProduct A).hom
  let e := mumfordProductBaseChangeIso A b
  have : Smooth p := inferInstanceAs (Smooth (mumfordProduct A).hom)
  apply hasGenericTrivializingNeighbourhoods_of_iso _ e.symm D
  have he : e.inv ≫ mumfordProductBaseChangeMap A b = pullback.fst p b := by
    rw [← mumfordProductBaseChangeIso_hom_fst A b]
    simp only [e, Iso.inv_hom_id_assoc]
    rfl
  change HasGenericTrivializingNeighbourhoods
    (e.inv ≫ mumfordProductBaseChangeMap A b) ((LineBundle.pullback e.inv).obj D)
  rw [he]
  exact hasGenericTrivializingNeighbourhoods_of_smooth K p ((LineBundle.pullback e.inv).obj D)

/-- Affine total neighbourhoods with actual generic frame sections for
the exact canonical self-product map in the extension target. -/
def mumfordProductClosedFibreGenericFrames
    (D : LineBundle (mumfordProduct
      ((baseChange (Spec.map (CommRingCat.ofHom (algebraMap R K)))).obj A)).left) :
    ClosedFibreGenericFrames
      (mumfordProductBaseChangeMap A (Spec.map (CommRingCat.ofHom (algebraMap R K)))) D
      (mumfordProduct A).hom :=
  closedFibreGenericFramesOfNeighbourhoods _ D _
    (hasGenericTrivializingNeighbourhoods_mumfordProduct K A D)

/-- The affine neighbourhoods constructed for the actual product cover it. -/
theorem mumfordProductClosedFibreGenericFrames_iSup
    (D : LineBundle (mumfordProduct
      ((baseChange (Spec.map (CommRingCat.ofHom (algebraMap R K)))).obj A)).left) :
    (⨆ x, (mumfordProductClosedFibreGenericFrames K A D).opens x) = ⊤ :=
  (mumfordProductClosedFibreGenericFrames K A D).iSup_eq_top

/-- All these product neighbourhoods contain the generic point of the
closed fibre, so that frame normalization may use one common total point. -/
theorem mumfordProductClosedFibreGenericFrames_commonPoint
    (D : LineBundle (mumfordProduct
      ((baseChange (Spec.map (CommRingCat.ofHom (algebraMap R K)))).obj A)).left)
    (x : (mumfordProduct A).hom.fiber (IsLocalRing.closedPoint R)) :
    Langlands.AlgebraicGeometry.closedFibreGenericPoint (mumfordProduct A).hom ∈
      (mumfordProductClosedFibreGenericFrames K A D).opens x := by
  exact (mumfordProductClosedFibreGenericFrames K A D).commonPoint_mem x

end Langlands.AbelianScheme
