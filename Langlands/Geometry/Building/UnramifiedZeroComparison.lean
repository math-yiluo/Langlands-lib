import Langlands.Geometry.Building.SimplyConnectedImageNormal
import Langlands.GroupScheme.Rational.ParabolicPointConjugation

/-! # Comparing unramified zero subgroups through torus norm images -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open Langlands.GroupScheme
open scoped CategoryTheory.MonObj

namespace Langlands.Geometry.Building.UnramifiedZeroDatum

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {H H' : GroupScheme (Spec (CommRingCat.of (UnramifiedClosure F)))}

/-- Equal ambient torus norm images give equal zero subgroups, independently
of the derived subgroup and its simply connected cover. -/
theorem zeroPoints_eq_of_torusIwahori_image_eq (E E' : UnramifiedZeroDatum F H)
    (hT : E.torusIwahori.map (rationalPoints.map E.i) =
      E'.torusIwahori.map (rationalPoints.map E'.i)) :
    E.zeroPoints = E'.zeroPoints := by
  rw [zeroPoints, zeroPoints, E.simplyConnectedImage_eq E', hT]

/-- An ambient isomorphism carries the zero subgroup to the target zero
subgroup if it does so for the torus norm images. -/
theorem map_zeroPoints_eq_of_torusIwahori_image_eq
    (E : UnramifiedZeroDatum F H) (E' : UnramifiedZeroDatum F H') (e : H ≅ H')
    (hT : (E.torusIwahori.map (rationalPoints.map E.i)).map (rationalPoints.map e.hom) =
      E'.torusIwahori.map (rationalPoints.map E'.i)) :
    E.zeroPoints.map (rationalPoints.map e.hom) = E'.zeroPoints := by
  rw [zeroPoints, zeroPoints, Subgroup.map_sup, hT]
  exact congrArg (fun N => N ⊔ E'.torusIwahori.map (rationalPoints.map E'.i))
    (Building.map_simplyConnectedImage_eq E.isSimplyConnectedDerivedCover
      E'.isSimplyConnectedDerivedCover e)

/-- The restriction of a compatible ambient isomorphism to the zero subgroups. -/
def zeroPointsEquivOfTorusIwahoriImageEq
    (E : UnramifiedZeroDatum F H) (E' : UnramifiedZeroDatum F H') (e : H ≅ H')
    (hT : (E.torusIwahori.map (rationalPoints.map E.i)).map (rationalPoints.map e.hom) =
      E'.torusIwahori.map (rationalPoints.map E'.i)) :
    E.zeroPoints ≃* E'.zeroPoints :=
  ((isoPointsEquiv e (Over.mk (𝟙 _))).subgroupMap E.zeroPoints).trans
    (MulEquiv.subgroupCongr (E.map_zeroPoints_eq_of_torusIwahori_image_eq E' e hT))

@[simp]
theorem coe_zeroPointsEquivOfTorusIwahoriImageEq_apply
    (E : UnramifiedZeroDatum F H) (E' : UnramifiedZeroDatum F H') (e : H ≅ H')
    (hT : (E.torusIwahori.map (rationalPoints.map E.i)).map (rationalPoints.map e.hom) =
      E'.torusIwahori.map (rationalPoints.map E'.i))
    (x : E.zeroPoints) :
    (E.zeroPointsEquivOfTorusIwahoriImageEq E' e hT x : rationalPoints H') =
      rationalPoints.map e.hom x :=
  rfl

/-- Conjugation by an element of the zero subgroup preserves that subgroup. -/
theorem map_zeroPoints_inner_eq (E : UnramifiedZeroDatum F H)
    {g : rationalPoints H} (hg : g ∈ E.zeroPoints) :
    E.zeroPoints.map (rationalPoints.map (H.innerIso g).hom) = E.zeroPoints := by
  rw [rationalPoints_map_innerIso]
  exact Subgroup.mem_normalizer_iff_map_conj_eq.mp (E.zeroPoints.le_normalizer hg)

/-- A conjugation by an element of the simply connected image that carries the
torus norm image to the other one gives equal zero subgroups. -/
theorem zeroPoints_eq_of_sharp_conjugation (E E' : UnramifiedZeroDatum F H)
    (g : rationalPoints H) (hg : g ∈ E.simplyConnectedImage)
    (hT : (E.torusIwahori.map (rationalPoints.map E.i)).map
        (rationalPoints.map (H.innerIso g).hom) =
      E'.torusIwahori.map (rationalPoints.map E'.i)) :
    E.zeroPoints = E'.zeroPoints := by
  rw [← E.map_zeroPoints_inner_eq (E.simplyConnectedImage_le_zeroPoints hg)]
  exact E.map_zeroPoints_eq_of_torusIwahori_image_eq E' (H.innerIso g) hT

/-- Compatible isomorphisms of tori and their norm subgroups reduce sharp
conjugacy to the preceding ambient-image comparison. -/
theorem zeroPoints_eq_of_sharp_torus_iso (E E' : UnramifiedZeroDatum F H)
    (g : rationalPoints H) (hg : g ∈ E.simplyConnectedImage)
    (e : E.T.toGrp ≅ E'.T.toGrp)
    (he : E.i ≫ (H.innerIso g).hom = e.hom ≫ E'.i)
    (hT : E.torusIwahori.map (rationalPoints.map e.hom) = E'.torusIwahori) :
    E.zeroPoints = E'.zeroPoints := by
  apply E.zeroPoints_eq_of_sharp_conjugation E' g hg
  have hm : (rationalPoints.map (H.innerIso g).hom).comp (rationalPoints.map E.i) =
      (rationalPoints.map E'.i).comp (rationalPoints.map e.hom) := by
    apply MonoidHom.ext
    intro x
    simpa only [MonoidHom.comp_apply, rationalPoints.map_apply, Category.assoc,
      ← Grp.comp_hom_hom] using congrArg
        (fun f : E.T.toGrp ⟶ H => x ≫ f.hom.hom) he
  rw [Subgroup.map_map, hm, ← Subgroup.map_map, hT]

end Langlands.Geometry.Building.UnramifiedZeroDatum
