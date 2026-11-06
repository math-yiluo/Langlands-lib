import Langlands.GroupScheme.Rational.DerivedTorusCentralComplement
import Langlands.GroupScheme.Derived.CenterReduction
import Langlands.GroupScheme.Derived.CentralIntersectionProof
import Langlands.GroupScheme.Derived.MaximalTorusIntersectionReduction

/-! # Actual central products from a derived-torus complement -/

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000

universe u v

open CategoryTheory AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]
    {T S : CommGroupScheme (Spec (CommRingCat.of k))}
    {D G : GroupScheme (Spec (CommRingCat.of k))}
    {e : T ⟶ S} {i : S.toGrp ⟶ G}

namespace DerivedTorusCentralComplement

variable (C : DerivedTorusCentralComplement e i) (d : D ⟶ G)

/-- Multiply the actual central complement and the supplied subgroup. -/
def centralProduct : C.torus.toGrp ⊗ D ⟶ G :=
  prodHom (CommGroupScheme.groupHom C.map ≫ i) d (C.isCentral.commute_values d)

/-- The homomorphism has exactly the prescribed scheme multiplication map. -/
theorem centralProduct_hom :
    (C.centralProduct d).hom.hom =
      subgroupProductMap (CommGroupScheme.groupHom C.map ≫ i) d := by
  have h := comp_prodHom (CommGroupScheme.groupHom C.map ≫ i) d
    (C.isCentral.commute_values d) (C.torus.X ⊗ D.X) (𝟙 _)
  simpa only [centralProduct, Category.id_comp, productPointsEquiv_fst, productPointsEquiv_snd,
    subgroupProductMap] using h

/-- A compatible complement replaces the torus factor in a surjective product. -/
theorem surjective_centralProduct
    (j : T.toGrp ⟶ D)
    (hsquare : j ≫ d = CommGroupScheme.groupHom e ≫ i)
    (hproduct : Surjective (subgroupProductMap d i).left) :
    Surjective (C.centralProduct d).hom.hom.left := by
  let p := RelativeRoot.centralComplementProduct e C.map
  let W := D.X ⊗ (T.X ⊗ C.torus.X)
  let x : W ⟶ D.X := fst _ _
  let y : W ⟶ T.X := snd _ _ ≫ fst _ _
  let z : W ⟶ C.torus.X := snd _ _ ≫ snd _ _
  let f : W ⟶ C.torus.X ⊗ D.X := lift z (x * (y ≫ j.hom.hom))
  have hfac :
      f ≫ subgroupProductMap (CommGroupScheme.groupHom C.map ≫ i) d =
        (D.X ◁ p.hom.hom) ≫ subgroupProductMap d i := by
    have hcomm := commute_of_mem_center (C.isCentral W z)
      ((x * (y ≫ j.hom.hom)) ≫ d.hom.hom)
    have hsq : j.hom.hom ≫ d.hom.hom =
        (CommGroupScheme.groupHom e).hom.hom ≫ i.hom.hom :=
      congrArg (fun a => a.hom.hom) hsquare
    simp only [subgroupProductMap, MonObj.comp_mul, f, lift_fst_assoc, lift_snd_assoc,
      whiskerLeft_fst_assoc, whiskerLeft_snd_assoc]
    change _ = (x ≫ d.hom.hom) *
      ((snd D.X (T.X ⊗ C.torus.X) ≫ p.hom.hom) ≫ i.hom.hom)
    rw [comp_prodHom]
    simp only [productPointsEquiv_fst, productPointsEquiv_snd, Grp.comp_hom_hom,
      MonObj.mul_comp, Category.assoc] at hcomm ⊢
    rw [hcomm.eq, hsq, mul_assoc]
    rfl
  have hp : Surjective (D.X ◁ p.hom.hom).left :=
    MorphismProperty.pullbackMap (P := @Surjective)
      (by change Surjective (𝟙 D.X.left); infer_instance) C.surjective
      (by simp) (Over.w p.hom.hom).symm
  let : Surjective (D.X ◁ p.hom.hom).left := hp
  let : Surjective (subgroupProductMap d i).left := hproduct
  have hcomp : Surjective (f.left ≫
      (subgroupProductMap (CommGroupScheme.groupHom C.map ≫ i) d).left) := by
    change Surjective
      (f ≫ subgroupProductMap (CommGroupScheme.groupHom C.map ≫ i) d).left
    rw [hfac, Over.comp_left]
    infer_instance
  rw [centralProduct_hom]
  exact Surjective.of_comp f.left _

/-- The actual central product is faithfully flat once the prescribed product is surjective. -/
theorem flat_centralProduct
    (hG : IsConnectedReductive G) (hD : IsConnectedReductive D)
    (j : T.toGrp ⟶ D)
    (hsquare : j ≫ d = CommGroupScheme.groupHom e ≫ i)
    (hproduct : Surjective (subgroupProductMap d i).left) :
    Flat (C.centralProduct d).hom.hom.left := by
  let : Smooth G.X.hom := hG.smooth
  let : Smooth D.X.hom := hD.smooth
  let : IsAffineHom D.X.hom := hD.isAffineHom
  let : Smooth C.torus.X.hom := C.isSplit.smooth
  let : Smooth (C.torus.toGrp ⊗ D).X.hom := by
    change Smooth (Limits.pullback.fst C.torus.X.hom D.X.hom ≫ C.torus.X.hom)
    let : Smooth (Limits.pullback.fst C.torus.X.hom D.X.hom) :=
      MorphismProperty.pullback_fst _ _ (hD.smooth)
    infer_instance
  let : IsAffineHom C.torus.X.hom := C.isSplit.isAffineHom
  let : IsAffineHom (C.torus.toGrp ⊗ D).X.hom := by
    change IsAffineHom (Limits.pullback.fst C.torus.X.hom D.X.hom ≫ C.torus.X.hom)
    let : IsAffineHom (Limits.pullback.fst C.torus.X.hom D.X.hom) :=
      MorphismProperty.pullback_fst _ _ (hD.isAffineHom)
    infer_instance
  let : Surjective (C.centralProduct d).hom.hom.left :=
    C.surjective_centralProduct d j hsquare hproduct
  exact flat_of_surjective (C.centralProduct d)

end DerivedTorusCentralComplement

end Langlands.GroupScheme
