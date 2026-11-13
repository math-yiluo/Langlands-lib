import Langlands.GroupScheme.SimplyConnected.SpecialLinearTitsCocyclePresentation
import Langlands.GroupScheme.Rational.TorusCompatibleGaloisDiscrepancy

/-! # The coordinate Galois discrepancy and its torus action -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

noncomputable section
universe u
open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.SpecialLinearTitsCocycle

/-- The actual finite-coordinate diagonal inclusion commutes with change of model. -/
theorem diagonalTorus_baseChange (n : ℕ) {R R' : CommRingCat.{u}} (b : Spec R' ⟶ Spec R) :
    (GroupScheme.baseChange b).map (SpecialLinear.FinSucc.diagonalTorus n R) ≫
        (SpecialLinear.baseChangeModelIso (Fin (n + 1)) b).hom =
      CommGroupScheme.groupHom (splitTorus.commBaseChangeIso b (ULift (Fin n))).hom ≫
        SpecialLinear.FinSucc.diagonalTorus n R' := by
  apply hom_ext_points
  intro U x
  apply (SpecialLinear.pointsEquiv (Fin (n + 1)) R' U).injective
  rw [Grp.comp_hom_hom, ← Category.assoc,
    SpecialLinear.pointsEquiv_baseChangeModelIso_hom,
    baseChangePointsEquiv_comp, SpecialLinear.FinSucc.pointsEquiv_diagonalTorus,
    Grp.comp_hom_hom, ← Category.assoc, SpecialLinear.FinSucc.pointsEquiv_diagonalTorus]
  congr 1
  exact (splitTorus.pointsEquiv_baseChangeIso_hom b (ULift (Fin n)) U x).symm

private def commIsoToGroupIso {S : Scheme.{u}} {D T : CommGroupScheme S} (t : D ≅ T) :
    D.toGrp ≅ T.toGrp where
  hom := CommGroupScheme.groupHom t.hom
  inv := CommGroupScheme.groupHom t.inv
  hom_inv_id := congrArg CommGroupScheme.groupHom t.hom_inv_id
  inv_hom_id := congrArg CommGroupScheme.groupHom t.inv_hom_id

private theorem conjugate_square {C : Type*} [Category C]
    {D T G H : C} (i : D ⟶ G) (j : T ⟶ H) (E : G ≅ H) (t : D ≅ T)
    (f : G ≅ G) (s : D ≅ D)
    (hmodel : i ≫ E.hom = t.hom ≫ j) (hdis : i ≫ f.hom = s.hom ≫ i) :
    j ≫ (E.symm ≪≫ f ≪≫ E).hom = (t.symm ≪≫ s ≪≫ t).hom ≫ j := by
  apply (cancel_epi t.hom).mp
  simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc]
  calc
    t.hom ≫ j ≫ E.inv ≫ f.hom ≫ E.hom = i ≫ f.hom ≫ E.hom := by
      rw [← Category.assoc t.hom j, ← hmodel]
      simp only [Category.assoc, Iso.hom_inv_id_assoc]
    _ = s.hom ≫ t.hom ≫ j := by
      rw [← Category.assoc, hdis, Category.assoc, hmodel]
    _ = t.hom ≫ t.inv ≫ s.hom ≫ t.hom ≫ j := by
      simp only [Iso.hom_inv_id_assoc]

variable {K : Type u} [Field K]
  {G : GroupScheme (Spec (CommRingCat.of K))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom] {d : TitsIndexData G} {n : ℕ} {e : d.Vertex ≃ Fin n}

/-- The split pinning on the fixed coordinate diagonal torus. -/
def Presentation.coordinatePinning (p : Presentation d e) :=
  SpecialLinearTitsCocycle.coordinatePinning n p.coordinate.rootDatum p.coordinate.isRootDatum
    p.coordinate.isReduced p.coordinate.base

/-- The torus identification underlying the base-change presentation. -/
def Presentation.baseChangeTorusIso (p : Presentation d e) :
    (CommGroupScheme.baseChange (algebraBaseMap K p.L)).obj
        (splitTorus.commGroupScheme (Spec (CommRingCat.of K)) (ULift (Fin n))) ≅
      (CommGroupScheme.baseChange (algebraBaseMap K p.L)).obj p.stage.torus :=
  splitTorus.commBaseChangeIso (algebraBaseMap K p.L) (ULift (Fin n)) ≪≫
    p.coordinate.pinningIso.torusIso

/-- The full presentation respects the actual ground-field torus inclusions. -/
theorem Presentation.baseChange_square (p : Presentation d e) :
    (GroupScheme.baseChange (algebraBaseMap K p.L)).map
        (SpecialLinear.FinSucc.diagonalTorus n (CommRingCat.of K)) ≫ p.baseChangeIso.hom =
      CommGroupScheme.groupHom p.baseChangeTorusIso.hom ≫
        (GroupScheme.baseChange (algebraBaseMap K p.L)).map p.stage.inclusion := by
  change _ ≫ ((SpecialLinear.baseChangeModelIso (Fin (n + 1))
    (algebraBaseMap K p.L)).hom ≫ p.coordinate.pinningIso.groupIso.hom) = _
  have h := p.coordinate.pinningIso.square
  change SpecialLinear.FinSucc.diagonalTorus n (CommRingCat.of p.L) ≫
    p.coordinate.pinningIso.groupIso.hom = _ at h
  rw [← Category.assoc, diagonalTorus_baseChange, Category.assoc, h, ← Category.assoc]
  rfl

/-- The discrepancy on the actual split special linear model over the stage field. -/
def Presentation.discrepancyIso (p : Presentation d e) (σ : p.L ≃ₐ[K] p.L) :
    SpecialLinear.groupScheme (Fin (n + 1)) (CommRingCat.of p.L) ≅
      SpecialLinear.groupScheme (Fin (n + 1)) (CommRingCat.of p.L) :=
  (SpecialLinear.baseChangeModelIso (Fin (n + 1)) (algebraBaseMap K p.L)).symm ≪≫
    GaloisDiscrepancy.groupIso p.baseChangeIso σ ≪≫
      SpecialLinear.baseChangeModelIso (Fin (n + 1)) (algebraBaseMap K p.L)

/-- The discrepancy on the coordinate torus, with the same model comparisons. -/
def Presentation.discrepancyTorusIso (p : Presentation d e) (σ : p.L ≃ₐ[K] p.L) :
    p.coordinatePinning.torus ≅ p.coordinatePinning.torus :=
  (splitTorus.commBaseChangeIso (algebraBaseMap K p.L) (ULift (Fin n))).symm ≪≫
    GaloisDiscrepancy.torusIso p.baseChangeTorusIso σ ≪≫
      splitTorus.commBaseChangeIso (algebraBaseMap K p.L) (ULift (Fin n))

/-- The coordinate discrepancy preserves the actual coordinate diagonal torus. -/
theorem Presentation.discrepancy_square (p : Presentation d e) (σ : p.L ≃ₐ[K] p.L) :
    p.coordinatePinning.inclusion ≫ (p.discrepancyIso σ).hom =
      CommGroupScheme.groupHom (p.discrepancyTorusIso σ).hom ≫
        p.coordinatePinning.inclusion := by
  exact conjugate_square _ _ _
    (commIsoToGroupIso (splitTorus.commBaseChangeIso (algebraBaseMap K p.L) (ULift (Fin n))))
    _ (commIsoToGroupIso (GaloisDiscrepancy.torusIso p.baseChangeTorusIso σ))
    (diagonalTorus_baseChange n (algebraBaseMap K p.L))
    (GaloisDiscrepancy.square _ _ p.baseChangeIso p.baseChangeTorusIso
      p.baseChange_square σ)

/-- On characters the coordinate discrepancy is the inverse ordinary stage Galois
 action, transported by the actual coordinate torus identification. -/
theorem Presentation.discrepancyTorusIso_character (p : Presentation d e)
    (σ : p.L ≃ₐ[K] p.L) (χ : characterLattice p.coordinatePinning.torus) :
    (p.discrepancyTorusIso σ).hom ≫ χ =
      p.coordinate.pinningIso.torusIso.hom ≫
        characterLattice.galoisRepresentation K p.L p.stage.torus σ⁻¹
          (p.coordinate.pinningIso.torusIso.inv ≫ χ) := by
  let b := splitTorus.commBaseChangeIso (algebraBaseMap K p.L) (ULift (Fin n))
  have h := GaloisDiscrepancy.torusIso_character
    (isSplitTorus_splitTorus (S := Spec (CommRingCat.of K)) (ULift (Fin n)))
    p.baseChangeTorusIso σ (b.hom ≫ χ)
  change (b.inv ≫ (GaloisDiscrepancy.torusIso p.baseChangeTorusIso σ).hom ≫ b.hom) ≫ χ = _
  rw [Category.assoc, Category.assoc, h]
  simp only [Presentation.baseChangeTorusIso, Iso.trans_hom, Iso.trans_inv, b,
    Category.assoc, Iso.inv_hom_id_assoc]

end Langlands.GroupScheme.SpecialLinearTitsCocycle
