import Langlands.GroupScheme.Rational.TorusCompatibleGaloisDiscrepancy
import Langlands.GroupScheme.SimplyConnected.SpecialLinearTitsCocycleAlgebra
import Langlands.GroupScheme.SimplyConnected.SpecialLinearTitsCocycleDiagonal

/-! # Matrix evaluation of the actual Galois discrepancy -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.SpecialLinearTitsCocycle

private theorem conjugateIso_hom {C : Type*} [Category C] {A B : C}
    (m : A ≅ B) (d : A ≅ A) :
    m.hom ≫ (m.symm ≪≫ d ≪≫ m).hom = d.hom ≫ m.hom := by
  simp only [Iso.trans_hom, Iso.symm_hom, Iso.hom_inv_id_assoc]

private theorem conjugateIso_point {S : Scheme.{u}} {A B : GroupScheme S}
    (m : A ≅ B) (d : A ≅ A) {T : Over S} (x : T ⟶ A.X) :
    (x ≫ d.hom.hom.hom) ≫ m.hom.hom.hom =
      (x ≫ m.hom.hom.hom) ≫ (m.symm ≪≫ d ≪≫ m).hom.hom.hom := by
  have h := congrArg (fun f : A ⟶ B => x ≫ f.hom.hom) (conjugateIso_hom m d).symm
  simpa only [Grp.comp_hom_hom, Category.assoc] using h

private theorem localIso_trans_apply {S : Scheme.{u}} {G H J : GroupScheme S}
    {U : Over S}
    (e : (baseChange U.hom).obj G ≅ (baseChange U.hom).obj H)
    (f : (baseChange U.hom).obj H ≅ (baseChange U.hom).obj J)
    {Z : Over S} (a : Z ⟶ U) (g : Z ⟶ G.X) :
    (LocalGroupIso.ofBaseChangeIso (e ≪≫ f)).toFun a g =
      (LocalGroupIso.ofBaseChangeIso f).toFun a
        ((LocalGroupIso.ofBaseChangeIso e).toFun a g) := by
  change LocalGroupIso.coverPointsEquiv J a
      ((LocalGroupIso.coverPointsEquiv G a).symm g ≫
        e.hom.hom.hom ≫ f.hom.hom.hom) =
    LocalGroupIso.coverPointsEquiv J a
      ((LocalGroupIso.coverPointsEquiv H a).symm
        (LocalGroupIso.coverPointsEquiv H a
          ((LocalGroupIso.coverPointsEquiv G a).symm g ≫ e.hom.hom.hom)) ≫
            f.hom.hom.hom)
  rw [MulEquiv.symm_apply_apply]
  rfl

variable {K L : Type u} [Field K] [Field L] [Algebra K L]
  {G : GroupScheme (Spec (CommRingCat.of K))} {n : ℕ}

/-- The actual special-linear model automorphism obtained from the Galois discrepancy. -/
def matrixDiscrepancyIso
    (E : (baseChange (algebraBaseMap K L)).obj
        (SpecialLinear.groupScheme (Fin (n + 1)) (CommRingCat.of K)) ≅
      (baseChange (algebraBaseMap K L)).obj G)
    (σ : L ≃ₐ[K] L) :
    SpecialLinear.groupScheme (Fin (n + 1)) (CommRingCat.of L) ≅
      SpecialLinear.groupScheme (Fin (n + 1)) (CommRingCat.of L) :=
  (SpecialLinear.baseChangeModelIso (Fin (n + 1)) (algebraBaseMap K L)).symm ≪≫
    GaloisDiscrepancy.groupIso E σ ≪≫
      SpecialLinear.baseChangeModelIso (Fin (n + 1)) (algebraBaseMap K L)

private theorem matrixDiscrepancyIso_def
    (E : (baseChange (algebraBaseMap K L)).obj
        (SpecialLinear.groupScheme (Fin (n + 1)) (CommRingCat.of K)) ≅
      (baseChange (algebraBaseMap K L)).obj G)
    (σ : L ≃ₐ[K] L) :
    matrixDiscrepancyIso E σ =
      (SpecialLinear.baseChangeModelIso (Fin (n + 1)) (algebraBaseMap K L)).symm ≪≫
        GaloisDiscrepancy.groupIso E σ ≪≫
          SpecialLinear.baseChangeModelIso (Fin (n + 1)) (algebraBaseMap K L) := rfl

/-- The model comparison intertwines the two actual discrepancy automorphisms. -/
theorem matrixDiscrepancyIso_square
    (E : (baseChange (algebraBaseMap K L)).obj
        (SpecialLinear.groupScheme (Fin (n + 1)) (CommRingCat.of K)) ≅
      (baseChange (algebraBaseMap K L)).obj G)
    (σ : L ≃ₐ[K] L) :
    (SpecialLinear.baseChangeModelIso (Fin (n + 1)) (algebraBaseMap K L)).hom ≫
        (matrixDiscrepancyIso E σ).hom =
      (GaloisDiscrepancy.groupIso E σ).hom ≫
        (SpecialLinear.baseChangeModelIso (Fin (n + 1)) (algebraBaseMap K L)).hom :=
  conjugateIso_hom _ _

/-- The structure-ring map of the induced test over the extension is its coefficient map. -/
theorem scalarMap_coverTest {Z : Over (Spec (CommRingCat.of K))}
    (a : Z ⟶ cover K L) :
    scalarMap (LocalGroupIso.coverTest a) = coefficients a := rfl

/-- The published all-test discrepancy is the local value of the actual discrepancy
automorphism after base change. -/
theorem discrepancy_eq_groupIso
    (E : (baseChange (algebraBaseMap K L)).obj
        (SpecialLinear.groupScheme (Fin (n + 1)) (CommRingCat.of K)) ≅
      (baseChange (algebraBaseMap K L)).obj G)
    (σ : L ≃ₐ[K] L) {Z : Over (Spec (CommRingCat.of K))}
    (a : Z ⟶ cover K L)
    (g : Matrix.SpecialLinearGroup (Fin (n + 1)) Γ(Z.left, ⊤)) :
    discrepancy (LocalGroupIso.ofBaseChangeIso E) σ a g =
      SpecialLinear.pointsEquiv (Fin (n + 1)) (CommRingCat.of K) Z
        ((LocalGroupIso.ofBaseChangeIso (GaloisDiscrepancy.groupIso E σ)).toFun a
          ((SpecialLinear.pointsEquiv (Fin (n + 1)) (CommRingCat.of K) Z).symm g)) := by
  unfold discrepancy
  rw [LocalGroupIso.ofBaseChangeIso_comp_cover]
  unfold GaloisDiscrepancy.groupIso
  rw [localIso_trans_apply]
  rfl

private theorem modelConjugate_points
    (D : (baseChange (algebraBaseMap K L)).obj
        (SpecialLinear.groupScheme (Fin (n + 1)) (CommRingCat.of K)) ≅
      (baseChange (algebraBaseMap K L)).obj
        (SpecialLinear.groupScheme (Fin (n + 1)) (CommRingCat.of K)))
    {Z : Over (Spec (CommRingCat.of K))} (a : Z ⟶ cover K L)
    (g : Matrix.SpecialLinearGroup (Fin (n + 1)) Γ(Z.left, ⊤)) :
    SpecialLinear.pointsEquiv (Fin (n + 1)) (CommRingCat.of K) Z
      ((LocalGroupIso.ofBaseChangeIso D).toFun a
        ((SpecialLinear.pointsEquiv (Fin (n + 1)) (CommRingCat.of K) Z).symm g)) =
      SpecialLinear.pointsEquiv (Fin (n + 1)) (CommRingCat.of L)
        (LocalGroupIso.coverTest a)
        (((SpecialLinear.pointsEquiv (Fin (n + 1)) (CommRingCat.of L)
          (LocalGroupIso.coverTest a)).symm g) ≫
            ((SpecialLinear.baseChangeModelIso (Fin (n + 1))
              (algebraBaseMap K L)).symm ≪≫ D ≪≫
                SpecialLinear.baseChangeModelIso (Fin (n + 1))
                  (algebraBaseMap K L)).hom.hom.hom) := by
  let x := (LocalGroupIso.coverPointsEquiv
    (SpecialLinear.groupScheme (Fin (n + 1)) (CommRingCat.of K)) a).symm
      ((SpecialLinear.pointsEquiv (Fin (n + 1)) (CommRingCat.of K) Z).symm g)
  have hx : x ≫
      (SpecialLinear.baseChangeModelIso (Fin (n + 1)) (algebraBaseMap K L)).hom.hom.hom =
    (SpecialLinear.pointsEquiv (Fin (n + 1)) (CommRingCat.of L)
      (LocalGroupIso.coverTest a)).symm g := by
    apply (SpecialLinear.pointsEquiv (Fin (n + 1)) (CommRingCat.of L)
      (LocalGroupIso.coverTest a)).injective
    rw [← SpecialLinear.pointsEquiv_coverPointsEquiv]
    simp only [x, MulEquiv.apply_symm_apply]
  change SpecialLinear.pointsEquiv (Fin (n + 1)) (CommRingCat.of K) Z
    (LocalGroupIso.coverPointsEquiv
      (SpecialLinear.groupScheme (Fin (n + 1)) (CommRingCat.of K)) a
        (x ≫ D.hom.hom.hom)) = _
  rw [SpecialLinear.pointsEquiv_coverPointsEquiv, ← hx]
  exact congrArg (SpecialLinear.pointsEquiv (Fin (n + 1)) (CommRingCat.of L)
    (LocalGroupIso.coverTest a))
      (conjugateIso_point
        (SpecialLinear.baseChangeModelIso (Fin (n + 1)) (algebraBaseMap K L))
        D x)

/-- The actual special-linear model discrepancy evaluates to the original discrepancy
on every relative test equipped with a point of the extension cover. -/
theorem discrepancy_eq_matrixDiscrepancyIso
    (E : (baseChange (algebraBaseMap K L)).obj
        (SpecialLinear.groupScheme (Fin (n + 1)) (CommRingCat.of K)) ≅
      (baseChange (algebraBaseMap K L)).obj G)
    (σ : L ≃ₐ[K] L) {Z : Over (Spec (CommRingCat.of K))}
    (a : Z ⟶ cover K L)
    (g : Matrix.SpecialLinearGroup (Fin (n + 1)) Γ(Z.left, ⊤)) :
    discrepancy (LocalGroupIso.ofBaseChangeIso E) σ a g =
      SpecialLinear.pointsEquiv (Fin (n + 1)) (CommRingCat.of L)
        (LocalGroupIso.coverTest a)
        (((SpecialLinear.pointsEquiv (Fin (n + 1)) (CommRingCat.of L)
          (LocalGroupIso.coverTest a)).symm g) ≫
            (matrixDiscrepancyIso E σ).hom.hom.hom) := by
  rw [matrixDiscrepancyIso_def]
  exact (discrepancy_eq_groupIso E σ a g).trans
    (modelConjugate_points (GaloisDiscrepancy.groupIso E σ) a g)

end Langlands.GroupScheme.SpecialLinearTitsCocycle
