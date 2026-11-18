import Langlands.GroupScheme.RelativeUnipotent.LinearQuotientComparison
import Langlands.GroupScheme.AutomorphicAction.BaseChange
import Langlands.GroupScheme.Torus.CentralExtensionSplit

/-! # Actual power actions and vector quotients under coefficient change -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Matrix

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme.AutomorphicAction

variable {S S' : Scheme.{u}} {U : GroupScheme S}

/-- Base change of a multiplicative-group action, with its source identified with the new Gm. -/
def coefficientChange (a : AutomorphicAction (Gm S).toGrp U) (b : S' ⟶ S) :
    AutomorphicAction (Gm S').toGrp ((GroupScheme.baseChange b).obj U) :=
  (a.baseChange b).restrict (Gm.baseChangeIso b).inv

/-- The actual pullback point comparison retains the action and the underlying unit. -/
theorem coefficientChange_act (a : AutomorphicAction (Gm S).toGrp U) (b : S' ⟶ S)
    (T : Over S') (s : T ⟶ (Gm S').X)
    (x : T ⟶ ((GroupScheme.baseChange b).obj U).X) :
    baseChangePointsEquiv b U T ((a.coefficientChange b).act s x) =
      a.act (baseChangePointsEquiv b (Gm S).toGrp T
        (s ≫ (Gm.baseChangeIso b).inv.hom.hom)) (baseChangePointsEquiv b U T x) := by
  rw [coefficientChange, restrict_act, baseChangePointsEquiv_act]

end Langlands.GroupScheme.AutomorphicAction

namespace Langlands.GroupScheme.VectorGroup

variable {R A : CommRingCat.{u}} {n m : ℕ}

/-- A power character reads the same power of the actual underlying global unit. -/
theorem charValue_power_eq (N : ℕ) (T : Over (Spec R)) (s : T ⟶ (Gm (Spec R)).X) :
    charValue (Gm.powerHom _ (N : ℤ)) T s =
      ((Gm.pointsEquiv (Spec R) T s : Γ(T.left, ⊤)) ^ N) := by
  change (Gm.pointsEquiv (Spec R) T
    (s ≫ (CommGroupScheme.groupHom (Gm.powerHom _ (N : ℤ))).hom.hom) :
      Γ(T.left, ⊤)) = _
  rw [Gm.powerHom_apply, Gm.comp_zsmul_id, map_zpow]
  simp

/-- Matrix morphisms commute with every common natural scalar power on all tests. -/
theorem matrixHom_isEquivariant_power (M : Matrix (Fin m) (Fin n) R) (N : ℕ) :
    (powerWeightAction n N).IsEquivariant (powerWeightAction m N) (matrixHom M) := by
  intro T s x
  apply (coordinates R m T).injective
  apply Multiplicative.toAdd.injective
  rw [coordinates_matrixHom, coordinates_weightAction_act,
    coordinates_weightAction_act, coordinates_matrixHom, Matrix.mulVec_smul]

/-- Any positive scalar weight gives every scalar power for the same actual morphism. -/
theorem isEquivariant_power_of_hasScalarWeight (φ : groupScheme R n ⟶ groupScheme R m)
    {d : ℕ} (hd : 0 < d) (hφ : HasScalarWeight (pointTransformation φ) d) (N : ℕ) :
    (powerWeightAction n N).IsEquivariant (powerWeightAction m N) φ := by
  rw [eq_matrixHom_of_hasScalarWeight φ hd hφ]
  exact matrixHom_isEquivariant_power _ N

/-- Canonical vector base change preserves the actual power-character action. -/
theorem baseChangeIso_isEquivariant_power (ρ : R ⟶ A) (N : ℕ) :
    ((powerWeightAction n N).coefficientChange (Spec.map ρ)).IsEquivariant
      (powerWeightAction n N) (baseChangeIso ρ).hom := by
  intro T s x
  apply (coordinates A n T).injective
  apply Multiplicative.toAdd.injective
  rw [coordinates_baseChangeIso_hom, coordinates_weightAction_act,
    coordinates_baseChangeIso_hom]
  change (coordinates R n ((Over.map (Spec.map ρ)).obj T)
      (baseChangePointsEquiv (Spec.map ρ) (groupScheme R n) T
        (((powerWeightAction n N).coefficientChange (Spec.map ρ)).act s x))).toAdd = _
  rw [AutomorphicAction.coefficientChange_act, coordinates_weightAction_act,
    charValue_power_eq, charValue_power_eq]
  congr 1
  exact congrArg (fun t : Γ(T.left, ⊤)ˣ => (t : Γ(T.left, ⊤)) ^ N)
    (Gm.baseChangeUnitsEquiv_baseChangeIso_inv (Spec.map ρ) T s)

end Langlands.GroupScheme.VectorGroup

namespace Langlands.GroupScheme.FppfQuotientComparison

variable {R A : CommRingCat.{u}} {U : GroupScheme (Spec R)} {n : ℕ}

/-- The original actual quotient after coefficient change, in standard vector coordinates. -/
def coefficientQuotient (ρ : R ⟶ A) (q : U ⟶ VectorGroup.groupScheme R n) :
    (GroupScheme.baseChange (Spec.map ρ)).obj U ⟶ VectorGroup.groupScheme A n :=
  (GroupScheme.baseChange (Spec.map ρ)).map q ≫ (VectorGroup.baseChangeIso ρ).hom

/-- Full fppf quotients remain full after the canonical vector coefficient comparison. -/
theorem isFppfQuotient_coefficientQuotient (ρ : R ⟶ A)
    {q : U ⟶ VectorGroup.groupScheme R n} {F : SubgroupFunctor U}
    (hq : RelativeRoot.IsFppfQuotient F q) :
    RelativeRoot.IsFppfQuotient (F.baseChange (Spec.map ρ)) (coefficientQuotient ρ q) :=
  (hq.baseChange (Spec.map ρ)).comp_iso (VectorGroup.baseChangeIso ρ)

/-- Actual scalar equivariance of a vector quotient is preserved under coefficient change. -/
theorem coefficientQuotient_isEquivariant (ρ : R ⟶ A)
    (a : AutomorphicAction (Gm (Spec R)).toGrp U) (N : ℕ)
    (q : U ⟶ VectorGroup.groupScheme R n)
    (hq : a.IsEquivariant (VectorGroup.powerWeightAction n N) q) :
    (a.coefficientChange (Spec.map ρ)).IsEquivariant
      (VectorGroup.powerWeightAction n N) (coefficientQuotient ρ q) := by
  intro T s x
  have he : (a.coefficientChange (Spec.map ρ)).act s x ≫
      ((GroupScheme.baseChange (Spec.map ρ)).map q).hom.hom =
    ((VectorGroup.powerWeightAction n N).coefficientChange (Spec.map ρ)).act s
      (x ≫ ((GroupScheme.baseChange (Spec.map ρ)).map q).hom.hom) := by
    apply (baseChangePointsEquiv (Spec.map ρ) (VectorGroup.groupScheme R n) T).injective
    rw [baseChangePointsEquiv_comp, AutomorphicAction.coefficientChange_act,
      AutomorphicAction.coefficientChange_act, baseChangePointsEquiv_comp]
    exact hq _ _
  change ((a.coefficientChange (Spec.map ρ)).act s x ≫
      ((GroupScheme.baseChange (Spec.map ρ)).map q).hom.hom) ≫
      (VectorGroup.baseChangeIso ρ).hom.hom.hom = _
  rw [he, VectorGroup.baseChangeIso_isEquivariant_power]
  rfl

end Langlands.GroupScheme.FppfQuotientComparison
