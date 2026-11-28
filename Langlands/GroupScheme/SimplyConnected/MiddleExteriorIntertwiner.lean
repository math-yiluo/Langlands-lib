import Langlands.GroupScheme.Chevalley.MiddleExteriorCocycle
import Langlands.GroupScheme.SimplyConnected.OuterTypeAStarCover
import Langlands.GroupScheme.LocalGroupIsoBaseChangeRecovery
import Langlands.GroupScheme.SpecialLinearBaseChange
import Langlands.GroupScheme.MatrixRepresentation.ComponentIntertwiners
import Langlands.GroupScheme.MatrixRepresentation.GaloisTwist

/-! # Galois intertwiners on the middle exterior power of a special linear chart -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Matrix
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.SpecialLinearTitsCocycle

open MatrixRepresentation Chevalley
open Langlands.LinearAlgebra.SpecialLinearInverseTranspose (inverseTranspose)
open Langlands.UnitaryDiscriminant (invTranspose)

variable {K M : Type u} [Field K] [Field M] [Algebra K M]
  {G : GroupScheme (Spec (CommRingCat.of K))}

local notation "b" => algebraBaseMap K M
local notation "Gₘ" => Functor.obj (GroupScheme.baseChange b) G

section ExteriorChart

variable {n : ℕ}
  (E : LocalGroupIso (SpecialLinear.groupScheme (Fin (n + 1)) (CommRingCat.of K)) G
    (cover K M))

/-- The exterior power of the column representation read in the supplied split chart. -/
def exteriorOnChart (d : ℕ) :
    MatrixRepresentation Gₘ (Set.powersetCard (Fin (n + 1)) d) :=
  (exteriorRepresentation (n + 1) d (CommRingCat.of M)
    (SpecialLinear.inclusion (Fin (n + 1)) (CommRingCat.of M))).restrict
    (E.toBaseChangeIso.inv ≫ (SpecialLinear.baseChangeModelIso (Fin (n + 1)) b).hom)

/-- The special-linear matrix of a point on the original group read at a cover point. -/
def chartMatrix {Z : Over (Spec (CommRingCat.of K))} (a : Z ⟶ cover K M) (y : Z ⟶ G.X) :
    SpecialLinearGroup (Fin (n + 1)) Γ(Z.left, ⊤) :=
  SpecialLinear.pointsEquiv (Fin (n + 1)) (CommRingCat.of K) Z ((E.toFun a).symm y)

/-- Evaluating the exterior representation recovers the exterior power of the chart matrix. -/
theorem exteriorOnChart_pointMatrix (d : ℕ) (T : Over (Spec (CommRingCat.of M)))
    (y : T ⟶ (Gₘ).X) :
    (exteriorOnChart E d).pointMatrix T y =
      exteriorGL (n + 1) d Γ(T.left, ⊤)
        (SpecialLinearGroup.toGL (chartMatrix E (LocalGroupIso.baseChangeTestPoint (U := cover K M) T)
          (baseChangePointsEquiv b G T y))) := by
  rw [exteriorOnChart, pointMatrix_restrict, exteriorRepresentation_pointMatrix, pointMatrix_apply,
    SpecialLinear.pointsEquiv_inclusion]
  simp only [Grp.comp_hom_hom, ← Category.assoc]
  apply congrArg (fun g => exteriorGL (n + 1) d Γ(T.left, ⊤) (SpecialLinearGroup.toGL g))
  refine (SpecialLinear.pointsEquiv_baseChangeModelIso_hom (Fin (n + 1)) b T _).trans ?_
  exact congrArg (SpecialLinear.pointsEquiv (Fin (n + 1)) (CommRingCat.of K) _)
    (E.toBaseChangeIso_inv_points T y)

private theorem chartMatrix_transport (σ : M ≃ₐ[K] M) (T : Over (Spec (CommRingCat.of M)))
    (y : T ⟶ (Gₘ).X) :
    chartMatrix E (LocalGroupIso.baseChangeTestPoint (U := cover K M)
        ((Over.map (galoisBaseMap K M σ)).obj T))
        (baseChangePointsEquiv b G _ (descentPoint b (galoisBaseMap K M σ)
          (galoisBaseMap_over K M σ) G T y)) =
      chartMatrix E (LocalGroupIso.baseChangeTestPoint (U := cover K M) T ≫ coverAut K M σ)
        (baseChangePointsEquiv b G T y) := by
  rw [baseChangePointsEquiv_descentPoint]
  let t := (descentTestIso b (galoisBaseMap K M σ) (galoisBaseMap_over K M σ) T).inv
  let a := LocalGroupIso.baseChangeTestPoint (U := cover K M) T ≫ coverAut K M σ
  let z := baseChangePointsEquiv b G T y
  have ha : LocalGroupIso.baseChangeTestPoint (U := cover K M)
      ((Over.map (galoisBaseMap K M σ)).obj T) = t ≫ a := by
    apply Over.OverMorphism.ext
    exact (Category.id_comp _).symm
  rw [ha]
  change SpecialLinear.pointsEquiv _ (CommRingCat.of K) _ (E.symm.toFun (t ≫ a) (t ≫ z)) =
    chartMatrix E a z
  rw [E.symm.naturality, SpecialLinear.pointsEquiv_naturality]
  change SpecialLinearGroup.map (Scheme.Hom.appTop (𝟙 T.left)).hom _ = _
  rw [Scheme.Hom.id_appTop]
  apply Subtype.ext
  ext i j
  rfl

private theorem discrepancy_chartMatrix (σ : M ≃ₐ[K] M)
    {Z : Over (Spec (CommRingCat.of K))} (a : Z ⟶ cover K M) (y : Z ⟶ G.X) :
    discrepancy E σ a (chartMatrix E (a ≫ coverAut K M σ) y) = chartMatrix E a y := by
  simp only [discrepancy, chartMatrix, MulEquiv.symm_apply_apply, MulEquiv.apply_symm_apply]

end ExteriorChart

section Middle

variable {m : ℕ}
  (E : LocalGroupIso (SpecialLinear.groupScheme (Fin (2 * (m + 1))) (CommRingCat.of K)) G
    (cover K M))
  (H : Subgroup (M ≃ₐ[K] M)) (P : (M ≃ₐ[K] M) → GL (Fin (2 * (m + 1))) M)

local notation "N" => 2 * (m + 1)
local notation "d" => m + 1

private theorem toGL_inverseTranspose {A : Type*} [CommRing A]
    (g : SpecialLinearGroup (Fin N) A) :
    SpecialLinearGroup.toGL (inverseTranspose g) = invTranspose (SpecialLinearGroup.toGL g) :=
  Units.ext rfl

private theorem middleExteriorGL_conjugation {A : Type*} [CommRing A]
    (X : GL (Fin N) A) (g : SpecialLinearGroup (Fin N) A) :
    exteriorGL N d A (X * SpecialLinearGroup.toGL (inverseTranspose g) * X⁻¹) =
      (exteriorGL N d A X * middleExteriorGramUnit d A) *
        exteriorGL N d A (SpecialLinearGroup.toGL g) *
        (exteriorGL N d A X * middleExteriorGramUnit d A)⁻¹ := by
  have hJ := middleExteriorGramUnit_mul_exteriorGL d (SpecialLinearGroup.toGL g)
  rw [SpecialLinearGroup.coeToGL_det, map_one, one_mul, ← toGL_inverseTranspose] at hJ
  simp only [map_mul, map_inv]
  rw [mul_assoc (exteriorGL N d A X) (middleExteriorGramUnit d A), hJ]
  group

private theorem exteriorGL_discrepancy (hI : ∀ σ ∈ H, HasInnerDiscrepancy E σ (P σ))
    (hO : ∀ σ ∉ H, HasOuterDiscrepancy E σ (P σ)) (σ : M ≃ₐ[K] M)
    {Z : Over (Spec (CommRingCat.of K))} (a : Z ⟶ cover K M)
    (g : SpecialLinearGroup (Fin N) Γ(Z.left, ⊤)) :
    exteriorGL N d Γ(Z.left, ⊤) (SpecialLinearGroup.toGL (discrepancy E σ a g)) =
      GeneralLinearGroup.map (coefficients a) (middleExteriorLift d H P σ) *
        exteriorGL N d Γ(Z.left, ⊤) (SpecialLinearGroup.toGL g) *
        (GeneralLinearGroup.map (coefficients a) (middleExteriorLift d H P σ))⁻¹ := by
  by_cases hσ : σ ∈ H
  · refine (congrArg (exteriorGL N d Γ(Z.left, ⊤)) (hI σ hσ Z a g)).trans ?_
    rw [middleExteriorLift, ite_eq_left hσ, ← exteriorGL_naturality]
    simp only [map_mul, map_inv]
    rfl
  · refine (congrArg (exteriorGL N d Γ(Z.left, ⊤)) (hO σ hσ Z a g)).trans ?_
    rw [middleExteriorLift, ite_eq_right hσ,
      map_mul (GeneralLinearGroup.map (n := Set.powersetCard (Fin N) d) (coefficients a)),
      ← exteriorGL_naturality, middleExteriorGramUnit_map]
    exact middleExteriorGL_conjugation _ _

/-- The inverses of the middle exterior lifts are actual intertwiners from the chart
representation to its Galois twists. -/
theorem middleExterior_intertwines [IsAffineHom (Gₘ).X.hom]
    (hI : ∀ σ ∈ H, HasInnerDiscrepancy E σ (P σ))
    (hO : ∀ σ ∉ H, HasOuterDiscrepancy E σ (P σ)) (σ : M ≃ₐ[K] M) :
    (exteriorOnChart E d).Intertwines (galoisTwist σ (exteriorOnChart E d))
      ((middleExteriorLift d H P σ)⁻¹ : GL (Set.powersetCard (Fin N) d) M).val := by
  apply (intertwines_iff_universal_pointMatrix _ _ _).mpr
  rw [pointMatrix_transport, exteriorOnChart_pointMatrix, exteriorOnChart_pointMatrix,
    chartMatrix_transport]
  let T := (Gₘ).X
  let Z := (Over.map b).obj T
  let a : Z ⟶ cover K M := LocalGroupIso.baseChangeTestPoint (U := cover K M) T
  let y : Z ⟶ G.X := baseChangePointsEquiv b G T (𝟙 T)
  let Q := GeneralLinearGroup.map (coefficients a) (middleExteriorLift d H P σ)
  let A := exteriorGL N d Γ(Z.left, ⊤) (SpecialLinearGroup.toGL (chartMatrix E a y))
  let B := exteriorGL N d Γ(Z.left, ⊤)
    (SpecialLinearGroup.toGL (chartMatrix E (a ≫ coverAut K M σ) y))
  have hA : A = Q * B * Q⁻¹ := (congrArg (fun g => exteriorGL N d Γ(Z.left, ⊤)
      (SpecialLinearGroup.toGL g)) (discrepancy_chartMatrix E σ a y)).symm.trans
    (exteriorGL_discrepancy E H P hI hO σ a _)
  have h : Q⁻¹ * A = B * Q⁻¹ := by
    rw [hA]
    group
  exact congrArg Units.val h

end Middle

end Langlands.GroupScheme.SpecialLinearTitsCocycle
