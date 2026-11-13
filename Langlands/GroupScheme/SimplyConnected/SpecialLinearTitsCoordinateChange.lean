import Langlands.GroupScheme.SimplyConnected.OuterTypeAStarCover
import Langlands.LinearAlgebra.SpecialLinearConjugationEquiv

/-! # Coordinate change of the all-test special-linear Galois presentation -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.SpecialLinearTitsCocycle

open Matrix
open Langlands.LinearAlgebra.SpecialLinearConjugation
open Langlands.LinearAlgebra.SpecialLinearInverseTranspose

variable {K L : Type u} [Field K] [Field L] [Algebra K L]
  {G : GroupScheme (Spec (CommRingCat.of K))} {n : ℕ}
  (E : LocalGroupIso (SpecialLinear.groupScheme (Fin (n + 1)) (CommRingCat.of K)) G
    (cover K L))

/-- Change local coordinates by conjugation with the coefficient image of `P`. -/
def coordinateChange (P : GeneralLinearGroup (Fin (n + 1)) L) :
    LocalGroupIso (SpecialLinear.groupScheme (Fin (n + 1)) (CommRingCat.of K)) G
      (cover K L) where
  toFun {Z} a :=
    (SpecialLinear.pointsEquiv (Fin (n + 1)) (CommRingCat.of K) Z).trans
      ((conjugationEquiv (GeneralLinearGroup.map (coefficients a) P)).trans
        ((SpecialLinear.pointsEquiv (Fin (n + 1)) (CommRingCat.of K) Z).symm.trans
          (E.toFun a)))
  naturality {Z W} t a g := by
    change E.toFun (t ≫ a)
        ((SpecialLinear.pointsEquiv (Fin (n + 1)) (CommRingCat.of K) W).symm
          (conjugate (GeneralLinearGroup.map (coefficients (t ≫ a)) P)
            (SpecialLinear.pointsEquiv (Fin (n + 1)) (CommRingCat.of K) W (t ≫ g)))) =
      t ≫ E.toFun a
        ((SpecialLinear.pointsEquiv (Fin (n + 1)) (CommRingCat.of K) Z).symm
          (conjugate (GeneralLinearGroup.map (coefficients a) P)
            (SpecialLinear.pointsEquiv (Fin (n + 1)) (CommRingCat.of K) Z g)))
    rw [← E.naturality t a]
    congr 1
    apply (SpecialLinear.pointsEquiv (Fin (n + 1)) (CommRingCat.of K) W).injective
    rw [MulEquiv.apply_symm_apply, SpecialLinear.pointsEquiv_naturality,
      SpecialLinear.pointsEquiv_naturality, MulEquiv.apply_symm_apply, map_conjugate,
      coefficients_naturality]
    rfl

/-- The matrix coordinates in the changed presentation are conjugated by `P⁻¹`. -/
theorem coordinateChange_coordinates (P : GeneralLinearGroup (Fin (n + 1)) L)
    {Z : Over (Spec (CommRingCat.of K))} (a : Z ⟶ cover K L) (z : Z ⟶ G.X) :
    SpecialLinear.pointsEquiv (Fin (n + 1)) (CommRingCat.of K) Z
        (((coordinateChange E P).toFun a).symm z) =
      conjugate (GeneralLinearGroup.map (coefficients a) P)⁻¹
        (SpecialLinear.pointsEquiv (Fin (n + 1)) (CommRingCat.of K) Z
          ((E.toFun a).symm z)) := by
  simp only [coordinateChange, MulEquiv.symm_trans_apply, MulEquiv.apply_symm_apply,
    conjugationEquiv_symm, conjugationEquiv_apply, MulEquiv.symm_symm]

/-- Coordinate change conjugates the discrepancy at both cover points. -/
theorem discrepancy_coordinateChange (P : GeneralLinearGroup (Fin (n + 1)) L)
    (σ : L ≃ₐ[K] L) {Z : Over (Spec (CommRingCat.of K))}
    (a : Z ⟶ cover K L) (g : SpecialLinearGroup (Fin (n + 1)) Γ(Z.left, ⊤)) :
    discrepancy (coordinateChange E P) σ a g =
      conjugate (GeneralLinearGroup.map (coefficients a) P)⁻¹
        (discrepancy E σ a
          (conjugate (GeneralLinearGroup.map (coefficients (a ≫ coverAut K L σ)) P) g)) := by
  simp only [discrepancy, coordinateChange, MulEquiv.trans_apply,
    MulEquiv.symm_trans_apply, MulEquiv.apply_symm_apply,
    conjugationEquiv_symm, conjugationEquiv_apply, MulEquiv.symm_symm]

/-- The inner representative transforms to `P⁻¹ X σ(P)`. -/
theorem HasInnerDiscrepancy.coordinateChange {σ : L ≃ₐ[K] L}
    {X : GeneralLinearGroup (Fin (n + 1)) L} (hX : HasInnerDiscrepancy E σ X)
    (P : GeneralLinearGroup (Fin (n + 1)) L) :
    HasInnerDiscrepancy (coordinateChange E P) σ
      (P⁻¹ * X * GeneralLinearGroup.map σ.toRingHom P) := by
  intro Z a g
  rw [discrepancy_coordinateChange, toGL_conjugate, hX, toGL_conjugate,
    coefficients_coverAut]
  change
    (GeneralLinearGroup.map (coefficients a) P)⁻¹ *
        (GeneralLinearGroup.map (coefficients a) X *
          (GeneralLinearGroup.map (coefficients a) (GeneralLinearGroup.map σ.toRingHom P) *
            SpecialLinearGroup.toGL g *
            (GeneralLinearGroup.map (coefficients a) (GeneralLinearGroup.map σ.toRingHom P))⁻¹) *
          (GeneralLinearGroup.map (coefficients a) X)⁻¹) *
        ((GeneralLinearGroup.map (coefficients a) P)⁻¹)⁻¹ = _
  simp only [map_mul, map_inv]
  group

/-- The outer representative transforms to `P⁻¹ X θ(σ(P))`. -/
theorem HasOuterDiscrepancy.coordinateChange {σ : L ≃ₐ[K] L}
    {X : GeneralLinearGroup (Fin (n + 1)) L} (hX : HasOuterDiscrepancy E σ X)
    (P : GeneralLinearGroup (Fin (n + 1)) L) :
    HasOuterDiscrepancy (coordinateChange E P) σ
      (P⁻¹ * X * inverseTransposeGL (GeneralLinearGroup.map σ.toRingHom P)) := by
  intro Z a g
  rw [discrepancy_coordinateChange, toGL_conjugate, hX,
    inverseTranspose_conjugate, toGL_conjugate, coefficients_coverAut]
  change
    (GeneralLinearGroup.map (coefficients a) P)⁻¹ *
        (GeneralLinearGroup.map (coefficients a) X *
          (inverseTransposeGL
              (GeneralLinearGroup.map (coefficients a) (GeneralLinearGroup.map σ.toRingHom P)) *
            SpecialLinearGroup.toGL (inverseTranspose g) *
            (inverseTransposeGL
              (GeneralLinearGroup.map (coefficients a) (GeneralLinearGroup.map σ.toRingHom P)))⁻¹) *
          (GeneralLinearGroup.map (coefficients a) X)⁻¹) *
        ((GeneralLinearGroup.map (coefficients a) P)⁻¹)⁻¹ = _
  rw [inverseTransposeGL_map]
  simp only [map_mul, map_inv]
  group

/-- A coboundary representative becomes identity discrepancy after coordinate change. -/
theorem discrepancy_coordinateChange_eq_self {σ : L ≃ₐ[K] L}
    {X : GeneralLinearGroup (Fin (n + 1)) L} (hX : HasInnerDiscrepancy E σ X)
    (P : GeneralLinearGroup (Fin (n + 1)) L)
    (hP : X = P * GeneralLinearGroup.map σ.toRingHom P⁻¹)
    {Z : Over (Spec (CommRingCat.of K))} (a : Z ⟶ cover K L)
    (g : SpecialLinearGroup (Fin (n + 1)) Γ(Z.left, ⊤)) :
    discrepancy (coordinateChange E P) σ a g = g := by
  have h := hX.coordinateChange E P
  have hrep : P⁻¹ * X * GeneralLinearGroup.map σ.toRingHom P = 1 := by
    rw [hP, map_inv]
    group
  rw [hrep] at h
  apply SpecialLinearGroup.toGL_injective
  simpa using h Z a g

/-- Coordinates unchanged by conjugation remain unchanged by the new presentation. -/
theorem coordinateChange_coordinates_eq (P : GeneralLinearGroup (Fin (n + 1)) L)
    {Z : Over (Spec (CommRingCat.of K))} (a : Z ⟶ cover K L)
    (z : Z ⟶ G.X) (g : SpecialLinearGroup (Fin (n + 1)) Γ(Z.left, ⊤))
    (hz : SpecialLinear.pointsEquiv (Fin (n + 1)) (CommRingCat.of K) Z
      ((E.toFun a).symm z) = g)
    (hP : Commute (GeneralLinearGroup.map (coefficients a) P) (SpecialLinearGroup.toGL g)) :
    SpecialLinear.pointsEquiv (Fin (n + 1)) (CommRingCat.of K) Z
      (((coordinateChange E P).toFun a).symm z) = g := by
  rw [coordinateChange_coordinates, hz]
  apply SpecialLinearGroup.toGL_injective
  rw [toGL_conjugate]
  calc
    _ = (GeneralLinearGroup.map (coefficients a) P)⁻¹ *
        (SpecialLinearGroup.toGL g * GeneralLinearGroup.map (coefficients a) P) := by
      rw [inv_inv, mul_assoc]
    _ = (GeneralLinearGroup.map (coefficients a) P)⁻¹ *
        (GeneralLinearGroup.map (coefficients a) P * SpecialLinearGroup.toGL g) := by
      rw [hP.eq]
    _ = _ := by group

end Langlands.GroupScheme.SpecialLinearTitsCocycle
