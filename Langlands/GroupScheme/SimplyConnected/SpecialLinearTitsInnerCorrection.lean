import Langlands.GroupScheme.SimplyConnected.SpecialLinearTitsWeightLines
import Langlands.GroupScheme.SimplyConnected.SpecialLinearTitsCoordinateChange
import Langlands.LinearAlgebra.GaloisBlockDescent

/-! # Inner correction preserving the diagonal split torus -/

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.SpecialLinearTitsCocycle

open Matrix
open Langlands.LinearAlgebra.SpecialLinearConjugation
open Langlands.LinearAlgebra.GaloisBlockDescent

variable {K L : Type u} [Field K] [Field L] [Algebra K L]
  {G : GroupScheme (Spec (CommRingCat.of K))} {n : ℕ}
  (E : LocalGroupIso (SpecialLinear.groupScheme (Fin (n + 1)) (CommRingCat.of K)) G
    (cover K L))
  (S : CommGroupScheme (Spec (CommRingCat.of K))) (f : S.toGrp ⟶ G)
  (χ : Fin (n + 1) → characterLattice S)
  (hdiag : ∀ (Z : Over (Spec (CommRingCat.of K))) (a : Z ⟶ cover K L)
    (s : Z ⟶ S.X),
    (SpecialLinear.pointsEquiv (Fin (n + 1)) (CommRingCat.of K) Z
      ((E.toFun a).symm (s ≫ f.hom.hom)) : Matrix (Fin (n + 1)) (Fin (n + 1)) Γ(Z.left, ⊤)) =
      Matrix.diagonal fun i =>
        ((Gm.pointsEquiv _ Z (s ≫ (CommGroupScheme.groupHom (χ i)).hom.hom) : Γ(Z.left, ⊤)ˣ) :
          Γ(Z.left, ⊤)))

omit E f χ hdiag in
private theorem split_pairing_injective (hS : IsSplitTorus S.toGrp) :
    Function.Injective (latticePairing S) := by
  obtain ⟨I, hI, ⟨e⟩⟩ := hS
  let e' : S ≅ splitTorus.commGroupScheme (Spec (CommRingCat.of K)) I :=
    CommGroupScheme.isoOfGroupIso e
  have hp : (latticePairing S).IsPerfPair := by
    refine LinearMap.IsPerfPair.congr
      (characterLattice.congr e').toIntLinearEquiv
      (cocharacterLattice.congr e').toIntLinearEquiv (latticePairing S)
      (p := latticePairing (splitTorus.commGroupScheme (Spec (CommRingCat.of K)) I)) ?_
    ext ψ ν
    change latticePairing S ((characterLattice.congr e').symm ψ)
        ((cocharacterLattice.congr e').symm ν) =
      latticePairing (splitTorus.commGroupScheme (Spec (CommRingCat.of K)) I) ψ ν
    simpa only [AddEquiv.apply_symm_apply] using
      (latticePairing_congr e' ((characterLattice.congr e').symm ψ)
        ((cocharacterLattice.congr e').symm ν)).symm
  let := hp
  exact (LinearMap.IsPerfPair.bijective_left (latticePairing S)).injective

include hdiag

/-- Inner representatives have no entries between distinct character spaces. -/
theorem HasInnerDiscrepancy.entry_eq_zero_of_character_ne (hS : IsSplitTorus S.toGrp)
    {σ : L ≃ₐ[K] L} {X : GeneralLinearGroup (Fin (n + 1)) L}
    (hX : HasInnerDiscrepancy E σ X) (i j : Fin (n + 1)) (hij : χ i ≠ χ j) :
    X i j = 0 := by
  have hpair : ∃ ν : cocharacterLattice S,
      latticePairing S (χ i) ν ≠ latticePairing S (χ j) ν := by
    by_contra! h
    apply hij
    apply split_pairing_injective S hS
    exact LinearMap.ext h
  obtain ⟨ν, hν⟩ := hpair
  exact hX.entry_eq_zero_of_weight_ne E S f χ hdiag ν i j hν

/-- A matrix with the character-block zero pattern commutes with every torus coordinate. -/
theorem commutes_of_character_blocks (P : GeneralLinearGroup (Fin (n + 1)) L)
    (hP : ∀ i j, χ i ≠ χ j → P i j = 0)
    (Z : Over (Spec (CommRingCat.of K))) (a : Z ⟶ cover K L) (s : Z ⟶ S.X) :
    Commute (GeneralLinearGroup.map (coefficients a) P)
      (SpecialLinearGroup.toGL
        (SpecialLinear.pointsEquiv (Fin (n + 1)) (CommRingCat.of K) Z
          ((E.toFun a).symm (s ≫ f.hom.hom)))) := by
  apply Units.ext
  change P.val.map (coefficients a) *
      (SpecialLinear.pointsEquiv (Fin (n + 1)) (CommRingCat.of K) Z
        ((E.toFun a).symm (s ≫ f.hom.hom))).val =
    (SpecialLinear.pointsEquiv (Fin (n + 1)) (CommRingCat.of K) Z
        ((E.toFun a).symm (s ≫ f.hom.hom))).val * P.val.map (coefficients a)
  rw [hdiag Z a s]
  ext i j
  simp only [Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.map_apply]
  by_cases hij : χ i = χ j
  · rw [hij, mul_comm]
  · rw [hP i j hij, map_zero, zero_mul, mul_zero]

variable (H : Subgroup (L ≃ₐ[K] L)) [Finite H]
  (c : H → GeneralLinearGroup (Fin (n + 1)) L)
  (hc1 : c 1 = 1)
  (hc : ∀ σ τ, c (σ * τ) = c σ * GeneralLinearGroup.map σ.val.toRingHom (c τ))
  (hx : ∀ σ, HasInnerDiscrepancy E σ.val (c σ))
  (hS : IsSplitTorus S.toGrp)

include hc1 hc hx hS

/-- Blockwise Hilbert 90 trivialises a supplied inner cocycle within the torus centralizer. -/
theorem exists_torus_preserving_inner_coboundary :
    ∃ P : GeneralLinearGroup (Fin (n + 1)) L,
      (∀ σ, c σ = P * GeneralLinearGroup.map σ.val.toRingHom P⁻¹) ∧
      ∀ i j, χ i ≠ χ j → P i j = 0 := by
  have hb (σ : H) (i j : Fin (n + 1)) (hij : χ i ≠ χ j) : c σ i j = 0 :=
    (hx σ).entry_eq_zero_of_character_ne E S f χ hdiag hS i j hij
  obtain ⟨P, hP, hPb⟩ := exists_blockwise_coboundary H χ c hc1 hc hb
  refine ⟨P, fun σ => ?_, hPb⟩
  have hP' : c σ * GeneralLinearGroup.map σ.val.toRingHom P = P := hP σ
  have h := congrArg (fun Q : GeneralLinearGroup (Fin (n + 1)) L =>
    Q * (GeneralLinearGroup.map σ.val.toRingHom P)⁻¹) hP'
  simpa only [mul_inv_cancel_right, map_inv] using h

/-- A chosen matrix trivialising the inner cocycle and preserving its character blocks. -/
def innerCorrectionMatrix : GeneralLinearGroup (Fin (n + 1)) L :=
  Classical.choose
    (exists_torus_preserving_inner_coboundary E S f χ hdiag H c hc1 hc hx hS)

/-- The chosen correction matrix gives the supplied inner cocycle as a coboundary. -/
theorem innerCorrectionMatrix_spec (σ : H) :
    c σ = innerCorrectionMatrix E S f χ hdiag H c hc1 hc hx hS *
      GeneralLinearGroup.map σ.val.toRingHom
        (innerCorrectionMatrix E S f χ hdiag H c hc1 hc hx hS)⁻¹ :=
  (Classical.choose_spec
    (exists_torus_preserving_inner_coboundary E S f χ hdiag H c hc1 hc hx hS)).1 σ

/-- The chosen correction has zero entries between distinct character spaces. -/
theorem innerCorrectionMatrix_apply_of_ne (i j : Fin (n + 1)) (hij : χ i ≠ χ j) :
    innerCorrectionMatrix E S f χ hdiag H c hc1 hc hx hS i j = 0 :=
  (Classical.choose_spec
    (exists_torus_preserving_inner_coboundary E S f χ hdiag H c hc1 hc hx hS)).2 i j hij

/-- The chosen coordinate change kills all inner discrepancies in `H`. -/
theorem discrepancy_innerCorrection_eq_self (σ : H)
    {Z : Over (Spec (CommRingCat.of K))} (a : Z ⟶ cover K L)
    (g : SpecialLinearGroup (Fin (n + 1)) Γ(Z.left, ⊤)) :
    discrepancy (coordinateChange E
      (innerCorrectionMatrix E S f χ hdiag H c hc1 hc hx hS)) σ.val a g = g :=
  discrepancy_coordinateChange_eq_self E (hx σ) _
    (innerCorrectionMatrix_spec E S f χ hdiag H c hc1 hc hx hS σ) a g

/-- The chosen coordinate change preserves the actual torus coordinates on every test. -/
theorem innerCorrection_coordinates (Z : Over (Spec (CommRingCat.of K)))
    (a : Z ⟶ cover K L) (s : Z ⟶ S.X) :
    (SpecialLinear.pointsEquiv (Fin (n + 1)) (CommRingCat.of K) Z
      (((coordinateChange E (innerCorrectionMatrix E S f χ hdiag H c hc1 hc hx hS)).toFun a).symm
        (s ≫ f.hom.hom)) : Matrix (Fin (n + 1)) (Fin (n + 1)) Γ(Z.left, ⊤)) =
      Matrix.diagonal fun i =>
        ((Gm.pointsEquiv _ Z (s ≫ (CommGroupScheme.groupHom (χ i)).hom.hom) : Γ(Z.left, ⊤)ˣ) :
          Γ(Z.left, ⊤)) := by
  rw [coordinateChange_coordinates_eq E _ a (s ≫ f.hom.hom) _ rfl
    (commutes_of_character_blocks E S f χ hdiag _
      (innerCorrectionMatrix_apply_of_ne E S f χ hdiag H c hc1 hc hx hS) Z a s)]
  exact hdiag Z a s

end Langlands.GroupScheme.SpecialLinearTitsCocycle
