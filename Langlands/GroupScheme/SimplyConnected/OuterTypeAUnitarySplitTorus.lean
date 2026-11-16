import Langlands.GroupScheme.SimplyConnected.OuterTypeAUnitarySplitReduction

/-! # Unitary splitting with the actual split-torus coordinates retained -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.SpecialLinearTitsCocycle

open Matrix
open Langlands.LinearAlgebra.SpecialLinearHermitianNormalization

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

variable {K M : Type u} [Field K] [Field M] [Algebra K M]
  {G : GroupScheme (Spec (CommRingCat.of K))} {n : ℕ}
  (E : LocalGroupIso (SpecialLinear.groupScheme (Fin (n + 1)) (CommRingCat.of K)) G
    (cover K M))

/-- Multiplication by a scalar leaves an inner discrepancy unchanged. -/
theorem HasInnerDiscrepancy.scalar_mul {σ : M ≃ₐ[K] M}
    {X : GeneralLinearGroup (Fin (n + 1)) M}
    (hX : HasInnerDiscrepancy E σ X) (b : Mˣ) :
    HasInnerDiscrepancy E σ (GeneralLinearGroup.scalar (Fin (n + 1)) b * X) := by
  intro Z a g
  rw [map_scalar_mul_conjugate]
  exact hX Z a g

variable (S : CommGroupScheme (Spec (CommRingCat.of K))) (f : S.toGrp ⟶ G)
  (χ : Fin (n + 1) → characterLattice S)
  (hdiag : ∀ (Z : Over (Spec (CommRingCat.of K))) (a : Z ⟶ cover K M)
    (s : Z ⟶ S.X),
    (SpecialLinear.pointsEquiv (Fin (n + 1)) (CommRingCat.of K) Z
      ((E.toFun a).symm (s ≫ f.hom.hom)) :
        Matrix (Fin (n + 1)) (Fin (n + 1)) Γ(Z.left, ⊤)) =
      Matrix.diagonal fun i =>
        ((Gm.pointsEquiv _ Z (s ≫ (CommGroupScheme.groupHom (χ i)).hom.hom) :
          Γ(Z.left, ⊤)ˣ) : Γ(Z.left, ⊤)))
  (H : Subgroup (M ≃ₐ[K] M)) [Finite H]
  {x : (M ≃ₐ[K] M) → GeneralLinearGroup (Fin (n + 1)) M}

include hdiag

/-- A projectively trivial inner family can be trivialized within the
centralizer of the actual split torus. -/
theorem exists_torus_preserving_correction_of_scalar
    (hS : IsSplitTorus S.toGrp)
    (hx : ∀ σ ∈ H, HasInnerDiscrepancy E σ (x σ))
    (P : GeneralLinearGroup (Fin (n + 1)) M)
    (hP : ∀ σ ∈ H, ∃ b : Mˣ,
      P⁻¹ * x σ * GeneralLinearGroup.map σ.toRingHom P =
        GeneralLinearGroup.scalar (Fin (n + 1)) b) :
    ∃ Q : GeneralLinearGroup (Fin (n + 1)) M,
      HasTrivialDiscrepancy (coordinateChange E Q) H ∧
      ∀ (Z : Over (Spec (CommRingCat.of K))) (a : Z ⟶ cover K M)
        (s : Z ⟶ S.X),
        (SpecialLinear.pointsEquiv (Fin (n + 1)) (CommRingCat.of K) Z
          (((coordinateChange E Q).toFun a).symm (s ≫ f.hom.hom)) :
            Matrix (Fin (n + 1)) (Fin (n + 1)) Γ(Z.left, ⊤)) =
          Matrix.diagonal fun i =>
            ((Gm.pointsEquiv _ Z (s ≫ (CommGroupScheme.groupHom (χ i)).hom.hom) :
              Γ(Z.left, ⊤)ˣ) : Γ(Z.left, ⊤)) := by
  classical
  let c : H → GeneralLinearGroup (Fin (n + 1)) M :=
    fun σ => P * GeneralLinearGroup.map σ.val.toRingHom P⁻¹
  have hc1 : c 1 = 1 := by
    have hid : GeneralLinearGroup.map (1 : H).val.toRingHom P⁻¹ = P⁻¹ := by
      ext i j
      rfl
    change P * GeneralLinearGroup.map (1 : H).val.toRingHom P⁻¹ = 1
    rw [hid, mul_inv_cancel]
  have hc : ∀ σ τ, c (σ * τ) =
      c σ * GeneralLinearGroup.map σ.val.toRingHom (c τ) := by
    intro σ τ
    change P * GeneralLinearGroup.map (σ * τ).val.toRingHom P⁻¹ =
      (P * GeneralLinearGroup.map σ.val.toRingHom P⁻¹) *
        GeneralLinearGroup.map σ.val.toRingHom
          (P * GeneralLinearGroup.map τ.val.toRingHom P⁻¹)
    simp only [map_mul, map_inv]
    group
    rfl
  have hcx (σ : H) : HasInnerDiscrepancy E σ.val (c σ) := by
    obtain ⟨b, hb⟩ := hP σ.val σ.property
    have hbcomm := GeneralLinearGroup.scalar_commute b P
    have hxrep : x σ.val = GeneralLinearGroup.scalar (Fin (n + 1)) b * c σ := by
      dsimp [c]
      calc
        x σ.val = P * (P⁻¹ * x σ.val * GeneralLinearGroup.map σ.val.toRingHom P) *
            GeneralLinearGroup.map σ.val.toRingHom P⁻¹ := by
              rw [map_inv]
              group
        _ = P * GeneralLinearGroup.scalar (Fin (n + 1)) b *
            GeneralLinearGroup.map σ.val.toRingHom P⁻¹ := by rw [hb]
        _ = _ := by
          rw [← hbcomm, mul_assoc]
          rfl
    have h := (hx σ.val σ.property).scalar_mul E b⁻¹
    simpa only [hxrep, ← mul_assoc, ← map_mul, inv_mul_cancel, map_one, one_mul] using h
  let Q := innerCorrectionMatrix E S f χ hdiag H c hc1 hc hcx hS
  refine ⟨Q, ?_, ?_⟩
  · intro σ Z a g
    exact discrepancy_innerCorrection_eq_self E S f χ hdiag H c hc1 hc hcx hS σ a g
  · exact innerCorrection_coordinates E S f χ hdiag H c hc1 hc hcx hS

/-- Choose the correction whose existence is proved above. -/
noncomputable def torusPreservingCorrectionOfScalar
    (hS : IsSplitTorus S.toGrp)
    (hx : ∀ σ ∈ H, HasInnerDiscrepancy E σ (x σ))
    (P : GeneralLinearGroup (Fin (n + 1)) M)
    (hP : ∀ σ ∈ H, ∃ b : Mˣ,
      P⁻¹ * x σ * GeneralLinearGroup.map σ.toRingHom P =
        GeneralLinearGroup.scalar (Fin (n + 1)) b) :
    GeneralLinearGroup (Fin (n + 1)) M :=
  Classical.choose
    (exists_torus_preserving_correction_of_scalar E S f χ hdiag H hS hx P hP)

end Langlands.GroupScheme.SpecialLinearTitsCocycle
