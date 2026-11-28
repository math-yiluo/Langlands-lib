import Langlands.GroupScheme.Chevalley.MiddleExteriorPairing
import Langlands.Algebra.UnitaryDiscriminant.Cocycle

/-! # The factor set of the middle exterior lifts -/

noncomputable section

open Matrix
open scoped Classical

namespace Langlands.GroupScheme.Chevalley

open UnitaryDiscriminant (invTranspose coe_invTranspose coe_invTranspose_inv)

private abbrev MiddleIndices (m : ℕ) := Set.powersetCard (Fin (2 * m)) m

private theorem scalar_val {I : Type*} [Fintype I] [DecidableEq I]
    {A : Type*} [CommRing A] (a : Aˣ) :
    (GeneralLinearGroup.scalar I a : Matrix I I A) = (a : A) • 1 := by
  rw [GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]

/-- Taking exterior powers commutes with inverse transpose. -/
theorem exteriorGL_invTranspose (N d : ℕ) {A : Type*} [CommRing A] (g : GL (Fin N) A) :
    exteriorGL N d A (invTranspose g) = invTranspose (exteriorGL N d A g) := by
  apply Units.ext
  rw [coe_invTranspose, ← map_inv]
  ext s t
  change exteriorGL N d A (invTranspose g) s t = exteriorGL N d A g⁻¹ t s
  rw [exteriorGL_apply, exteriorGL_apply, ← Matrix.det_transpose
    (Matrix.of fun i j : Fin d => g⁻¹ (Set.powersetCard.ofFinEmbEquiv.symm t j)
      (Set.powersetCard.ofFinEmbEquiv.symm s i))]
  rfl

/-- On the `d`th exterior power, a scalar acts by its `d`th power. -/
theorem exteriorGL_scalar (N d : ℕ) {A : Type*} [CommRing A] (a : Aˣ) :
    exteriorGL N d A (GeneralLinearGroup.scalar (Fin N) a) =
      GeneralLinearGroup.scalar (Set.powersetCard (Fin N) d) (a ^ d) := by
  apply Units.ext
  rw [exteriorGL_val, scalar_val, scalar_val, map_smul, Matrix.toLin'_one, Units.val_pow_eq_pow_val]
  rw [← LinearMap.toMatrix_id (matrixExteriorBasis N d A), ← map_smul]
  apply congrArg (LinearMap.toMatrix (matrixExteriorBasis N d A) (matrixExteriorBasis N d A))
  apply exteriorPower.linearMap_ext
  ext v
  simp only [LinearMap.compAlternatingMap_apply, exteriorPower.map_apply_ιMulti, LinearMap.smul_apply,
    LinearMap.id_apply, Function.comp_def]
  rw [(exteriorPower.ιMulti A d).map_smul_univ (fun _ => (a : A)) v]
  simp

/-- The wedge Gram unit intertwines the middle exterior action with inverse transpose,
up to the determinant character. -/
theorem middleExteriorGramUnit_mul_exteriorGL (m : ℕ) {A : Type*} [CommRing A]
    (g : GL (Fin (2 * m)) A) :
    middleExteriorGramUnit m A * exteriorGL (2 * m) m A g =
      GeneralLinearGroup.scalar (MiddleIndices m) (GeneralLinearGroup.det g) *
        exteriorGL (2 * m) m A (invTranspose g) * middleExteriorGramUnit m A := by
  rw [exteriorGL_invTranspose]
  let J := middleExteriorGram m A
  let X := exteriorGL (2 * m) m A g
  let U : Matrix (MiddleIndices m) (MiddleIndices m) A := X
  let V : Matrix (MiddleIndices m) (MiddleIndices m) A := invTranspose X
  have h : V * Uᵀ = 1 := Units.mul_inv (invTranspose X)
  have hsim : Uᵀ * J * U = (g : Matrix (Fin (2 * m)) (Fin (2 * m)) A).det • J :=
    middleExteriorGram_similitude m A g
  apply Units.ext
  change J * U =
    (GeneralLinearGroup.scalar (MiddleIndices m) (GeneralLinearGroup.det g) : Matrix _ _ A) * V * J
  rw [scalar_val, smul_mul_assoc, Matrix.one_mul, smul_mul_assoc]
  calc
    J * U = V * (Uᵀ * J * U) := by
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc V Uᵀ, h, Matrix.one_mul]
    _ = _ := by rw [hsim, Matrix.mul_smul]; rfl

/-- The square of the wedge Gram unit is the scalar with the interchange sign. -/
theorem middleExteriorGramUnit_square (m : ℕ) (A : Type*) [CommRing A] :
    middleExteriorGramUnit m A * middleExteriorGramUnit m A =
      GeneralLinearGroup.scalar (MiddleIndices m) ((-1 : Aˣ) ^ m) := by
  apply Units.ext
  change middleExteriorGram m A * middleExteriorGram m A =
    (GeneralLinearGroup.scalar (MiddleIndices m) ((-1 : Aˣ) ^ m) : Matrix _ _ A)
  rw [middleExteriorGram_mul_self, scalar_val]
  simp

/-- The wedge Gram unit commutes with change of coefficients. -/
theorem middleExteriorGramUnit_map (m : ℕ) {A A' : Type*} [CommRing A] [CommRing A']
    (f : A →+* A') :
    GeneralLinearGroup.map f (middleExteriorGramUnit m A) = middleExteriorGramUnit m A' :=
  Units.ext (middleExteriorGram_map m A f)

section FactorSet

universe u

open UnitaryDiscriminant (twistGL twistGL_of_mem twistGL_of_not_mem detCocycle
  detCocycle_of_mem detCocycle_of_not_mem_of_mem detCocycle_of_not_mem_of_not_mem)

variable {F M : Type u} [Field F] [Field M] [Algebra F M] (m : ℕ)
  (H : Subgroup (M ≃ₐ[F] M)) (P : (M ≃ₐ[F] M) → GL (Fin (2 * m)) M)

/-- The middle exterior lifts, using the wedge pairing for automorphisms outside `H`. -/
def middleExteriorLift (g : M ≃ₐ[F] M) : GL (MiddleIndices m) M :=
  if g ∈ H then exteriorGL (2 * m) m M (P g)
  else exteriorGL (2 * m) m M (P g) * middleExteriorGramUnit m M

/-- The determinant factor set gives the ordinary semilinear multiplication law of the
middle exterior lifts associated to a twisted projective cocycle. -/
theorem middleExteriorLift_mul {g h : M ≃ₐ[F] M}
    (hmul : g * h ∈ H ↔ (g ∈ H ↔ h ∈ H)) (c : (M ≃ₐ[F] M) → (M ≃ₐ[F] M) → Mˣ)
    (hc : P g * twistGL H g (P h) = GeneralLinearGroup.scalar (Fin (2 * m)) (c g h) * P (g * h)) :
    middleExteriorLift m H P g *
        GeneralLinearGroup.map (g : M →+* M) (middleExteriorLift m H P h) =
      GeneralLinearGroup.scalar (MiddleIndices m) (detCocycle H P c m g h) *
        middleExteriorLift m H P (g * h) := by
  have hΛ := congrArg (exteriorGL (2 * m) m M) hc
  simp only [map_mul, exteriorGL_scalar] at hΛ
  by_cases hg : g ∈ H
  · rw [twistGL_of_mem hg, exteriorGL_naturality] at hΛ
    rw [detCocycle_of_mem _ _ _ hg]
    by_cases hh : h ∈ H
    · have hgh := hmul.mpr (iff_of_true hg hh)
      simpa only [middleExteriorLift, ite_eq_left hg, ite_eq_left hh, ite_eq_left hgh] using hΛ
    · have hgh : g * h ∉ H := fun h' => hh ((hmul.mp h').mp hg)
      simpa only [middleExteriorLift, ite_eq_left hg, ite_eq_right hh, ite_eq_right hgh, map_mul,
        middleExteriorGramUnit_map, mul_assoc] using
        congrArg (· * middleExteriorGramUnit m M) hΛ
  · rw [twistGL_of_not_mem hg, exteriorGL_invTranspose, exteriorGL_naturality] at hΛ
    let a : Mˣ := g • GeneralLinearGroup.det (P h)
    let Λ := exteriorGL (2 * m) m M
    let J := middleExteriorGramUnit m M
    let s := GeneralLinearGroup.scalar (MiddleIndices m) (R := M)
    let gmap := GeneralLinearGroup.map (n := MiddleIndices m) (g : M →+* M)
    have hJ : J * gmap (Λ (P h)) = s a * invTranspose (gmap (Λ (P h))) * J := by
      have hi := middleExteriorGramUnit_mul_exteriorGL m
        (GeneralLinearGroup.map (g : M →+* M) (P h))
      rw [exteriorGL_invTranspose, exteriorGL_naturality, GeneralLinearGroup.map_det] at hi
      exact hi
    have houter : Λ (P g) * J * gmap (Λ (P h)) = s (c g h ^ m * a) * Λ (P (g * h)) * J := by
      calc
        _ = Λ (P g) * (s a * invTranspose (gmap (Λ (P h))) * J) := by rw [mul_assoc, hJ]
        _ = s a * ((Λ (P g) * invTranspose (gmap (Λ (P h)))) * J) := by
          have hcomm : Λ (P g) * s a = s a * Λ (P g) :=
            (GeneralLinearGroup.scalar_commute a (Λ (P g))).symm
          simp only [← mul_assoc, hcomm]
        _ = _ := by rw [show Λ (P g) * invTranspose (gmap (Λ (P h))) = _ from hΛ,
          ← mul_assoc (s a), ← mul_assoc (s a), ← map_mul, mul_comm a]
    by_cases hh : h ∈ H
    · have hgh : g * h ∉ H := fun h' => hg ((hmul.mp h').mpr hh)
      rw [detCocycle_of_not_mem_of_mem _ _ _ hg hh]
      simpa only [middleExteriorLift, ite_eq_right hg, ite_eq_left hh, ite_eq_right hgh, mul_assoc] using houter
    · have hgh := hmul.mpr (iff_of_false hg hh)
      rw [detCocycle_of_not_mem_of_not_mem _ _ _ hg hh]
      change middleExteriorLift m H P g * gmap (middleExteriorLift m H P h) =
        s (c g h ^ m * a * (-1) ^ m) * middleExteriorLift m H P (g * h)
      simp only [middleExteriorLift, ite_eq_right hg, ite_eq_right hh, ite_eq_left hgh]
      change (Λ (P g) * J) * gmap (Λ (P h) * J) = s (c g h ^ m * a * (-1) ^ m) * Λ (P (g * h))
      have hgmapJ : gmap J = J := middleExteriorGramUnit_map m (g : M →+* M)
      rw [map_mul gmap, hgmapJ, ← mul_assoc, houter, mul_assoc (s (c g h ^ m * a) * Λ (P (g * h))) J J,
        show J * J = s ((-1) ^ m) from middleExteriorGramUnit_square m M,
        mul_assoc, ← GeneralLinearGroup.scalar_commute ((-1) ^ m) (Λ (P (g * h))),
        ← mul_assoc, ← map_mul]

end FactorSet

end Langlands.GroupScheme.Chevalley
