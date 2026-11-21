import Langlands.GroupScheme.Quaternionic.SkewHermitianComponentIsotropicPlane
import Langlands.GroupScheme.Quaternionic.SkewHermitianTensorGram
import Langlands.Global.AdelicGroupLocalPoints
import Langlands.Global.AdelicFunctoriality.Extension
import Langlands.Global.AdelicFunctoriality.Inclusion
import Langlands.Global.AdelicFunctoriality.Infinite

/-! # Isotropic planes at the completions of the quadratic component field -/

noncomputable section

universe u

open TensorProduct NumberField IsDedekindDomain
open scoped TensorProduct NumberField

namespace Langlands.GroupScheme.Quaternionic.FirstKindInvolution

open FiniteAlgebraUnits.MatrixPoints

/-- At every completion a nonsingular isotropic row has an invertible coordinate. -/
def IsLocallyNonsingularIsotropic {F D : Type u} [Field F] [NumberField F]
    [DivisionRing D] [Algebra F D] {I : Type} [Fintype I] [DecidableEq I]
    (τ : FirstKindInvolution F D) (H : Matrix I I D) : Prop :=
  ∀ v : Global.Place F, let R := Global.placeCompletion F v
    let M := coefficientEquiv F D R ((1 : R) ⊗ₜ[F] H)
    ∃ (x : I → R ⊗[F] D) (i : I), IsUnit (x i) ∧
      ∑ j, ∑ k, x j * M j k * τ.baseChange R (x k) = 0

end Langlands.GroupScheme.Quaternionic.FirstKindInvolution

namespace Langlands.GroupScheme.KneserThree.QuatData

open QuadField Quaternionic Global.AdelicFunctoriality

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1900000

variable {F D : Type u} [Field F] [NumberField F] [DivisionRing D] [Algebra F D]
  {I : Type} [Fintype I] [DecidableEq I]
  (Q : QuatData F D) (τ : FirstKindInvolution F D) (hbar : ∀ z, τ z = Q.bar z)
  {H : Matrix I I D} (hH : τ.IsAntihermitian H)

local notation "E" => field Q.c
local notation "V" => I → D
local notation "B" => AntihermitianForm.ofMatrix hH

omit [NumberField F] in
private theorem bilinear_map_coefficients {K R : Type u} [Field K] [Algebra F K]
    [Field R] [Algebra F R] (f : K →ₐ[F] R) (x y : K ⊗[F] V) :
    TensorProduct.map f.toLinearMap (LinearMap.id : D →ₗ[F] D)
      (LinearMap.BilinMap.baseChange K (B).toBilin x y) =
    LinearMap.BilinMap.baseChange R (B).toBilin
      (TensorProduct.map f.toLinearMap (LinearMap.id : V →ₗ[F] V) x)
      (TensorProduct.map f.toLinearMap (LinearMap.id : V →ₗ[F] V) y) := by
  induction x using TensorProduct.inductionOn with
  | add x x' hx hx' => simp only [map_add, LinearMap.add_apply, hx, hx']
  | tmul a x =>
    induction y using TensorProduct.inductionOn with
    | add y y' hy hy' => simp only [map_add, hy, hy']
    | tmul b y =>
      simp only [LinearMap.BilinMap.baseChange_tmul, TensorProduct.map_tmul, AlgHom.toLinearMap_apply,
        LinearMap.id_apply, map_mul]

/-- At each completion of the quadratic component field there are two independent
  orthogonal isotropic vectors for the extended symmetric component. -/
theorem symmetricComponent_local_isotropic_pair (hu : IsUnit H) (hl : τ.IsLocallyNonsingularIsotropic H) :
    letI : NumberField E := NumberField.of_module_finite F E
    letI : Module E V := Module.compHom V Q.ι.toRingHom
    ∀ w : Global.Place E, let R := Global.placeCompletion E w
      let C := LinearMap.BilinForm.baseChange R (Q.symmetricComponent B hbar)
      ∃ x y : R ⊗[E] V, LinearIndependent R ![x, y] ∧ C x x = 0 ∧ C x y = 0 ∧ C y y = 0 := by
  let : NumberField E := NumberField.of_module_finite F E
  let : Module E V := Module.compHom V Q.ι.toRingHom
  have hPair (v : Global.Place F) : let K := Global.placeCompletion F v
      ∃ t s : K ⊗[F] V, LinearMap.BilinMap.baseChange K (B).toBilin t t = 0 ∧
        LinearMap.BilinMap.baseChange K (B).toBilin t s = (1 : K) ⊗ₜ[F] (1 : D) := by
    rcases v with v | v
    · obtain ⟨x, i, hi, hx⟩ := hl (.inl v)
      exact τ.tensorGram_exists_isotropic_with_partner hH v.Completion hu hi hx
    · obtain ⟨x, i, hi, hx⟩ := hl (.inr v)
      exact τ.tensorGram_exists_isotropic_with_partner hH (Global.FiniteCompletion F v) hu hi hx
  have liftPair {K R : Type u} [Field K] [Algebra F K] [Field R] [Algebra F R]
      [Algebra E R] [IsScalarTower F E R] (f : K →ₐ[F] R) (t s : K ⊗[F] V)
      (ht : LinearMap.BilinMap.baseChange K (B).toBilin t t = 0)
      (hs : LinearMap.BilinMap.baseChange K (B).toBilin t s = (1 : K) ⊗ₜ[F] (1 : D)) :
      let C := LinearMap.BilinForm.baseChange R (Q.symmetricComponent B hbar)
      ∃ x y : R ⊗[E] V, LinearIndependent R ![x, y] ∧ C x x = 0 ∧ C x y = 0 ∧ C y y = 0 := by
    let j := TensorProduct.map f.toLinearMap (LinearMap.id : V →ₗ[F] V)
    have h0 : LinearMap.BilinMap.baseChange R (B).toBilin (j t) (j t) = 0 := by
      rw [← bilinear_map_coefficients τ hH f t t, ht, map_zero]
    have h1 : LinearMap.BilinMap.baseChange R (B).toBilin (j t) (j s) = (1 : R) ⊗ₜ[F] (1 : D) := by
      rw [← bilinear_map_coefficients τ hH f t s, hs, TensorProduct.map_tmul, AlgHom.toLinearMap_apply,
        map_one, LinearMap.id_apply]
    exact Q.exists_isotropic_pair_in_symmetricComponent B hbar R (j t) (j s) h0 h1
  intro w
  rcases w with w | w
  · let v := w.comap (algebraMap F E)
    let R := w.Completion
    let : Algebra F R := Algebra.compHom R (algebraMap F E)
    let : IsScalarTower F E R := IsScalarTower.of_algebraMap_eq fun _ => rfl
    let f : v.Completion →ₐ[F] R :=
      { toRingHom := infiniteCompletionMap (algebraMap F E) w
        commutes' := infiniteCompletionMap_coe (algebraMap F E) w }
    obtain ⟨t, s, ht, hs⟩ := hPair (.inl v)
    exact liftPair (K := v.Completion) (R := w.Completion) f t s ht hs
  · let v := w.under (𝓞 F)
    let R := Global.FiniteCompletion E w
    let : Algebra F R := Algebra.compHom R (algebraMap F E)
    let : IsScalarTower F E R := IsScalarTower.of_algebraMap_eq fun _ => rfl
    let f : Global.FiniteCompletion F v →ₐ[F] R :=
      { toRingHom := FiniteExtension.completionMap v w
        commutes' := FiniteExtension.completionMap_coe v w }
    obtain ⟨t, s, ht, hs⟩ := hPair (.inr v)
    exact liftPair (K := Global.FiniteCompletion F v) (R := Global.FiniteCompletion E w) f t s ht hs

/-- Local nonsingular skew isotropy implies an isotropic plane over each completion
  of the embedded quadratic field. -/
def NumberFieldSymmetricComponentLocalPlaneStatement : Prop :=
  ∀ (F D : Type u) [Field F] [NumberField F] [DivisionRing D] [Algebra F D]
    (I : Type) [Fintype I] [DecidableEq I] (Q : QuatData F D)
    (τ : FirstKindInvolution F D) (hbar : ∀ z, τ z = Q.bar z)
    (H : Matrix I I D) (hH : τ.IsAntihermitian H), IsUnit H → τ.IsLocallyNonsingularIsotropic H →
    let K := field Q.c
    let U := I → D
    letI : NumberField K := NumberField.of_module_finite F K
    letI : Module K U := Module.compHom U Q.ι.toRingHom
    ∀ w : Global.Place K, let R := Global.placeCompletion K w
      let C := LinearMap.BilinForm.baseChange R (Q.symmetricComponent (AntihermitianForm.ofMatrix hH) hbar)
      ∃ x y : R ⊗[K] U, LinearIndependent R ![x, y] ∧ C x x = 0 ∧ C x y = 0 ∧ C y y = 0

theorem numberFieldSymmetricComponentLocalPlane : NumberFieldSymmetricComponentLocalPlaneStatement.{u} := by
  intro F D _ _ _ _ I _ _ Q τ hbar H hH hu hl
  exact Q.symmetricComponent_local_isotropic_pair τ hbar hH hu hl

end Langlands.GroupScheme.KneserThree.QuatData
