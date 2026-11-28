import Langlands.GroupScheme.Quaternionic.SkewHermitianComponentIsotropicVector
import Langlands.GroupScheme.Quaternionic.SkewHermitianTensorGram
import Langlands.GroupScheme.Rational.NumberFieldQuaternionicProjectiveRepresentation
import Langlands.LinearAlgebra.NumberFieldQuadraticRepresentation
import Langlands.GroupScheme.Rational.NumberFieldQuaternionEllipticNorm

/-! # A value on a prescribed pure quaternion line from real local isotropy -/

noncomputable section

universe u

open TensorProduct LinearMap NumberField IsDedekindDomain
open scoped TensorProduct NumberField

namespace Langlands.GroupScheme.KneserThree.QuatData

open QuadField Quaternionic Global.AdelicFunctoriality FiniteAlgebraUnits.MatrixPoints

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1500000

variable {F D : Type u} [Field F] [DivisionRing D] [Algebra F D]
  {τ : FirstKindInvolution F D} {V : Type u} [AddCommGroup V]
  [Module D V] [Module F V] [IsScalarTower F D V]
  (B : AntihermitianForm τ V)

private theorem bilinear_baseChange_map' {K R : Type u}
    [Field K] [Algebra F K] [Field R] [Algebra F R]
    (f : K →ₐ[F] R) (x y : K ⊗[F] V) :
    TensorProduct.map f.toLinearMap (LinearMap.id : D →ₗ[F] D)
      (LinearMap.BilinMap.baseChange K B.toBilin x y) =
    LinearMap.BilinMap.baseChange R B.toBilin
      (TensorProduct.map f.toLinearMap (LinearMap.id : V →ₗ[F] V) x)
      (TensorProduct.map f.toLinearMap (LinearMap.id : V →ₗ[F] V) y) := by
  induction x using TensorProduct.inductionOn with
  | add x x' hx hx' => simp only [map_add, LinearMap.add_apply, hx, hx']
  | tmul k v =>
    induction y using TensorProduct.inductionOn with
    | add y y' hy hy' => simp only [map_add, hy, hy']
    | tmul k' v' =>
      simp only [LinearMap.BilinMap.baseChange_tmul, TensorProduct.map_tmul,
        AlgHom.toLinearMap_apply, LinearMap.id_apply, map_mul]

section Rows

variable {I : Type} [Fintype I] [DecidableEq I] {H : Matrix I I D} (hH : τ.IsAntihermitian H)

private theorem tensorGram_pairing' (R : Type u) [Field R] [Algebra F R]
    (x y : R ⊗[F] (I → D)) :
    LinearMap.BilinMap.baseChange R (AntihermitianForm.ofMatrix hH).toBilin x y =
      ∑ i, ∑ j, TensorProduct.piRight F R R (fun _ : I => D) x i * ((1 : R) ⊗ₜ[F] H i j) *
        τ.baseChange R (TensorProduct.piRight F R R (fun _ : I => D) y j) := by
  induction x using TensorProduct.inductionOn with
  | add x x' hx hx' =>
    simp only [_root_.map_add, LinearMap.add_apply, Pi.add_apply, add_mul,
      Finset.sum_add_distrib, hx, hx']
  | tmul r x =>
    induction y using TensorProduct.inductionOn with
    | add y y' hy hy' =>
      simp only [_root_.map_add, Pi.add_apply, mul_add, Finset.sum_add_distrib, hy, hy']
    | tmul s y =>
      simp only [LinearMap.BilinMap.baseChange_tmul, AntihermitianForm.ofMatrix_apply,
        FirstKindInvolution.sesqForm, TensorProduct.piRight_apply, TensorProduct.piRightHom_tmul,
        FirstKindInvolution.baseChange_tmul, Algebra.TensorProduct.tmul_mul_tmul, mul_one,
        TensorProduct.tmul_sum]

/-- A nonzero isotropic row in coordinates gives a nonzero isotropic tensor. -/
theorem exists_isotropic_tensor_of_row (R : Type u) [Field R] [Algebra F R]
    {y : I → R ⊗[F] D} (hy0 : y ≠ 0)
    (hy : ∑ j, ∑ k, y j * ((1 : R) ⊗ₜ[F] H j k) * τ.baseChange R (y k) = 0) :
    ∃ t : R ⊗[F] (I → D), t ≠ 0 ∧
      LinearMap.BilinMap.baseChange R (AntihermitianForm.ofMatrix hH).toBilin t t = 0 := by
  let e := TensorProduct.piRight F R R (fun _ : I => D)
  refine ⟨e.symm y, ?_, ?_⟩
  · intro h
    apply hy0
    rw [← e.apply_symm_apply y, h, map_zero]
  · rw [tensorGram_pairing' hH R, e.apply_symm_apply]
    exact hy

end Rows

section Global

variable [NumberField F] (Q : QuatData F D) (hbar : ∀ z, τ z = Q.bar z)
  {I : Type} [Fintype I] [DecidableEq I] {H : Matrix I I D} (hH : τ.IsAntihermitian H)

local notation "E" => field Q.c

include hbar hH in
/-- Let `H` be an invertible Gram matrix of rank at least three for a skew-hermitian form
over a quaternion division algebra over a number field, with involution `Q.bar`. If `H`
has a nonzero isotropic row over every real completion where `Q.c` is a square, then a
nonzero vector has value on the ground-field line of `Q.x`. -/
theorem exists_vector_on_pureLine_of_real (hu : IsUnit H) (hI : 3 ≤ Fintype.card I)
    (hloc : ∀ v : InfinitePlace F, v.IsReal → IsSquare (algebraMap F v.Completion Q.c) →
      ∃ y : I → v.Completion ⊗[F] D, y ≠ 0 ∧
        ∑ j, ∑ k, y j * ((1 : v.Completion) ⊗ₜ[F] H j k) * τ.baseChange v.Completion (y k) = 0) :
    ∃ x : I → D, x ≠ 0 ∧ ∃ b : F, τ.sesqForm H x x = b • Q.x := by
  have : FiniteDimensional F D := Module.Finite.of_basis Q.basis
  let V := I → D
  let B := AntihermitianForm.ofMatrix hH
  have hB : B.toBilin.SeparatingLeft := AntihermitianForm.ofMatrix_separatingLeft hH hu
  let : NumberField E := NumberField.of_module_finite F E
  let : Module E V := Module.compHom V Q.ι.toRingHom
  let : IsScalarTower F E V := ⟨fun a b x => by
    change (Q.ι (a • b)) • x = a • (Q.ι b • x)
    rw [map_smul, smul_assoc]⟩
  let : FiniteDimensional E V := Module.Finite.of_restrictScalars_finite F E V
  let : Invertible (2 : E) := invertibleOfNonzero (two_ne_zero : (2 : E) ≠ 0)
  let C := Q.symmetricComponent B hbar
  let q : QuadraticForm E V := C.toQuadraticMap
  have hC := Q.symmetricComponent_nondegenerate B hbar hB
  have hpolar (x y : V) : q.polarBilin x y = (2 : E) * C x y := by
    change C.toQuadraticMap.polarBilin x y = _
    rw [LinearMap.BilinMap.polarBilin_toQuadraticMap, LinearMap.add_apply, LinearMap.add_apply,
      LinearMap.flip_apply, show C y x = C x y from Q.symmetricComponent_swap B hbar x y, two_mul]
  have hq : q.polarBilin.Nondegenerate := by
    refine ⟨fun x hx => hC.1 x fun y => ?_, fun y hy => hC.2 y fun x => ?_⟩
    · exact (mul_eq_zero.mp ((hpolar x y).symm.trans (hx y))).resolve_left two_ne_zero
    · exact (mul_eq_zero.mp ((hpolar x y).symm.trans (hy x))).resolve_left two_ne_zero
  have hD : Module.finrank F D = 4 := by
    rw [Module.finrank_eq_card_basis Q.basis, Fintype.card_fin]
  have hFV : Module.finrank F V = Fintype.card I * 4 := by
    rw [Module.finrank_pi_fintype, Finset.sum_const, Finset.card_univ, hD, smul_eq_mul]
  have hEV : Module.finrank E V = 2 * Fintype.card I := by
    have h := Module.finrank_mul_finrank F E V
    rw [Algebra.IsQuadraticExtension.finrank_eq_two, hFV] at h
    omega
  have hbase (R : Type u) [Field R] [Algebra E R] :
      q.baseChange R = (LinearMap.BilinForm.baseChange R C).toQuadraticMap := by
    apply baseChange_ext
    intro x
    rw [QuadraticForm.baseChange_tmul]
    change C x x • ((1 : R) * 1) =
      LinearMap.BilinForm.baseChange R C ((1 : R) ⊗ₜ[E] x) ((1 : R) ⊗ₜ[E] x)
    rw [LinearMap.BilinForm.baseChange_tmul]
  have hroot : (root : E) ≠ 0 := by
    intro h
    have hx : Q.x = 0 := by rw [← Q.ι_root, h, map_zero]
    have hb := Q.basis.ne_zero 1
    rw [show Q.basis 1 = Q.x from congrFun Q.basis_eq 1] at hb
    exact hb hx
  have hplaces (w : Global.Place E) :
      ¬ (q.baseChange (Global.placeCompletion E w)).Anisotropic := by
    rcases w with w | w
    · change ¬ (q.baseChange w.Completion).Anisotropic
      by_cases hw : w.IsReal
      · let v := w.comap (algebraMap F E)
        have hv : v.IsReal := hw.comap _
        let R := w.Completion
        let : Algebra F R := Algebra.compHom R (algebraMap F E)
        let : IsScalarTower F E R := IsScalarTower.of_algebraMap_eq fun _ => rfl
        let f : v.Completion →ₐ[F] R :=
          { toRingHom := infiniteCompletionMap (algebraMap F E) w
            commutes' := infiniteCompletionMap_coe (algebraMap F E) w }
        set θ := algebraMap E R root
        have hθ : algebraMap F R Q.c = θ * θ := by
          rw [IsScalarTower.algebraMap_apply F E R, ← root_mul_self, map_mul]
        have hcsq : IsSquare (algebraMap F v.Completion Q.c) := by
          rcases Langlands.Global.realCompletion_isSquare_or_isSquare_neg hv
            (algebraMap F v.Completion Q.c) with h | h
          · exact h
          · exfalso
            obtain ⟨s, hs⟩ := h
            have hfs : -(θ * θ) = f s * f s := by
              rw [← hθ, ← f.commutes, ← map_neg, hs, map_mul]
            have hsum : θ * θ + f s * f s = 0 := by rw [← hfs, add_neg_cancel]
            have h0 := Langlands.Global.realCompletion_eq_zero_of_mul_self_add_mul_self hw hsum
            exact hroot ((algebraMap E R).injective (h0.trans (map_zero _).symm))
        obtain ⟨y, hy0, hy⟩ := hloc v hv hcsq
        obtain ⟨t, ht0, ht⟩ := exists_isotropic_tensor_of_row hH v.Completion hy0 hy
        let j := TensorProduct.map f.toLinearMap (LinearMap.id : V →ₗ[F] V)
        have hj : Function.Injective j :=
          Module.Flat.rTensor_preserves_injective_linearMap f.toLinearMap f.toRingHom.injective
        have hjt0 : j t ≠ 0 := fun h => ht0 (hj (h.trans (map_zero j).symm))
        have hjt : LinearMap.BilinMap.baseChange R B.toBilin (j t) (j t) = 0 := by
          rw [← bilinear_baseChange_map' B f t t, ht, map_zero]
        obtain ⟨u, hu0, hu⟩ := Q.exists_isotropic_component_of_isotropic B hbar R two_ne_zero
          (j t) hjt0 hjt
        apply (QuadraticMap.not_anisotropic_iff_exists _).mpr
        refine ⟨u, hu0, ?_⟩
        rw [hbase, LinearMap.BilinMap.toQuadraticMap_apply]
        exact hu
      · have hwc : w.IsComplex := InfinitePlace.not_isReal_iff_isComplex.mp hw
        have : NeZero (2 : w.Completion) := ⟨by
          have h := (algebraMap E w.Completion).injective.ne (two_ne_zero : (2 : E) ≠ 0)
          rwa [map_ofNat, map_zero] at h⟩
        apply Langlands.quadraticForm_not_anisotropic_of_forall_isSquare
          (Langlands.Global.complexCompletion_isSquare hwc)
        rw [Module.finrank_baseChange, hEV]
        omega
    · let K := Global.FiniteCompletion E w
      let : ValuativeRel K := Global.FiniteCompletion.valuativeRel w
      let : IsNonarchimedeanLocalField K := Global.FiniteCompletion.isNonarchimedeanLocalField w
      change ¬ (q.baseChange K).Anisotropic
      intro han
      have hb := localQuadraticAnisotropicDimensionBound K (K ⊗[E] V) _ han
      rw [Module.finrank_baseChange, hEV] at hb
      omega
  obtain ⟨x, hx, hzero⟩ := (QuadraticMap.not_anisotropic_iff_exists q).mp
    (Langlands.numberFieldQuadraticIsotropy_of_cyclicNorm ClassFieldTheory.Global.cyclicHasseNorm
      E V q hq hplaces)
  exact ⟨x, hx, (Q.symmetricComponent_self_eq_zero_iff B hbar two_ne_zero x).mp hzero⟩

end Global

end Langlands.GroupScheme.KneserThree.QuatData

namespace Langlands.GroupScheme.Quaternionic.FirstKindInvolution

open KneserThree

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000

section Hyperbolic

variable {F D : Type u} [Field F] [DivisionRing D] [Algebra F D]
  {I : Type} [Fintype I] [DecidableEq I]

/-- In characteristic different from two, a nondegenerate skew-hermitian row pairing over a
division ring with a nonzero isotropic row represents every `w` satisfying `τ(w) = -w`. -/
theorem exists_sesqForm_eq_of_isotropic (τ : FirstKindInvolution F D) (h2 : (2 : F) ≠ 0)
    {H : Matrix I I D} (hH : τ.IsAntihermitian H) (hu : IsUnit H) {x : I → D} (hx0 : x ≠ 0)
    (hx : τ.sesqForm H x x = 0) {w : D} (hw : τ w = -w) :
    ∃ y : I → D, τ.sesqForm H y y = w := by
  let B := AntihermitianForm.ofMatrix hH
  have hsep : B.toBilin.SeparatingLeft := AntihermitianForm.ofMatrix_separatingLeft hH hu
  have hxx : B x x = 0 := hx
  obtain ⟨z, hz⟩ : ∃ z, B x z ≠ 0 := by
    by_contra h
    push Not at h
    exact hx0 (hsep x h)
  obtain ⟨z', h1⟩ : ∃ z', B x z' = 1 :=
    ⟨τ ((B x z)⁻¹) • z, by rw [B.smul_right, τ.apply_apply, mul_inv_cancel₀ hz]⟩
  have h1' : B z' x = -1 := by
    rw [B.skew x z', h1, τ.map_one]
  set P := B z' z'
  have hP : τ P = -P := neg_eq_iff_eq_neg.mp (B.skew z' z').symm
  set a := algebraMap F D (2⁻¹)
  set β := (w - P) * a
  have hτβ : τ β = a * (P - w) := by
    simp only [β, a, τ.map_mul, τ.map_sub, hw, hP, τ.map_algebraMap]
    noncomm_ring
  have ha : a + a = 1 := by
    rw [← _root_.map_add, ← two_mul, mul_inv_cancel₀ h2, _root_.map_one]
  have hcomm : a * (P - w) = (P - w) * a := Algebra.commutes _ _
  refine ⟨β • x + z', ?_⟩
  change B (β • x + z') (β • x + z') = w
  rw [B.add_left, B.add_right, B.add_right, B.smul_left, B.smul_left, B.smul_right, B.smul_right,
    hxx, h1, h1', hτβ, hcomm]
  calc β * (0 * ((P - w) * a)) + β * 1 + (-1 * ((P - w) * a) + P)
      = (w - P) * (a + a) + P := by simp only [β]; noncomm_ring
    _ = w := by rw [ha, mul_one, sub_add_cancel]

end Hyperbolic

variable {F D : Type u} [Field F] [NumberField F] [DivisionRing D] [Algebra F D]
  [FiniteDimensional F D] [Algebra.IsCentral F D]

/-- A nondegenerate skew-hermitian form of rank at least three for quaternion conjugation
over a number field takes a nonzero scalar multiple of a prescribed nonzero pure quaternion
`w` as a value, provided it has a nonzero isotropic row over every real completion at which
the ground-field scalar `w²` is a square. -/
theorem exists_value_on_pureLine_of_real (σ : FirstKindInvolution F D)
    (hdim : Module.finrank F D = 4) (hsym : Module.finrank F σ.symmetricSubspace = 3)
    {I : Type} [Fintype I] [DecidableEq I] (hI : 3 ≤ Fintype.card I) {H : Matrix I I D}
    (hH : (σ.quaternionConjugation hdim hsym).IsAntihermitian H) (hu : IsUnit H)
    {w : D} (hw0 : w ≠ 0) (hw : σ.quaternionConjugation hdim hsym w = -w) {c : F}
    (hc : w * w = algebraMap F D c)
    (hloc : ∀ v : InfinitePlace F, v.IsReal → IsSquare (algebraMap F v.Completion c) →
      ∃ y : I → v.Completion ⊗[F] D, y ≠ 0 ∧
        ∑ j, ∑ k, y j * ((1 : v.Completion) ⊗ₜ[F] H j k) *
          (σ.quaternionConjugation hdim hsym).baseChange v.Completion (y k) = 0) :
    ∃ (x : I → D) (b : F), b ≠ 0 ∧ (σ.quaternionConjugation hdim hsym).sesqForm H x x = b • w := by
  obtain ⟨Q, hQx, hbar⟩ := Quaternion.exists_quatData_of_pure σ hdim hsym two_ne_zero hw0 hw
  have hQc : Q.c = c := (algebraMap F D).injective (by rw [← Q.x_mul_x, ← hc, hQx])
  obtain ⟨x, hx0, b, hb⟩ :=
    Q.exists_vector_on_pureLine_of_real hbar hH hu hI (by rw [hQc]; exact hloc)
  by_cases hb0 : b = 0
  · rw [hb0, zero_smul] at hb
    obtain ⟨y, hy⟩ := exists_sesqForm_eq_of_isotropic _ two_ne_zero hH hu hx0 hb hw
    exact ⟨y, 1, one_ne_zero, by rw [hy, one_smul]⟩
  · exact ⟨x, b, hb0, by rw [hb, hQx]⟩

end Langlands.GroupScheme.Quaternionic.FirstKindInvolution
