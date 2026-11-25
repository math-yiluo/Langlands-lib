import Langlands.GroupScheme.Rational.NumberFieldSkewHermitianComponentPlanes
import Langlands.GroupScheme.Quaternionic.SkewHermitianSemilinearComponent
import Langlands.LinearAlgebra.IsotropicPlaneOrthogonalComplement
import Langlands.LinearAlgebra.NumberFieldQuadraticIsometryProof

/-! # A projective skew value in the complement of a prescribed line -/

noncomputable section

universe u

open scoped TensorProduct

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 3500000

namespace Langlands.SymmetricBilinear.HyperbolicPair

variable {K R V : Type u} [Field K] [Field R] [Algebra K R] [AddCommGroup V] [Module K V]
  {B : LinearMap.BilinForm K V} (P : HyperbolicPair B)

/-- An isotropic plane after scalar extension gives a nonzero isotropic vector
  for the scalar extension of the original hyperbolic complement. -/
theorem exists_baseChange_complement_isotropic (hS : B.IsSymm) {x y : R ⊗[K] V}
    (hli : LinearIndependent R ![x, y])
    (hxx : B.baseChange R x x = 0) (hxy : B.baseChange R x y = 0) (hyy : B.baseChange R y y = 0) :
    ∃ z : R ⊗[K] P.orthogonalComplement, z ≠ 0 ∧
      ((B.restrict P.orthogonalComplement).baseChange R) z z = 0 := by
  let C := B.baseChange R
  let P' : HyperbolicPair C :=
    ⟨(1 : R) ⊗ₜ[K] P.x, (1 : R) ⊗ₜ[K] P.y,
      by simp [C, P.xx], by simp [C, P.xy], by simp [C, P.yy]⟩
  have hS₀ : LinearMap.IsSymm B := ⟨hS.eq⟩
  have hS' : C.IsSymm := ⟨(LinearMap.BilinForm.IsSymm.baseChange R hS₀).eq⟩
  obtain ⟨z, hz, hzz⟩ := P'.exists_isotropic_in_complement_of_plane hS' hli hxx hxy hyy
  let W := P.orthogonalComplement
  let j := W.subtype.baseChange R
  let r := (LinearMap.snd K (K × K) W).comp (P.split hS).symm.toLinearMap
  let rR := r.baseChange R
  have hproj (w : R ⊗[K] V) :
      j (rR w) = w - C P'.y w • P'.x - C P'.x w • P'.y := by
    induction w using TensorProduct.inductionOn with
    | add w w' hw hw' =>
      simp only [map_add, hw, hw', add_smul]
      abel
    | tmul a w =>
      have ht (c : K) (v : V) : a ⊗ₜ[K] (c • v) = (c • a) • ((1 : R) ⊗ₜ[K] v) := by
        rw [← TensorProduct.smul_tmul, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      change (W.subtype.baseChange R) ((r.baseChange R) (a ⊗ₜ[K] w)) = _
      rw [LinearMap.baseChange_tmul, LinearMap.baseChange_tmul, show (W.subtype (r w) : V) =
        w - B P.y w • P.x - B P.x w • P.y from P.split_symm_snd hS w,
        TensorProduct.tmul_sub, TensorProduct.tmul_sub, ht, ht]
      simp only [C, P', LinearMap.BilinForm.baseChange_tmul, one_mul]
  have hzero := (P'.mem_orthogonalComplement (z : R ⊗[K] V)).mp z.property
  have hj : j (rR z) = (z : R ⊗[K] V) := by rw [hproj, hzero.1, hzero.2, zero_smul, zero_smul, sub_zero, sub_zero]
  have hpair (a b : R ⊗[K] W) : ((B.restrict W).baseChange R) a b = C (j a) (j b) := by
    induction a using TensorProduct.inductionOn with
    | add a a' ha ha' => simp only [map_add, LinearMap.add_apply, ha, ha']
    | tmul s a =>
      induction b using TensorProduct.inductionOn with
      | add b b' hb hb' => simp only [map_add, hb, hb']
      | tmul t b => simp only [j, C, LinearMap.baseChange_tmul, LinearMap.BilinForm.baseChange_tmul]; rfl
  refine ⟨rR z, fun h => hz (Subtype.ext (hj.symm.trans ?_)), ?_⟩
  · rw [h, map_zero]
    rfl
  · rw [hpair, hj]
    exact hzz

/-- The quadratic local-to-global theorem gives an isotropic vector in the
  complement of a specified hyperbolic pair when every completion has an isotropic plane. -/
theorem exists_complement_isotropic_of_local_planes [NumberField K] [FiniteDimensional K V]
    (hS : B.IsSymm) (hB : B.Nondegenerate)
    (hl : ∀ v : Global.Place K, let R := Global.placeCompletion K v
      let C := B.baseChange R
      ∃ x y : R ⊗[K] V, LinearIndependent R ![x, y] ∧ C x x = 0 ∧ C x y = 0 ∧ C y y = 0) :
    ∃ z : P.orthogonalComplement, z ≠ 0 ∧ B z z = 0 := by
  let W := P.orthogonalComplement
  let B₀ := B.restrict W
  let q : QuadraticForm K W := B₀.toQuadraticMap
  have hnd := P.nondegenerate_restrict hS hB
  have hpol (x y : W) : q.polarBilin x y = (2 : K) * B₀ x y := by
    change B₀.toQuadraticMap.polarBilin x y = _
    rw [LinearMap.BilinMap.polarBilin_toQuadraticMap, LinearMap.add_apply, LinearMap.add_apply,
      LinearMap.flip_apply, show B₀ y x = B₀ x y from hS.eq _ _, two_mul]
  have hq : q.polarBilin.Nondegenerate := by
    refine ⟨fun x hx => hnd.1 x fun y => ?_, fun y hy => hnd.2 y fun x => ?_⟩
    · exact (mul_eq_zero.mp ((hpol x y).symm.trans (hx y))).resolve_left two_ne_zero
    · exact (mul_eq_zero.mp ((hpol x y).symm.trans (hy x))).resolve_left two_ne_zero
  let : Invertible (2 : K) := invertibleOfNonzero (two_ne_zero : (2 : K) ≠ 0)
  have hlocal (R : Type u) [Field R] [Algebra K R]
      (h : let C := B.baseChange R
        ∃ x y : R ⊗[K] V, LinearIndependent R ![x, y] ∧ C x x = 0 ∧ C x y = 0 ∧ C y y = 0) :
      ¬ (q.baseChange R).Anisotropic := by
    obtain ⟨x, y, hxy, hx0, hxy0, hy0⟩ := h
    obtain ⟨z, hz, hzz⟩ := P.exists_baseChange_complement_isotropic
      (R := R) (x := x) (y := y) hS hxy hx0 hxy0 hy0
    have heq : q.baseChange R = (B₀.baseChange R).toQuadraticMap := by
      apply baseChange_ext
      intro w
      rw [QuadraticForm.baseChange_tmul]
      change B₀ w w • ((1 : R) * 1) = (B₀.baseChange R) ((1 : R) ⊗ₜ[K] w) ((1 : R) ⊗ₜ[K] w)
      rw [LinearMap.BilinForm.baseChange_tmul]
    rw [heq]
    exact (QuadraticMap.not_anisotropic_iff_exists _).mpr ⟨z, hz, hzz⟩
  have hloc (v : Global.Place K) : ¬ (q.baseChange (Global.placeCompletion K v)).Anisotropic := by
    rcases v with v | v
    · exact hlocal v.Completion (hl (.inl v))
    · exact hlocal (Global.FiniteCompletion K v) (hl (.inr v))
  exact (QuadraticMap.not_anisotropic_iff_exists q).mp
    (Langlands.numberFieldQuadraticIsotropy_of_cyclicNorm ClassFieldTheory.Global.cyclicHasseNorm K W q hq hloc)

end Langlands.SymmetricBilinear.HyperbolicPair

namespace Langlands.GroupScheme.KneserThree.QuatData

open QuadField Quaternionic Langlands.SymmetricBilinear

variable {F D : Type u} [Field F] [DivisionRing D] [Algebra F D] (Q : QuatData F D)
  {τ : FirstKindInvolution F D} {V : Type u} [AddCommGroup V] [Module F V]
  [Module D V] [IsScalarTower F D V] (B : AntihermitianForm τ V) (hbar : ∀ z, τ z = Q.bar z)

local notation "E" => field Q.c
local notation "C" => Q.symmetricComponent B hbar
local notation "κ" => SU3Root.conjugation F E

omit [Module F V] [IsScalarTower F D V] in
private theorem component_root_ne_zero : (root : E) ≠ 0 := by
  intro h
  have h0 := Q.basis.ne_zero 1
  rw [show Q.basis 1 = Q.x from congrFun Q.basis_eq 1, ← Q.ι_root, h, map_zero] at h0
  exact h0 rfl

private def linePair (e : V) (he : B e e = Q.x) :
    letI : Module E V := Module.compHom V Q.ι.toRingHom
    HyperbolicPair C := by
  let : Module E V := Module.compHom V Q.ι.toRingHom
  have hxe : C e e = 0 := by rw [Q.symmetricComponent_apply, he, ← Q.ι_root, Q.snd_ι, map_zero]
  have hxy : C e (Q.jAction e) = -(root : E) := by
    rw [Q.symmetricComponent_jAction_right, he, ← Q.ι_root, Q.fst_ι]
  refine ⟨e, (-(root : E))⁻¹ • Q.jAction e, hxe, ?_, ?_⟩
  · rw [map_smul, hxy, smul_eq_mul, inv_mul_cancel₀ (neg_ne_zero.mpr Q.component_root_ne_zero)]
  · simp only [map_smul, LinearMap.smul_apply, Q.symmetricComponent_jAction_both, hxe,
      map_zero, mul_zero, smul_zero]

private theorem skew_orthogonal_of_mem_linePair {e z : V} (he : B e e = Q.x)
    (hz : letI : Module E V := Module.compHom V Q.ι.toRingHom
      z ∈ (Q.linePair B hbar e he).orthogonalComplement) : B e z = 0 := by
  let : Module E V := Module.compHom V Q.ι.toRingHom
  have h₁ : κ (Q.snd (B e z)) = 0 := hz.1
  have h₂ : ((-(root : E))⁻¹ : E) • C (Q.jAction e) z = 0 := by
    have h : C ((-(root : E))⁻¹ • Q.jAction e) z = 0 := hz.2
    simpa only [map_smul, LinearMap.smul_apply] using h
  have hs := (map_eq_zero_iff κ (κ).injective).mp h₁
  have hf := (smul_eq_zero.mp h₂).resolve_left (inv_ne_zero (neg_ne_zero.mpr Q.component_root_ne_zero))
  rw [Q.symmetricComponent_jAction_left, map_eq_zero_iff κ (κ).injective] at hf
  rw [← Q.decompose (B e z), hs, hf, map_zero, mul_zero, add_zero]

end Langlands.GroupScheme.KneserThree.QuatData

namespace Langlands.GroupScheme.Quaternionic

open KneserThree QuadField Langlands.SymmetricBilinear

/-- Local nonsingular skew isotropy supplies a nonzero vector in the orthogonal
  complement of a prescribed nondegenerate line, with value in its pure scalar line. -/
def NumberFieldSkewProjectiveComplementStatement : Prop :=
  ∀ (F D : Type u) [Field F] [NumberField F] [DivisionRing D] [Algebra F D]
    [FiniteDimensional F D] [Algebra.IsCentral F D] (σ : FirstKindInvolution F D)
    (hdim : Module.finrank F D = 4) (hsym : Module.finrank F σ.symmetricSubspace = 3),
    let τ := σ.quaternionConjugation hdim hsym
    ∀ (I : Type) [Fintype I] [DecidableEq I] (H : Matrix I I D), τ.IsAntihermitian H →
    IsUnit H → τ.IsLocallyNonsingularIsotropic H → ∀ e : I → D, τ.sesqForm H e e ≠ 0 →
    ∃ z : I → D, z ≠ 0 ∧ τ.sesqForm H e z = 0 ∧ ∃ a : F, τ.sesqForm H z z = a • τ.sesqForm H e e

theorem numberFieldSkewProjectiveComplement : NumberFieldSkewProjectiveComplementStatement.{u} := by
  intro F D _ _ _ _ _ _ σ hdim hsym τ I _ _ H hH hu hl e he
  let B := AntihermitianForm.ofMatrix hH
  let a := B e e
  have ha : τ a = -a := by
    have h := congrArg Neg.neg (B.skew e e)
    simpa only [neg_neg] using h.symm
  obtain ⟨Q, hQa, hbar⟩ := Quaternion.exists_quatData_of_pure σ hdim hsym two_ne_zero he ha
  let E := field Q.c
  let : NumberField E := NumberField.of_module_finite F E
  let V := I → D
  let : Module E V := Module.compHom V Q.ι.toRingHom
  let : IsScalarTower F E V := ⟨fun s r x => by
    change Q.ι (s • r) • x = s • (Q.ι r • x)
    rw [map_smul, smul_assoc]⟩
  let : FiniteDimensional E V := Module.Finite.of_restrictScalars_finite F E V
  let C := Q.symmetricComponent B hbar
  have hC : C.IsSymm := ⟨fun x y => Q.symmetricComponent_swap B hbar y x⟩
  let P := Q.linePair B hbar e hQa.symm
  have hCnd := Q.symmetricComponent_nondegenerate B hbar (AntihermitianForm.ofMatrix_separatingLeft hH hu)
  obtain ⟨w, hw, hw0⟩ := P.exists_complement_isotropic_of_local_planes hC hCnd
    (Q.symmetricComponent_local_isotropic_pair τ hbar hH hu hl)
  have hw' : (w : V) ≠ 0 := fun h => hw (Subtype.ext h)
  have hew : B e w = 0 := Q.skew_orthogonal_of_mem_linePair B hbar hQa.symm w.property
  obtain ⟨s, hs⟩ := (Q.symmetricComponent_self_eq_zero_iff B hbar two_ne_zero (w : V)).mp hw0
  exact ⟨w, hw', hew, s, hs.trans (congrArg (s • ·) hQa)⟩

end Langlands.GroupScheme.Quaternionic
