import Langlands.Algebra.CorrectedCyclicDeterminant
import Langlands.BaseChange.CyclicMatrixCoordinates
import Langlands.BaseChange.TwistedCharacter.SemisimpleSlice

/-! # The determinant of the twisted Weyl differential -/

noncomputable section

namespace Langlands.BaseChange

open Langlands.JacquetLanglands
open scoped TensorProduct
open Fin.NatCast

universe u v w

variable {F : Type u} [Field F] {E : Type v} [CommRing E] [Algebra F E]
  {K : Type w} [Field K] [Algebra F K] {n l : ℕ}

local notation "MF" => Matrix (Fin n) (Fin n) F
local notation "ME" => Matrix (Fin n) (Fin n) E
local notation "MK" => Matrix (Fin n) (Fin n) K

private theorem linearAdjoint_apply {B : Type*} [Field B]
    (g : GeneralLinear n B) (x : Matrix (Fin n) (Fin n) B) :
    linearAdjoint g x = g.val * x * g⁻¹.val := by
  simp [linearAdjoint, mul_assoc]

private def linearAdjointHom (K : Type*) [Field K] (n : ℕ) :
    GeneralLinear n K →* Module.End K (Matrix (Fin n) (Fin n) K) where
  toFun := linearAdjoint
  map_one' := by
    apply LinearMap.ext
    intro x
    simp [linearAdjoint_apply]
  map_mul' a b := by
    apply LinearMap.ext
    intro x
    simp only [Module.End.mul_apply, linearAdjoint_apply, Units.val_mul, mul_inv_rev, mul_assoc]

private theorem matrixScalarExtension_tmul_eq (a : K) (x : MF) :
    matrixScalarExtension (a ⊗ₜ[F] x) = a • (algebraMap F K).mapMatrix x :=
  Matrix.ext fun p q => matrixScalarExtension_tmul a x p q

private theorem cyclicMatrixScalarExtension_tmul_eq
    (e : (K ⊗[F] E) ≃ₐ[K] (Fin l → K)) (a : K) (x : ME) (j : Fin l) :
    cyclicMatrixScalarExtension e (a ⊗ₜ[F] x) j =
      a • (cyclicCoordinate e j).toRingHom.mapMatrix x :=
  Matrix.ext fun p q => cyclicMatrixScalarExtension_tmul e a x j p q

private theorem matrixScalarExtension_adjoint (g : GeneralLinear n F) (x : K ⊗[F] MF) :
    matrixScalarExtension ((linearAdjoint g).baseChange K x) =
      linearAdjoint (baseChange F K n g) (matrixScalarExtension x) := by
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul a x =>
    rw [LinearMap.baseChange_tmul, matrixScalarExtension_tmul_eq, matrixScalarExtension_tmul_eq,
      map_smul, linearAdjoint_apply, linearAdjoint_apply, map_mul, map_mul]
    rfl

private theorem cyclicMatrixScalarExtension_twistedAdjoint
    (e : (K ⊗[F] E) ≃ₐ[K] (Fin l → K)) (σ : E ≃ₐ[F] E)
    (he : ∀ x j, e (tensorFactorAut K σ x) j = e x (finRotate l j))
    (δ : GeneralLinear n E) (x : K ⊗[F] ME) (j : Fin l) :
    cyclicMatrixScalarExtension e ((twistedAdjointAlgEquiv σ δ).toLinearMap.baseChange K x) j =
      linearAdjoint (Matrix.GeneralLinearGroup.map (cyclicCoordinate e j).toRingHom δ)
        (cyclicMatrixScalarExtension e x (finRotate l j)) := by
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, Pi.add_apply, hx, hy]
  | tmul a x =>
    rw [LinearMap.baseChange_tmul, cyclicMatrixScalarExtension_tmul_eq,
      cyclicMatrixScalarExtension_tmul_eq, map_smul]
    congr 1
    change (cyclicCoordinate e j).toRingHom.mapMatrix (twistedMatrixConj σ δ x) = _
    rw [twistedMatrixConj_apply, linearAdjoint_apply, map_mul, map_mul]
    congr 2
    exact Matrix.ext fun p q => cyclicCoordinate_shift e σ he j (x p q)

private theorem cyclicCoordinate_mapMatrix_base (e : (K ⊗[F] E) ≃ₐ[K] (Fin l → K))
    (j : Fin l) (x : MF) :
    (cyclicCoordinate e j).toRingHom.mapMatrix (matrixBaseChangeLinear x) =
      (algebraMap F K).mapMatrix x :=
  Matrix.ext fun p q => (cyclicCoordinate e j).commutes (x p q)

private theorem cyclicCoordinate_mapMatrix_sum (e : (K ⊗[F] E) ≃ₐ[K] (Fin l → K))
    (σ : E ≃ₐ[F] E) (he : ∀ x j, e (tensorFactorAut K σ x) j = e x (finRotate l j))
    [NeZero l] (x : ME) :
    ∑ j, (cyclicCoordinate e j).toRingHom.mapMatrix x =
      (cyclicCoordinate e (0 : Fin l)).toRingHom.mapMatrix
        (∑ j : Fin l, matrixEntrywiseAut (σ ^ (j : ℕ)) x) := by
  apply Matrix.ext
  intro p q
  rw [map_sum, Matrix.sum_apply, Matrix.sum_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  change cyclicCoordinate e j (x p q) = cyclicCoordinate e 0 ((σ ^ (j : ℕ)) (x p q))
  rw [cyclicCoordinate_pow e σ he, zero_add,
    show ((j : ℕ) : Fin l) = j from Fin.ext (Nat.mod_eq_of_lt j.isLt)]

set_option maxHeartbeats 800000 in
/-- A section of the additive trace completes the twisted orbit differential.
Its determinant is the ordinary discriminant at the exact regular norm. -/
theorem WeylTorus.det_twistedWeylDifferential
    (T : WeylTorus F n) {σ : E ≃ₐ[F] E} (hσ : IsCyclicAlgebra σ l)
    {t : T.val} (ht : t ∈ T.regularPoints) (δ : T.points E)
    (hnorm : cyclicNorm σ l δ.val = baseChange F E n t.val)
    (p : ME →ₗ[F] weylTorusLie t.val)
    (hp : ∀ x, p (weylTorusLieInclusion t.val x) = x)
    (s : weylTorusLie t.val →ₗ[F] ME)
    (hs : ∀ x, Commute (s x) (baseChange F E n t.val).val)
    (htrace : ∀ x, ∑ i : Fin l, matrixEntrywiseAut (σ ^ (i : ℕ)) (s x) =
      weylTorusLieInclusion t.val x) :
    let D : Module.End F ME := 1 - (twistedAdjointAlgEquiv σ δ.val).toLinearMap + s.comp p
    IsUnit D.det ∧ D.det = weylDiscriminant t.val := by
  classical
  let : Module.Finite F E := hσ.1
  let : Module.Finite F ME := inferInstanceAs (Module.Finite F (Fin n → Fin n → E))
  let K := AlgebraicClosure F
  cases l with
  | zero => exact (Nat.not_lt_zero _ hσ.pos).elim
  | succ d =>
    obtain ⟨e, he⟩ := hσ.exists_splitCoordinates_baseChange K
    let γ := t.val
    let g := baseChange F K n γ
    let b := adjointDefect γ
    let S := weylTorusLie γ
    let S' := K ⊗[F] S
    let M' := Matrix (Fin n) (Fin n) K
    let e₀ : (K ⊗[F] MF) ≃ₗ[K] M' := matrixScalarExtension
    let e₁ : (K ⊗[F] ME) ≃ₗ[K] (Fin (d + 1) → M') := cyclicMatrixScalarExtension e
    let i₀ := S.subtype
    let i₁ := weylTorusLieInclusion (E := E) γ
    let p₀ := S.projectionOnto b.range (isCompl_ker_range_adjointDefect γ ht)
    let i : S' →ₗ[K] M' := e₀.toLinearMap.comp (i₀.baseChange K)
    let p' : M' →ₗ[K] S' := (p₀.baseChange K).comp e₀.symm.toLinearMap
    let π : (Fin (d + 1) → M') →ₗ[K] S' := (p.baseChange K).comp e₁.symm.toLinearMap
    let δ' (j : Fin (d + 1)) := Matrix.GeneralLinearGroup.map (cyclicCoordinate e j).toRingHom δ.val
    let A (j : Fin (d + 1)) : Module.End K M' := linearAdjoint (δ' j)
    let u : S' →ₗ[K] (Fin (d + 1) → M') := e₁.toLinearMap.comp (s.baseChange K)
    let f : S' →ₗ[K] (Fin (d + 1) → S') := LinearMap.pi fun j =>
      p'.comp ((LinearMap.proj j).comp u)
    have hp' (x : S') : p' (i x) = x := by
      have hp₀ : p₀.comp i₀ = LinearMap.id := by
        apply LinearMap.ext
        intro y
        exact S.projectionOnto_apply_left _ y
      have hh := congrArg (LinearMap.baseChange K) hp₀
      rw [LinearMap.baseChange_comp, LinearMap.baseChange_id] at hh
      change (p₀.baseChange K) (e₀.symm (e₀ ((i₀.baseChange K) x))) = x
      rw [e₀.symm_apply_apply]
      exact DFunLike.congr_fun hh x
    have hdiagonal (x : S') : e₁ ((i₁.baseChange K) x) = fun _ => i x := by
      induction x using TensorProduct.inductionOn with
      | add x y hx hy =>
        change e₁ ((i₁.baseChange K) (x + y)) = fun _ => i (x + y)
        rw [map_add, map_add, hx, hy]
        funext j
        exact (i.map_add x y).symm
      | tmul a x =>
        funext j
        change (cyclicMatrixScalarExtension e) ((i₁.baseChange K) (a ⊗ₜ[F] x)) j =
          matrixScalarExtension ((i₀.baseChange K) (a ⊗ₜ[F] x))
        rw [LinearMap.baseChange_tmul, LinearMap.baseChange_tmul,
          cyclicMatrixScalarExtension_tmul_eq, matrixScalarExtension_tmul_eq]
        exact congrArg (a • ·) (cyclicCoordinate_mapMatrix_base e j x.val)
    have hπ (x : S') : π (fun _ => i x) = x := by
      rw [← hdiagonal]
      change (p.baseChange K) (e₁.symm (e₁ ((i₁.baseChange K) x))) = x
      rw [e₁.symm_apply_apply]
      have hh : p.comp i₁ = LinearMap.id := LinearMap.ext hp
      have hb := congrArg (LinearMap.baseChange K) hh
      rw [LinearMap.baseChange_comp, LinearMap.baseChange_id] at hb
      exact DFunLike.congr_fun hb x
    have hA (j : Fin (d + 1)) (x : S') : A j (i x) = i x := by
      induction x using TensorProduct.inductionOn with
      | add x y hx hy => simp only [map_add, hx, hy]
      | tmul a x =>
        change linearAdjoint (δ' j) (matrixScalarExtension (a ⊗ₜ[F] x.val)) =
          matrixScalarExtension (a ⊗ₜ[F] x.val)
        rw [matrixScalarExtension_tmul_eq, map_smul]
        congr 1
        have h := (T.commute_weylTorusLieInclusion hσ ht δ x).map
          (cyclicCoordinate e j).toRingHom.mapMatrix
        rw [show (cyclicCoordinate e j).toRingHom.mapMatrix (weylTorusLieInclusion γ x) =
          (algebraMap F K).mapMatrix x.val from cyclicCoordinate_mapMatrix_base e j x.val] at h
        change Commute (δ' j).val ((algebraMap F K).mapMatrix x.val) at h
        rw [linearAdjoint_apply]
        change (δ' j).val * _ * (δ' j)⁻¹.val = _
        rw [h.eq, mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, mul_one]
    have hbase (x : K ⊗[F] MF) : e₀ (b.baseChange K x) = adjointDefect g (e₀ x) := by
      change e₀ ((linearAdjoint γ - LinearMap.id).baseChange K x) = _
      rw [LinearMap.baseChange_sub, LinearMap.baseChange_id, LinearMap.sub_apply, map_sub]
      exact congrArg (· - e₀ x) (matrixScalarExtension_adjoint γ x)
    have hexact (z : M') (hz : adjointDefect g z = 0) : ∃ x : S', i x = z := by
      have hk : b.baseChange K (e₀.symm z) = 0 := by
        apply e₀.injective
        rw [hbase, e₀.apply_symm_apply, hz, map_zero]
      obtain ⟨x, hx⟩ := (Module.Flat.lTensor_exact K b.exact_subtype_ker_map _).mp hk
      refine ⟨x, ?_⟩
      change e₀ ((i₀.baseChange K) x) = z
      change (i₀.baseChange K) x = e₀.symm z at hx
      rw [hx, e₀.apply_symm_apply]
    have hu (x : S') (j : Fin (d + 1)) : adjointDefect g (u x j) = 0 := by
      induction x using TensorProduct.inductionOn with
      | add x y hx hy => simp only [map_add, Pi.add_apply, hx, hy, add_zero]
      | tmul a x =>
        change adjointDefect g (cyclicMatrixScalarExtension e ((s.baseChange K) (a ⊗ₜ[F] x)) j) = 0
        rw [LinearMap.baseChange_tmul, cyclicMatrixScalarExtension_tmul_eq, map_smul]
        suffices hs' : adjointDefect g ((cyclicCoordinate e j).toRingHom.mapMatrix (s x)) = 0 by
          rw [hs', smul_zero]
        apply LinearMap.mem_ker.mp
        apply (mem_ker_adjointDefect_iff _ _).mpr
        have hh := (hs x).map (cyclicCoordinate e j).toRingHom.mapMatrix
        change Commute ((cyclicCoordinate e j).toRingHom.mapMatrix (s x))
          ((cyclicCoordinate e j).toRingHom.mapMatrix (matrixBaseChangeLinear γ.val)) at hh
        rwa [cyclicCoordinate_mapMatrix_base e j γ.val] at hh
    have huf (x : S') (j : Fin (d + 1)) : i (f x j) = u x j := by
      obtain ⟨y, hy⟩ := hexact (u x j) (hu x j)
      change i (p' (u x j)) = u x j
      rw [← hy, hp']
    have hsum (x : S') : ∑ j, u x j = i x := by
      induction x using TensorProduct.inductionOn with
      | add x y hx hy =>
        simp only [map_add, Pi.add_apply, Finset.sum_add_distrib, hx, hy]
      | tmul a x =>
        change (∑ j, cyclicMatrixScalarExtension e ((s.baseChange K) (a ⊗ₜ[F] x)) j) =
          matrixScalarExtension ((i₀.baseChange K) (a ⊗ₜ[F] x))
        simp only [LinearMap.baseChange_tmul, cyclicMatrixScalarExtension_tmul_eq,
          matrixScalarExtension_tmul_eq, ← Finset.smul_sum, cyclicCoordinate_mapMatrix_sum e σ he,
          htrace]
        exact congrArg (a • ·) (cyclicCoordinate_mapMatrix_base e 0 x.val)
    have hf (x : S') : ∑ j, f x j = x := by
      change ∑ j, p' (u x j) = x
      rw [← map_sum, hsum, hp']
    let D : Module.End F ME := 1 - (twistedAdjointAlgEquiv σ δ.val).toLinearMap + s.comp p
    let C : Module.End K (Fin (d + 1) → M') := Algebra.weightedCycleDefect A +
      (LinearMap.pi fun j => i.comp ((LinearMap.proj j).comp f)).comp π
    have hD (x : K ⊗[F] ME) : e₁ (D.baseChange K x) = C (e₁ x) := by
      have hcomp : π (e₁ x) = p.baseChange K x := by simp [π]
      change e₁ ((1 - (twistedAdjointAlgEquiv σ δ.val).toLinearMap + s.comp p).baseChange K x) = _
      rw [LinearMap.baseChange_add, LinearMap.baseChange_sub, LinearMap.baseChange_one,
        LinearMap.baseChange_comp]
      funext j
      simp only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.sub_apply, map_add, map_sub,
        Module.End.one_apply, Pi.add_apply, Pi.sub_apply, C, Algebra.weightedCycleDefect_apply,
        LinearMap.pi_apply, LinearMap.proj_apply, hcomp, huf]
      rw [cyclicMatrixScalarExtension_twistedAdjoint e σ he δ.val x j]
      rfl
    have hC : C = e₁.conj (D.baseChange K) := by
      apply LinearMap.ext
      intro x
      simpa only [LinearEquiv.conj_apply_apply, LinearEquiv.apply_symm_apply] using (hD (e₁.symm x)).symm
    have hprod : (List.ofFn A).prod = linearAdjoint g := by
      have hp := prod_splitCoordinates_units hσ e he δ.val hnorm
      simpa only [A, g, γ, List.map_ofFn, linearAdjointHom, MonoidHom.coe_mk, OneHom.coe_mk,
        Function.comp_def] using
        ((map_list_prod (linearAdjointHom K n) (List.ofFn δ')).symm.trans
          (congrArg (linearAdjointHom K n) hp))
    let D₀ : Module.End F MF := S.projection b.range (isCompl_ker_range_adjointDefect γ ht) - b
    have hD₀ : e₀.conj (D₀.baseChange K) = 1 - linearAdjoint g + i.comp p' := by
      have hmap (x : K ⊗[F] MF) : e₀ (D₀.baseChange K x) =
          i (p' (e₀ x)) - adjointDefect g (e₀ x) := by
        change e₀ ((i₀.comp p₀ - b).baseChange K x) = _
        rw [LinearMap.baseChange_sub, LinearMap.baseChange_comp, LinearMap.sub_apply, map_sub, hbase]
        change i ((p₀.baseChange K) x) - _ = i ((p₀.baseChange K) (e₀.symm (e₀ x))) - _
        rw [e₀.symm_apply_apply]
      apply LinearMap.ext
      intro x
      have hx := hmap (e₀.symm x)
      rw [e₀.apply_symm_apply] at hx
      change e₀ (D₀.baseChange K (e₀.symm x)) = x - linearAdjoint g x + i (p' x)
      rw [hx, adjointDefect_apply, linearAdjoint_apply]
      abel
    have heq : D.det = D₀.det := by
      apply (algebraMap F K).injective
      rw [← LinearMap.det_baseChange, ← LinearMap.det_baseChange]
      calc
        _ = C.det := by
          rw [hC, LinearEquiv.conj_apply, LinearMap.comp_assoc, LinearMap.det_conj]
        _ = (1 - linearAdjoint g + i.comp p').det := by
          rw [show C.det = (1 - (List.ofFn A).prod + i.comp p').det from
            Algebra.det_weightedCycleDefect_add_section A i p' hA π hπ hp' f hf, hprod]
        _ = _ := by rw [← hD₀, LinearEquiv.conj_apply, LinearMap.comp_assoc, LinearMap.det_conj]
    change IsUnit D.det ∧ D.det = _
    rw [heq]
    exact det_ordinaryWeylDifferential γ ht

/-- The differential formula is unchanged when the Lie algebra is presented
as an equal submodule coming from a fixed representative of the torus. -/
theorem WeylTorus.det_twistedWeylDifferential_of_lie_eq
    (T : WeylTorus F n) {σ : E ≃ₐ[F] E} (hσ : IsCyclicAlgebra σ l)
    {t : T.val} (ht : t ∈ T.regularPoints) (δ : T.points E)
    (hnorm : cyclicNorm σ l δ.val = baseChange F E n t.val)
    {S : Submodule F MF} (hS : S = weylTorusLie t.val)
    (p : ME →ₗ[F] S) (hp : ∀ x, p (matrixBaseChangeLinear x.val) = x)
    (s : S →ₗ[F] ME) (hs : ∀ x, Commute (s x) (baseChange F E n t.val).val)
    (htrace : ∀ x, ∑ i : Fin l, matrixEntrywiseAut (σ ^ (i : ℕ)) (s x) =
      matrixBaseChangeLinear x.val) :
    let D : Module.End F ME := 1 - (twistedAdjointAlgEquiv σ δ.val).toLinearMap + s.comp p
    IsUnit D.det ∧ D.det = weylDiscriminant t.val := by
  subst S
  exact T.det_twistedWeylDifferential hσ ht δ hnorm p hp s hs htrace

end Langlands.BaseChange
