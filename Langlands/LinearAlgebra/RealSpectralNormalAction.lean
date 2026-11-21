import Langlands.LinearAlgebra.RealSpectralStratumChart
import Mathlib.Analysis.Normed.Group.Submodule
import Mathlib.Analysis.Normed.Operator.NormedSpace

/-! # Quotient and trace dual descriptions of the real spectral normal action -/

noncomputable section

open Matrix
open scoped Matrix.Norms.Operator Topology

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 4

namespace Langlands

variable {n : ℕ}

local notation "Mat" => Matrix (Fin n) (Fin n) ℝ
local notation:max "T[" A "]" => LinearMap.range (matrixConjugationTangent A)
local notation:max "Z[" A "]" => realMatrixSemisimpleDirections A
local notation:max "S[" A "]" => (T[A] ⊔ Z[A])
local notation:max "C[" A "]" => matrixConormalWith A Z[A]

variable {A : Matrix (Fin n) (Fin n) ℝ} {W : Submodule ℝ (Matrix (Fin n) (Fin n) ℝ)}
  {N : Submodule ℝ W}
variable (hZW : Z[A] ≤ W) (hTW : IsCompl T[A] W) (hN : IsCompl (Z[A].comap W.subtype) N)

/-- The linear sum map for the orbit, semisimple, and normal coordinates of the slice. -/
def realMatrixStratumLinearEquiv : ((T[A] × Z[A]) × N) ≃ₗ[ℝ] Mat :=
  let i : Z[A] ≃ₗ[ℝ] Z[A].comap W.subtype := (Submodule.comapSubtypeEquivOfLe hZW).symm
  let j : (Z[A] × N) ≃ₗ[ℝ] W :=
    (i.prodCongr (LinearEquiv.refl ℝ N)).trans ((Z[A].comap W.subtype).prodEquivOfIsCompl N hN)
  (LinearEquiv.prodAssoc ℝ T[A] Z[A] N).trans
    (((LinearEquiv.refl ℝ T[A]).prodCongr j).trans (T[A].prodEquivOfIsCompl W hTW))

@[simp]
theorem realMatrixStratumLinearEquiv_apply (p : (T[A] × Z[A]) × N) :
    realMatrixStratumLinearEquiv hZW hTW hN p =
      (p.1.1 : Mat) + (p.1.2 : Mat) + ((p.2 : W) : Mat) := by
  change (p.1.1 : Mat) + ((p.1.2 : Mat) + ((p.2 : W) : Mat)) = _
  rw [add_assoc]

/-- The normal coordinate of an ambient matrix displacement. -/
def realMatrixStratumNormalProjection : Mat →L[ℝ] N :=
  LinearMap.toContinuousLinearMap (𝕜 := ℝ) (E := Mat) (F' := ↥N)
    ((LinearMap.snd ℝ (T[A] × Z[A]) N).comp
      (realMatrixStratumLinearEquiv hZW hTW hN).symm.toLinearMap)

theorem realMatrixStratumNormalProjection_apply (X : Mat) :
    realMatrixStratumNormalProjection hZW hTW hN X =
      ((realMatrixStratumLinearEquiv hZW hTW hN).symm X).2 := rfl

@[simp]
theorem realMatrixStratumNormalProjection_sum (t : T[A]) (z : Z[A]) (y : N) :
    realMatrixStratumNormalProjection hZW hTW hN ((t : Mat) + (z : Mat) + ((y : W) : Mat)) = y := by
  rw [← realMatrixStratumLinearEquiv_apply hZW hTW hN ((t, z), y),
    realMatrixStratumNormalProjection_apply, LinearEquiv.symm_apply_apply]

@[simp]
theorem realMatrixStratumNormalProjection_normal (y : N) :
    realMatrixStratumNormalProjection hZW hTW hN ((y : W) : Mat) = y := by
  simpa only [Submodule.coe_zero, add_zero, zero_add] using
    realMatrixStratumNormalProjection_sum hZW hTW hN 0 0 y

theorem ker_realMatrixStratumNormalProjection :
    LinearMap.ker (realMatrixStratumNormalProjection hZW hTW hN).toLinearMap = S[A] := by
  let E := realMatrixStratumLinearEquiv hZW hTW hN
  let P := realMatrixStratumNormalProjection hZW hTW hN
  ext X
  change P X = 0 ↔ X ∈ S[A]
  constructor
  · intro h
    have he := E.apply_symm_apply X
    rw [realMatrixStratumLinearEquiv_apply] at he
    change ((E.symm X).2 : N) = 0 at h
    rw [h, Submodule.coe_zero, Submodule.coe_zero, add_zero] at he
    exact he ▸ Submodule.mem_sup.mpr ⟨_, (E.symm X).1.1.property, _, (E.symm X).1.2.property, rfl⟩
  · intro h
    obtain ⟨t, ht, z, hz, rfl⟩ := Submodule.mem_sup.mp h
    simpa only [Submodule.coe_zero, add_zero] using
      realMatrixStratumNormalProjection_sum hZW hTW hN ⟨t, ht⟩ ⟨z, hz⟩ 0

theorem sub_normalProjection_mem_realMatrixStratumTangent (X : Mat) :
    X - (((realMatrixStratumNormalProjection hZW hTW hN X : N) : W) : Mat) ∈ S[A] := by
  rw [← ker_realMatrixStratumNormalProjection hZW hTW hN, LinearMap.mem_ker]
  change realMatrixStratumNormalProjection hZW hTW hN
    (X - (((realMatrixStratumNormalProjection hZW hTW hN X : N) : W) : Mat)) = 0
  rw [map_sub, realMatrixStratumNormalProjection_normal, sub_self]

/-- The normal coordinates identify with the quotient by the orbit and semisimple directions. -/
def realMatrixStratumNormalQuotientEquiv : (Mat ⧸ S[A]) ≃ₗ[ℝ] N := by
  let P : Mat →ₗ[ℝ] ↥N := (realMatrixStratumNormalProjection hZW hTW hN).toLinearMap
  let F : (Mat ⧸ S[A]) →ₗ[ℝ] ↥N := S[A].liftQ P
    (ker_realMatrixStratumNormalProjection hZW hTW hN).ge
  let G : ↥N →ₗ[ℝ] (Mat ⧸ S[A]) := S[A].mkQ.comp (W.subtype.comp N.subtype)
  refine LinearEquiv.ofLinearMap (f := F) (g := G) ?_ ?_
  · ext1 y
    change P ((y : W) : Mat) = y
    exact realMatrixStratumNormalProjection_normal hZW hTW hN y
  · apply Submodule.linearMap_qext
    ext1 X
    change (Submodule.Quotient.mk (((P X : N) : W) : Mat) : Mat ⧸ S[A]) = Submodule.Quotient.mk X
    apply (Submodule.Quotient.eq _).2
    rw [← neg_sub]
    exact Submodule.neg_mem S[A] (sub_normalProjection_mem_realMatrixStratumTangent hZW hTW hN X)

@[simp]
theorem realMatrixStratumNormalQuotientEquiv_apply_mk (X : Mat) :
    realMatrixStratumNormalQuotientEquiv hZW hTW hN (Submodule.Quotient.mk X) =
      realMatrixStratumNormalProjection hZW hTW hN X := rfl

/-- Compress an ambient map to the chosen normal complement by inclusion and projection.
If the map preserves the sum of the orbit tangent and semisimple directions, this compression
represents the induced map on the normal quotient. -/
def realMatrixStratumNormalAction (L : Mat →L[ℝ] Mat) : N →L[ℝ] N :=
  (realMatrixStratumNormalProjection hZW hTW hN).comp (L.comp (W.subtypeL.comp N.subtypeL))

@[simp]
theorem realMatrixStratumNormalAction_apply (L : Mat →L[ℝ] Mat) (y : N) :
    realMatrixStratumNormalAction hZW hTW hN L y =
      realMatrixStratumNormalProjection hZW hTW hN (L ((y : W) : Mat)) := rfl

private theorem det_prod_triangular {E F : Type*} [AddCommGroup E] [Module ℝ E]
    [FiniteDimensional ℝ E] [AddCommGroup F] [Module ℝ F] [FiniteDimensional ℝ F]
    (L : (E × F) →ₗ[ℝ] (E × F)) (R : E →ₗ[ℝ] E) (Q : F →ₗ[ℝ] F)
    (h₁ : ∀ x, L (x, 0) = (R x, 0)) (h₂ : ∀ y, (L (0, y)).2 = Q y) :
    LinearMap.det L = LinearMap.det R * LinearMap.det Q := by
  let b := Module.finBasis ℝ E
  let c := Module.finBasis ℝ F
  let U := ((LinearMap.fst ℝ E F).comp L).comp (LinearMap.inr ℝ E F)
  have hm : LinearMap.toMatrix (b.prod c) (b.prod c) L =
      Matrix.fromBlocks (LinearMap.toMatrix b b R) (LinearMap.toMatrix c b U) 0
        (LinearMap.toMatrix c c Q) := by
    ext (i | i) (j | j) <;> simp [LinearMap.toMatrix_apply, U, h₁, h₂]
  rw [← LinearMap.det_toMatrix (b.prod c), hm, Matrix.det_fromBlocks_zero₂₁,
    LinearMap.det_toMatrix, LinearMap.det_toMatrix]

/-- In the stratum coordinates, the ambient determinant is the orbit tangent determinant times
the normal determinant. The semisimple directions are fixed. -/
theorem det_realMatrixStratumNormalAction (L : Mat →L[ℝ] Mat)
    (hT : T[A] ≤ T[A].comap L.toLinearMap) (hZ : ∀ z ∈ Z[A], L z = z) :
    LinearMap.det L.toLinearMap =
      LinearMap.det (L.toLinearMap.restrict (p := T[A]) (q := T[A]) hT) *
        LinearMap.det (M := ↥N) (realMatrixStratumNormalAction hZW hTW hN L).toLinearMap := by
  let E := realMatrixStratumLinearEquiv hZW hTW hN
  let B := E.symm.conj L.toLinearMap
  let R := L.toLinearMap.restrict (p := T[A]) (q := T[A]) hT
  let Q := (realMatrixStratumNormalAction hZW hTW hN L).toLinearMap
  have h₁ (p : T[A] × Z[A]) : B (p, 0) = ((R p.1, p.2), 0) := by
    apply E.injective
    change E (E.symm (L (E (p, 0)))) = E ((R p.1, p.2), 0)
    rw [E.apply_symm_apply, realMatrixStratumLinearEquiv_apply, realMatrixStratumLinearEquiv_apply]
    simp only [Submodule.coe_zero, add_zero, map_add, hZ _ p.2.property]
    rfl
  have h₂ (y : N) : (B (0, y)).2 = Q y := by
    change (E.symm (L (E (0, y)))).2 = Q y
    rw [realMatrixStratumLinearEquiv_apply]
    simp only [Prod.fst_zero, Prod.snd_zero, Submodule.coe_zero, zero_add]
    rfl
  have hd := det_prod_triangular (E := ↥(T[A]) × ↥(Z[A])) (F := ↥N)
    B (R.prodMap (LinearMap.id : Z[A] →ₗ[ℝ] Z[A])) Q h₁ h₂
  have hB : LinearMap.det (M := (↥(T[A]) × ↥(Z[A])) × ↥N) B = LinearMap.det L.toLinearMap := by
    change LinearMap.det (E.symm.toLinearMap ∘ₗ L.toLinearMap ∘ₗ E.symm.symm.toLinearMap) = _
    exact LinearMap.det_conj _ _
  rwa [hB, LinearMap.det_prodMap, LinearMap.det_id, mul_one] at hd

theorem abs_det_realMatrixStratumNormalAction (L : Mat →L[ℝ] Mat)
    (hT : T[A] ≤ T[A].comap L.toLinearMap) (hZ : ∀ z ∈ Z[A], L z = z)
    (hL : |LinearMap.det L.toLinearMap| = 1)
    (hR : |LinearMap.det (L.toLinearMap.restrict (p := T[A]) (q := T[A]) hT)| = 1) :
    (|LinearMap.det (M := ↥N) (realMatrixStratumNormalAction hZW hTW hN L).toLinearMap| : ℝ) = 1 := by
  rw [det_realMatrixStratumNormalAction hZW hTW hN L hT hZ, abs_mul, hR, one_mul] at hL
  exact hL

/-- The ambient trace functional restricted to the chosen normal complement. -/
def realMatrixTraceNormalFunctional (W : Submodule ℝ Mat) (N : Submodule ℝ W) :
    Mat →ₗ[ℝ] (N →L[ℝ] ℝ) :=
  (LinearMap.toContinuousLinearMap (𝕜 := ℝ) (E := ↥N) (F' := ℝ)).toLinearMap.comp
    ((W.subtype.comp N.subtype).dualMap.comp matrixTraceBilin)

@[simp]
theorem realMatrixTraceNormalFunctional_apply (X : Mat) (y : N) :
    realMatrixTraceNormalFunctional W N X y = matrixTraceBilin X ((y : W) : Mat) := rfl

/-- Restriction of the trace form identifies the trace conormal with the continuous dual of the
chosen normal coordinates. -/
def realMatrixStratumConormalEquiv : C[A] ≃L[ℝ] (N →L[ℝ] ℝ) :=
  (((matrixTraceOrthogonalEquivDualQuotient S[A]).trans
    (realMatrixStratumNormalQuotientEquiv hZW hTW hN).symm.dualMap).trans
      LinearMap.toContinuousLinearMap).toContinuousLinearEquiv

@[simp]
theorem realMatrixStratumConormalEquiv_apply (X : C[A]) :
    realMatrixStratumConormalEquiv hZW hTW hN X = realMatrixTraceNormalFunctional W N X := by
  ext y
  have he : (realMatrixStratumNormalQuotientEquiv hZW hTW hN).symm y =
      Submodule.Quotient.mk (((y : W) : Mat)) := by
    rw [LinearEquiv.symm_apply_eq, realMatrixStratumNormalQuotientEquiv_apply_mk,
      realMatrixStratumNormalProjection_normal]
  change matrixTraceOrthogonalEquivDualQuotient S[A] X
    ((realMatrixStratumNormalQuotientEquiv hZW hTW hN).symm y) = matrixTraceBilin X.val ((y : W) : Mat)
  rw [he, matrixTraceOrthogonalEquivDualQuotient_apply_mk]

theorem realMatrixTraceNormalFunctional_comp (L : Mat ≃L[ℝ] Mat)
    (hB : ∀ X Y, matrixTraceBilin (L X) (L Y) = matrixTraceBilin X Y)
    {X : Mat} (hX : X ∈ C[A]) :
    (realMatrixTraceNormalFunctional W N X).comp (realMatrixStratumNormalAction hZW hTW hN L) =
      realMatrixTraceNormalFunctional W N (L.symm X) := by
  ext y
  let V : Mat := L ((y : W) : Mat)
  let P := realMatrixStratumNormalProjection hZW hTW hN
  have hsub := sub_normalProjection_mem_realMatrixStratumTangent hZW hTW hN V
  have hz := hX _ hsub
  change matrixTraceBilin (V - (((P V : N) : W) : Mat)) X = 0 at hz
  rw [matrixTraceBilin_isSymm.eq, map_sub, sub_eq_zero] at hz
  change matrixTraceBilin X (((P V : N) : W) : Mat) = matrixTraceBilin (L.symm X) ((y : W) : Mat)
  rw [← hz]
  change matrixTraceBilin X (L ((y : W) : Mat)) = matrixTraceBilin (L.symm X) ((y : W) : Mat)
  simpa only [L.apply_symm_apply] using hB (L.symm X) ((y : W) : Mat)

end Langlands
