import Langlands.LinearAlgebra.RankSixHyperbolicity
import Langlands.LinearAlgebra.NumberFieldQuadraticIsometryProof
import Mathlib.LinearAlgebra.TensorProduct.Prod
import Mathlib.LinearAlgebra.TensorProduct.Basis

/-! # Rank-six hyperbolicity over a number field -/

noncomputable section

universe u

open Matrix QuadraticMap
open scoped TensorProduct

namespace Langlands.SymmetricBilinear

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1700000

section ScalarExtension

variable {K R : Type u} [Field K] [Invertible (2 : K)] [CommRing R] [Algebra K R]
  {V W : Type u} [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]

private def extendIsometry {q : QuadraticForm K V} {r : QuadraticForm K W} (e : q.IsometryEquiv r) :
    (q.baseChange R).IsometryEquiv (r.baseChange R) := by
  let f := TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl R R) e.toLinearEquiv
  refine ⟨f, fun z => ?_⟩
  have h : (r.baseChange R).comp f.toLinearMap = q.baseChange R := by
    apply baseChange_ext
    intro x
    change (r.baseChange R) (f (1 ⊗ₜ[K] x)) = (q.baseChange R) (1 ⊗ₜ[K] x)
    simp [f, e.map_app]
  exact DFunLike.congr_fun h z

private def extendProduct (q : QuadraticForm K V) (r : QuadraticForm K W) :
    (QuadraticForm.baseChange R (q.prod r)).IsometryEquiv ((q.baseChange R).prod (r.baseChange R)) := by
  let f := TensorProduct.prodRight K R R V W
  let t := (q.baseChange R).prod (r.baseChange R)
  refine ⟨f, fun z => ?_⟩
  have h : t.comp f.toLinearMap = QuadraticForm.baseChange R (q.prod r) := by
    apply baseChange_ext
    rintro ⟨x, y⟩
    change t (f (1 ⊗ₜ[K] (x, y))) = QuadraticForm.baseChange R (q.prod r) (1 ⊗ₜ[K] (x, y))
    simp [t, f, Algebra.smul_def]
  exact DFunLike.congr_fun h z

end ScalarExtension

section StandardForm

variable (K R : Type u) [Field K] [Field R] [Invertible (2 : K)] [Algebra K R]

private def extendHyperbolicPlane : ((hyperbolicPlane K).baseChange R).IsometryEquiv (hyperbolicPlane R) := by
  let j := TensorProduct.AlgebraTensorModule.rid K R R
  let f := (TensorProduct.prodRight K R R K K).trans (j.prodCongr j)
  refine ⟨f, fun z => ?_⟩
  have h : (hyperbolicPlane R).comp f.toLinearMap = (hyperbolicPlane K).baseChange R := by
    apply baseChange_ext
    rintro ⟨x, y⟩
    change hyperbolicPlane R (f (1 ⊗ₜ[K] (x, y))) = (hyperbolicPlane K).baseChange R (1 ⊗ₜ[K] (x, y))
    simp [f, j, Algebra.smul_def]
  exact DFunLike.congr_fun h z

private def extendThreeHyperbolicPlanes :
    ((threeHyperbolicPlanes K).baseChange R).IsometryEquiv (threeHyperbolicPlanes R) := by
  let e₁ := extendHyperbolicPlane K R
  let q := hyperbolicPlane K
  let e₂ := (extendProduct (R := R) q q).trans (e₁.prod e₁)
  exact (extendProduct (R := R) q (q.prod q)).trans (e₁.prod e₂)

private theorem polar_nondegenerate_hyperbolicPlane : (hyperbolicPlane K).polarBilin.Nondegenerate := by
  apply LinearMap.BilinForm.Nondegenerate.ofSeparatingLeft
  intro x hx
  have hp (y : K × K) : (hyperbolicPlane K).polarBilin x y = 2 * (x.1 * y.2 + x.2 * y.1) := by
    simp only [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar, hyperbolicPlane_apply,
      Prod.fst_add, Prod.snd_add]
    ring
  have h2 : (2 : K) ≠ 0 := Invertible.ne_zero _
  apply Prod.ext
  · have h := (mul_eq_zero.mp ((hp (0, 1)).symm.trans (hx (0, 1)))).resolve_left h2
    simpa using h
  · have h := (mul_eq_zero.mp ((hp (1, 0)).symm.trans (hx (1, 0)))).resolve_left h2
    simpa using h

end StandardForm

section Nondegeneracy

variable {K : Type u} [Field K] {V W : Type u} [AddCommGroup V] [Module K V]
  [AddCommGroup W] [Module K W]

private theorem polar_nondegenerate_prod {q : QuadraticForm K V} {r : QuadraticForm K W}
    (hq : q.polarBilin.Nondegenerate) (hr : r.polarBilin.Nondegenerate) : (q.prod r).polarBilin.Nondegenerate := by
  refine ⟨fun x hx => ?_, fun x hx => ?_⟩
  · apply Prod.ext
    · exact hq.1 _ (fun y => by simpa [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar_prod] using hx (y, 0))
    · exact hr.1 _ (fun y => by simpa [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar_prod] using hx (0, y))
  · apply Prod.ext
    · exact hq.2 _ (fun y => by simpa [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar_prod] using hx (y, 0))
    · exact hr.2 _ (fun y => by simpa [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar_prod] using hx (0, y))

private theorem polar_nondegenerate_comp {q : QuadraticForm K V} (h : q.polarBilin.Nondegenerate)
    (f : W ≃ₗ[K] V) : (q.comp f.toLinearMap).polarBilin.Nondegenerate := by
  rw [QuadraticMap.polarBilin_comp]
  refine ⟨fun x hx => f.injective ?_, fun y hy => f.injective ?_⟩
  · rw [map_zero]
    apply h.1
    intro y
    obtain ⟨y, rfl⟩ := f.surjective y
    exact hx y
  · rw [map_zero]
    apply h.2
    intro x
    obtain ⟨x, rfl⟩ := f.surjective x
    exact hy x

private theorem polar_nondegenerate_toQuadraticMap {B : LinearMap.BilinForm K V}
    (hS : B.IsSymm) (hB : B.Nondegenerate) (h2 : (2 : K) ≠ 0) : B.toQuadraticMap.polarBilin.Nondegenerate := by
  have hp (x y : V) : B.toQuadraticMap.polarBilin x y = 2 * B x y := by
    rw [LinearMap.BilinMap.polarBilin_toQuadraticMap, LinearMap.add_apply, LinearMap.add_apply,
      LinearMap.flip_apply, hS.eq y x, two_mul]
  exact ⟨fun x hx => hB.1 x fun y => (mul_eq_zero.mp ((hp x y).symm.trans (hx y))).resolve_left h2,
    fun y hy => hB.2 y fun x => (mul_eq_zero.mp ((hp x y).symm.trans (hy x))).resolve_left h2⟩

end Nondegeneracy

section Global

variable {K : Type u} [Field K] [NumberField K] {V : Type u} [AddCommGroup V] [Module K V]

private theorem numberField_isometry_of_local {W : Type u} [AddCommGroup W] [Module K W] (n : ℕ)
    (bV : Module.Basis (Fin n) K V) (bW : Module.Basis (Fin n) K W)
    (q : QuadraticForm K V) (r : QuadraticForm K W)
    (hq : q.polarBilin.Nondegenerate) (hr : r.polarBilin.Nondegenerate)
    (hloc : ∀ v : Global.Place K, (q.baseChange (Global.placeCompletion K v)).Equivalent
      (r.baseChange (Global.placeCompletion K v))) : q.Equivalent r := by
  let : Invertible (2 : K) := invertibleOfNonzero (two_ne_zero : (2 : K) ≠ 0)
  let q' : QuadraticForm K (Fin n → K) := q.comp bV.equivFun.symm.toLinearMap
  let r' : QuadraticForm K (Fin n → K) := r.comp bW.equivFun.symm.toLinearMap
  let i : q'.IsometryEquiv q := ⟨bV.equivFun.symm, fun _ => rfl⟩
  let j : r'.IsometryEquiv r := ⟨bW.equivFun.symm, fun _ => rfl⟩
  have hq' : q'.polarBilin.Nondegenerate := polar_nondegenerate_comp hq bV.equivFun.symm
  have hr' : r'.polarBilin.Nondegenerate := polar_nondegenerate_comp hr bW.equivFun.symm
  have hlocal (v : Global.Place K) : (q'.baseChange (Global.placeCompletion K v)).Equivalent
      (r'.baseChange (Global.placeCompletion K v)) := by
    let R := Global.placeCompletion K v
    obtain ⟨e⟩ := hloc v
    exact ⟨(extendIsometry (R := R) i).trans (e.trans (extendIsometry (R := R) j).symm)⟩
  obtain ⟨e⟩ := Langlands.numberFieldQuadraticIsometry K n q' r' hq' hr' hlocal
  exact ⟨i.symm.trans (e.trans j)⟩

omit [NumberField K] in
private theorem toQuadraticMap_baseChange {R : Type u} [CommRing R] [Algebra K R] [Invertible (2 : K)]
    (B : LinearMap.BilinForm K V) : QuadraticForm.baseChange R B.toQuadraticMap = (LinearMap.BilinForm.baseChange R B).toQuadraticMap := by
  apply baseChange_ext
  intro x
  rw [QuadraticForm.baseChange_tmul]
  change B x x • ((1 : R) * 1) = LinearMap.BilinForm.baseChange R B (1 ⊗ₜ[K] x) (1 ⊗ₜ[K] x)
  rw [LinearMap.BilinForm.baseChange_tmul]

omit [NumberField K] in
private theorem toMatrix_baseChange {R : Type u} [CommRing R] [Algebra K R]
    (B : LinearMap.BilinForm K V) (b : Module.Basis (Fin 6) K V) :
    LinearMap.BilinForm.toMatrix (b.baseChange R) (LinearMap.BilinForm.baseChange R B) =
      (LinearMap.BilinForm.toMatrix b B).map (algebraMap K R) := by
  ext i j
  simp [LinearMap.BilinForm.toMatrix_apply, Module.Basis.baseChange_apply,
    LinearMap.BilinForm.baseChange_tmul, Algebra.smul_def]

/-- A rank-six symmetric form over a number field is hyperbolic if its determinant
  is negative a square and its local scalar extensions all have an isotropic plane. -/
theorem numberField_rankSix_hyperbolic (B : LinearMap.BilinForm K V) (b : Module.Basis (Fin 6) K V)
    (hS : B.IsSymm) (hB : B.Nondegenerate) (s : K) (hd : (LinearMap.BilinForm.toMatrix b B).det = -(s ^ 2))
    (hl : ∀ v : Global.Place K, let R := Global.placeCompletion K v
      let C := LinearMap.BilinForm.baseChange R B
      ∃ x y : R ⊗[K] V, LinearIndependent R ![x, y] ∧ C x x = 0 ∧ C x y = 0 ∧ C y y = 0) :
    (threeHyperbolicPlanes K).Equivalent B.toQuadraticMap := by
  let : Invertible (2 : K) := invertibleOfNonzero (two_ne_zero : (2 : K) ≠ 0)
  let b₂ := Module.Basis.finTwoProd K
  let e : Fin 2 ⊕ (Fin 2 ⊕ Fin 2) ≃ Fin 6 :=
    (Equiv.sumCongr (Equiv.refl _) finSumFinEquiv).trans finSumFinEquiv
  let c := (b₂.prod (b₂.prod b₂)).reindex e
  have h₂ := polar_nondegenerate_hyperbolicPlane K
  have ht : (threeHyperbolicPlanes K).polarBilin.Nondegenerate := polar_nondegenerate_prod h₂ (polar_nondegenerate_prod h₂ h₂)
  apply numberField_isometry_of_local 6 c b (threeHyperbolicPlanes K) B.toQuadraticMap ht
    (polar_nondegenerate_toQuadraticMap hS hB two_ne_zero)
  have hlocal (R : Type u) [Field R] [Algebra K R]
      (h : let C := LinearMap.BilinForm.baseChange R B
        ∃ x y : R ⊗[K] V, LinearIndependent R ![x, y] ∧ C x x = 0 ∧ C x y = 0 ∧ C y y = 0) :
      ((threeHyperbolicPlanes K).baseChange R).Equivalent (QuadraticForm.baseChange R B.toQuadraticMap) := by
    let : CharZero R := charZero_of_injective_algebraMap (algebraMap K R).injective
    let : Invertible (2 : R) := invertibleOfNonzero (two_ne_zero : (2 : R) ≠ 0)
    let C := LinearMap.BilinForm.baseChange R B
    let : FiniteDimensional R (R ⊗[K] V) := Module.Finite.of_basis (b.baseChange R)
    have hC : C.IsSymm := by
      apply (LinearMap.BilinForm.isSymm_toMatrix_iff_isSymm (b.baseChange R)).mp
      change (LinearMap.BilinForm.toMatrix (b.baseChange R) C)ᵀ = _
      rw [toMatrix_baseChange, ← Matrix.transpose_map]
      exact congrArg (fun M : Matrix (Fin 6) (Fin 6) K => M.map (algebraMap K R))
        ((B.isSymm_toMatrix_iff_isSymm b).mpr hS).eq
    have hm : (LinearMap.BilinForm.toMatrix (b.baseChange R) C).det =
        algebraMap K R (LinearMap.BilinForm.toMatrix b B).det := by
      rw [toMatrix_baseChange]
      exact ((algebraMap K R).map_det (LinearMap.BilinForm.toMatrix b B)).symm
    have hdet : (LinearMap.BilinForm.toMatrix (b.baseChange R) C).det = -((algebraMap K R s) ^ 2) := by
      rw [hm, hd, map_neg, map_pow]
    have hnd : C.Nondegenerate := (LinearMap.BilinForm.nondegenerate_iff_det_ne_zero (b.baseChange R)).mpr (by
      rw [hm]
      simpa only [map_zero] using (algebraMap K R).injective.ne
        ((LinearMap.BilinForm.nondegenerate_iff_det_ne_zero b).mp hB))
    obtain ⟨x, y, hxy, hxx, hxy₀, hyy⟩ := h
    obtain ⟨i⟩ := rankSix_hyperbolic hC hnd (b.baseChange R) (algebraMap K R s) hdet x y hxy hxx hxy₀ hyy
    rw [toQuadraticMap_baseChange]
    exact ⟨(extendThreeHyperbolicPlanes K R).trans i⟩
  intro v
  rcases v with v | v
  · exact hlocal v.Completion (hl (.inl v))
  · exact hlocal (Global.FiniteCompletion K v) (hl (.inr v))

end Global

/-- A rank-six symmetric form of negative-square determinant over a number field
  is hyperbolic if it has an isotropic plane over every completion. -/
def NumberFieldRankSixHyperbolicityStatement : Prop :=
  ∀ (K : Type u) [Field K] [NumberField K] (V : Type u) [AddCommGroup V] [Module K V]
    (B : LinearMap.BilinForm K V) (b : Module.Basis (Fin 6) K V),
    B.IsSymm → B.Nondegenerate →
    (∃ s : K, (LinearMap.BilinForm.toMatrix b B).det = -(s ^ 2)) →
    (∀ v : Global.Place K, let R := Global.placeCompletion K v
      let C := LinearMap.BilinForm.baseChange R B
      ∃ x y : R ⊗[K] V, LinearIndependent R ![x, y] ∧ C x x = 0 ∧ C x y = 0 ∧ C y y = 0) →
    (threeHyperbolicPlanes K).Equivalent B.toQuadraticMap

theorem numberFieldRankSixHyperbolicity : NumberFieldRankSixHyperbolicityStatement.{u} := by
  intro K _ _ V _ _ B b hS hB ⟨s, hd⟩ hl
  exact numberField_rankSix_hyperbolic B b hS hB s hd hl

end Langlands.SymmetricBilinear
