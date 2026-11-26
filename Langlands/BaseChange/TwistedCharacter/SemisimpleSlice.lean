import Langlands.BaseChange.FiniteAlgebraAnalyticNorm
import Langlands.BaseChange.TwistedTriangularDifferential
import Mathlib.Topology.OpenPartialHomeomorph.Constructions
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
import Mathlib.Analysis.Normed.Ring.Units
import Mathlib.LinearAlgebra.Semisimple

/-! # Local conjugation slice for a semisimple algebra automorphism -/

noncomputable section

namespace Langlands.BaseChange

open ContinuousLinearMap Module
open scoped RightActions Topology

/-- The fixed subalgebra of the adjoint action at the slice center. -/
def adjointFixedAlgebra {F R : Type*} [CommSemiring F] [Semiring R] [Algebra F R]
    (α : R ≃ₐ[F] R) : Subalgebra F R :=
  α.toAlgHom.equalizer (AlgHom.id F R)

/-- In additive coordinates at the two identity elements, the conjugation slice
with the central element translated to the identity on the right. -/
def semisimpleSliceMap {F R : Type*} [CommRing F] [Ring R] [Algebra F R]
    (α : R ≃ₐ[F] R) (q : Submodule F R)
    (z : q × adjointFixedAlgebra α) : R :=
  (1 + z.1.val) * (1 + z.2.val) * Ring.inverse (α (1 + z.1.val))

section Normed

variable {F R : Type*} [NontriviallyNormedField F] [NormedRing R] [NormedAlgebra F R]
  [CompleteSpace F] [CompleteSpace R] [FiniteDimensional F R]

/-- Differential of the normalized slice at the two identity elements. -/
def semisimpleSliceDifferential (α : R ≃ₐ[F] R) (q : Submodule F R) :
    q × adjointFixedAlgebra α →L[F] R :=
  let p := q.subtype.toContinuousLinearMap.comp (fst F q (adjointFixedAlgebra α))
  let r := (adjointFixedAlgebra α).val.toLinearMap.toContinuousLinearMap.comp
    (snd F q (adjointFixedAlgebra α))
  p + r - α.toLinearMap.toContinuousLinearMap.comp p

private theorem hasStrictFDerivAt_semisimpleSliceMap (α : R ≃ₐ[F] R) (q : Submodule F R) :
    HasStrictFDerivAt (semisimpleSliceMap α q) (semisimpleSliceDifferential α q) 0 := by
  let A := q × adjointFixedAlgebra α
  let p : A →L[F] R := q.subtype.toContinuousLinearMap.comp (fst F q (adjointFixedAlgebra α))
  let r : A →L[F] R := (adjointFixedAlgebra α).val.toLinearMap.toContinuousLinearMap.comp
    (snd F q (adjointFixedAlgebra α))
  let s := α.toLinearMap.toContinuousLinearMap.comp p
  have hp : HasStrictFDerivAt (fun z : A => 1 + p z) p 0 :=
    p.hasStrictFDerivAt.const_add 1
  have hr : HasStrictFDerivAt (fun z : A => 1 + r z) r 0 :=
    r.hasStrictFDerivAt.const_add 1
  have hs : HasStrictFDerivAt (fun z : A => α (1 + p z)) s 0 :=
    α.toLinearMap.toContinuousLinearMap.hasStrictFDerivAt.comp 0 hp
  have hα0 : α (1 + p 0) = 1 := by simp
  have hi : HasStrictFDerivAt (Ring.inverse : R → R) (-ContinuousLinearMap.id F R)
      (α (1 + p 0)) := by
    rw [hα0]
    have heq : mulLeftRight F R (1 : R) 1 = ContinuousLinearMap.id F R := by
      ext x
      simp [mulLeftRight_apply]
    simpa only [Units.val_one, inv_one, heq] using
      hasStrictFDerivAt_ringInverse (𝕜 := F) (1 : Rˣ)
  have h := (hp.mul' hr).mul' (hi.comp 0 hs)
  change HasStrictFDerivAt (semisimpleSliceMap α q) _ 0 at h
  have hder : ((1 + p 0) * (1 + r 0)) •> (-ContinuousLinearMap.id F R).comp s +
      ((1 + p 0) •> r + p <• (1 + r 0)) <• Ring.inverse (α (1 + p 0)) =
      p + r - s := by
    rw [map_zero p, map_zero r, add_zero, map_one, Ring.inverse_one]
    apply ContinuousLinearMap.ext
    intro z
    simp [sub_eq_add_neg]
    abel
  simp only [Pi.mul_apply, hder] at h
  exact h

omit [CompleteSpace R] in
private theorem bijective_semisimpleSliceDifferential (α : R ≃ₐ[F] R)
    (hα : Module.End.IsSemisimple α.toLinearMap) :
    ∃ q : Submodule F R, IsCompl (adjointFixedAlgebra α).toSubmodule q ∧
      q = LinearMap.range (LinearMap.id - α.toLinearMap) ∧ Function.Bijective (semisimpleSliceDifferential α q) := by
  let m := (adjointFixedAlgebra α).toSubmodule
  have hm : m ∈ Module.End.invtSubmodule α.toLinearMap := by
    rw [Module.End.mem_invtSubmodule]
    intro x hx
    change α x = x at hx
    change α x ∈ m
    rwa [hx]
  obtain ⟨q, hq, hmq⟩ := Module.End.isSemisimple_iff.mp hα m hm
  have hq' : ∀ x ∈ q, α.toLinearMap x ∈ q :=
    (Module.End.mem_invtSubmodule_iff_forall_mem_of_mem α.toLinearMap).mp hq
  let a : Module.End F q := LinearMap.id - α.toLinearMap.restrict hq'
  have ha : Function.Injective a := by
    apply LinearMap.ker_eq_bot.mp
    rw [Submodule.eq_bot_iff]
    intro x hx
    have hxa : x.val - α x.val = 0 := congrArg Subtype.val (LinearMap.mem_ker.mp hx)
    have hxm : x.val ∈ m := (sub_eq_zero.mp hxa).symm
    exact Subtype.ext (Submodule.disjoint_def.mp hmq.disjoint x.val hxm x.prop)
  let e : q ≃ₗ[F] q := a.linearEquivOfInjective ha rfl
  have hqr : q = LinearMap.range (LinearMap.id - α.toLinearMap) := by
    apply le_antisymm
    · intro x hx
      obtain ⟨y, hy⟩ := e.surjective ⟨x, hx⟩
      exact ⟨y.val, congrArg Subtype.val hy⟩
    · rintro x ⟨y, rfl⟩
      obtain ⟨⟨y₁, y₂⟩, hy⟩ := (m.prodEquivOfIsCompl q hmq).surjective y
      change (y₁ : R) + (y₂ : R) = y at hy
      have hy₁ : (LinearMap.id - α.toLinearMap : Module.End F R) y₁.val = 0 :=
        sub_eq_zero.mpr (show α y₁.val = y₁.val from y₁.prop).symm
      rw [← hy, map_add, hy₁, zero_add]
      exact (a y₂).prop
  let E : (q × adjointFixedAlgebra α) ≃ₗ[F] R :=
    (e.prodCongr (LinearEquiv.refl F m)).trans (q.prodEquivOfIsCompl m hmq.symm)
  have hE (z : q × adjointFixedAlgebra α) : E z = semisimpleSliceDifferential α q z := by
    rw [show E z = (z.1.val - α z.1.val) + z.2.val from rfl]
    simp [semisimpleSliceDifferential]
    abel
  exact ⟨q, hmq, hqr, (funext hE) ▸ E.bijective⟩

/-- A semisimple adjoint action has a local conjugation chart with a transverse
coordinate in its fixed subalgebra and a complementary conjugating coordinate. -/
theorem exists_semisimpleSliceChart (α : R ≃ₐ[F] R) (hα : Module.End.IsSemisimple α.toLinearMap) :
    ∃ (q : Submodule F R) (e : OpenPartialHomeomorph (q × adjointFixedAlgebra α) R),
      IsCompl (adjointFixedAlgebra α).toSubmodule q ∧
      q = LinearMap.range (LinearMap.id - α.toLinearMap) ∧
      0 ∈ e.source ∧ 1 ∈ e.target ∧ ⇑e = semisimpleSliceMap α q ∧
      ∀ z ∈ e.source, IsUnit (1 + z.1.val) ∧ IsUnit (1 + z.2.val) := by
  obtain ⟨q, hq, hqr, hbij⟩ := bijective_semisimpleSliceDifferential α hα
  let d : (q × adjointFixedAlgebra α) ≃L[F] R :=
    (LinearEquiv.ofBijective (semisimpleSliceDifferential α q).toLinearMap hbij).toContinuousLinearEquiv
  have hd : HasStrictFDerivAt (semisimpleSliceMap α q) (d : _ →L[F] R) 0 :=
    hasStrictFDerivAt_semisimpleSliceMap α q
  have : CompleteSpace (q × adjointFixedAlgebra α) := FiniteDimensional.complete F _
  let e₀ := hd.toOpenPartialHomeomorph (semisimpleSliceMap α q)
  let U : Set (q × adjointFixedAlgebra α) := {z | IsUnit (1 + z.1.val) ∧ IsUnit (1 + z.2.val)}
  have hU : IsOpen U :=
    (Units.isOpen.preimage <| continuous_const.add (continuous_subtype_val.comp continuous_fst)).inter
      (Units.isOpen.preimage <| continuous_const.add (continuous_subtype_val.comp continuous_snd))
  let e := e₀.restrOpen U hU
  have h0 : (0 : q × adjointFixedAlgebra α) ∈ e.source :=
    ⟨hd.mem_toOpenPartialHomeomorph_source, by simp [U]⟩
  refine ⟨q, e, hq, hqr, h0, ?_, rfl, fun _ hz => hz.2⟩
  have htarget := e.map_source h0
  change semisimpleSliceMap α q 0 ∈ e.target at htarget
  simpa [semisimpleSliceMap, Ring.inverse_one] using htarget

end Normed

section Matrices

universe u v

variable {F : Type u} [Field F] {E : Type v} [CommRing E] [Algebra F E] {n : ℕ}

local notation "Mat" => Matrix (Fin n) (Fin n) E
local notation "G" => GeneralLinear n E

/-- The algebra automorphism whose underlying linear equivalence is the twisted adjoint. -/
def twistedAdjointAlgEquiv (σ : E ≃ₐ[F] E) (δ : G) : Mat ≃ₐ[F] Mat :=
  AlgEquiv.ofLinearEquiv (twistedMatrixConj σ δ) (by simp)
    (by intro x y; simp [map_mul, mul_assoc])

/-- Units of the fixed locus are precisely the twisted centralizing matrices. -/
theorem mem_adjointFixedAlgebra_matrix_units (σ : E ≃ₐ[F] E) (δ m : G) :
    m.val ∈ adjointFixedAlgebra (twistedAdjointAlgEquiv σ δ) ↔
      m * δ = δ * entrywiseAut σ n m := by
  change (δ * entrywiseAut σ n m * δ⁻¹).val = m.val ↔ _
  exact Units.val_inj.trans (eq_comm.trans eq_mul_inv_iff_mul_eq)

/-- The normalized slice on units is actual twisted conjugation, translated by `δ⁻¹`. -/
theorem semisimpleSliceMap_matrix_units
    (σ : E ≃ₐ[F] E) (δ : G) (q : Submodule F Mat)
    (z : q × adjointFixedAlgebra (twistedAdjointAlgEquiv σ δ)) (k m : G)
    (hk : k.val = 1 + z.1.val) (hm : m.val = 1 + z.2.val) :
    semisimpleSliceMap (twistedAdjointAlgEquiv σ δ) q z * δ.val =
      (k * m * δ * (entrywiseAut σ n k)⁻¹).val := by
  rw [semisimpleSliceMap, ← hk, ← hm]
  let a : G := δ * entrywiseAut σ n k * δ⁻¹
  change k.val * m.val * Ring.inverse a.val * δ.val = _
  rw [Ring.inverse_unit]
  change (k * m * a⁻¹ * δ).val = _
  simp [a, mul_assoc]

end Matrices

/-- The semisimple conjugation chart in the matrix coordinates of a finite coefficient
algebra with its module topology. -/
def TwistedSemisimpleSliceChartStatement.{u, v} : Prop :=
  ∀ (F : Type u) [NontriviallyNormedField F] [CompleteSpace F]
    (E : Type v) [CommRing E] [Algebra F E] [Module.Finite F E]
    [TopologicalSpace E] [IsModuleTopology F E] (n : ℕ)
    (σ : E ≃ₐ[F] E) (δ : GeneralLinear n E),
    let M := Matrix (Fin n) (Fin n) E
    let S : Subalgebra F M := adjointFixedAlgebra (twistedAdjointAlgEquiv σ δ)
    let T : Module.End F M := (twistedMatrixConj σ δ).toLinearMap
    Module.End.IsSemisimple T →
    ∃ (q : Submodule F M) (e : OpenPartialHomeomorph (q × S) M),
      IsCompl S.toSubmodule q ∧
      q = LinearMap.range ((LinearMap.id : M →ₗ[F] M) - T) ∧
      0 ∈ e.source ∧ δ.val ∈ e.target ∧ (∀ w ∈ e.target, IsUnit w) ∧
      ∀ z ∈ e.source, ∃ k m : GeneralLinear n E,
        k.val = 1 + z.1.val ∧ m.val = 1 + z.2.val ∧
        e z = (k * m * δ * (entrywiseAut σ n k)⁻¹).val

theorem twistedSemisimpleSliceChart.{u, v} : TwistedSemisimpleSliceChartStatement.{u, v} := by
  intro F _ _ E _ _ _ _ _ n σ δ M S T hss
  let α := twistedAdjointAlgEquiv σ δ
  let : IsModuleTopology F M := inferInstanceAs (IsModuleTopology F (Fin n → Fin n → E))
  let : NormedRing M := finiteAlgebraNormedRing F M
  let : NormedAlgebra F M := finiteAlgebraNormedAlgebra F M
  let : CompleteSpace M := FiniteDimensional.complete F M
  obtain ⟨q, e₀, hq, hrange, h0, _, he₀, hunit⟩ := exists_semisimpleSliceChart α hss
  let tr := (δ.mulRightLinearEquiv F).toContinuousLinearEquiv.toHomeomorph
  let e := e₀.transHomeomorph tr
  have he (z : q × adjointFixedAlgebra α) : e z = semisimpleSliceMap α q z * δ.val := by
    change e₀ z * δ.val = _
    rw [congrFun he₀ z]
  have hδ : δ.val ∈ e.target := by
    have hmem := e.map_source h0
    simpa [he, semisimpleSliceMap, Ring.inverse_one] using hmem
  have hformula (z : q × adjointFixedAlgebra α) (hz : z ∈ e.source) :
      ∃ k m : GeneralLinear n E, k.val = 1 + z.1.val ∧ m.val = 1 + z.2.val ∧
        e z = (k * m * δ * (entrywiseAut σ n k)⁻¹).val := by
    obtain ⟨⟨k, hk⟩, ⟨m, hm⟩⟩ := hunit z hz
    exact ⟨k, m, hk, hm, (he z).trans (semisimpleSliceMap_matrix_units σ δ q z k m hk hm)⟩
  refine ⟨q, e, hq, hrange, h0, hδ, ?_, hformula⟩
  intro w hw
  obtain ⟨k, m, _, _, hw'⟩ := hformula (e.symm w) (e.map_target hw)
  rw [e.right_inv hw] at hw'
  rw [hw']
  exact Units.isUnit _

end Langlands.BaseChange
