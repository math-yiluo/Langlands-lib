import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff

/-! # Local coordinates on a zero fibre -/

noncomputable section

open Set Topology
open scoped ContDiff

namespace Langlands.AlgebraicGeometry.PointManifold

section Topological

variable {E A B : Type*} [TopologicalSpace E] [TopologicalSpace A]
    [TopologicalSpace B] [Zero B]
variable (F : E → B) (e : OpenPartialHomeomorph E (A × B))
    (hF : ∀ x ∈ e.source, (e x).2 = F x) (x₀ : {x : E // F x = 0})

private def zeroFibreInverse (y : A) : {x : E // F x = 0} := by
  classical
  exact if h : (y, 0) ∈ e.target then
    ⟨e.symm (y, 0), by
      rw [← hF _ (e.map_target h), e.right_inv h]⟩
  else x₀

private theorem zeroFibreInverse_val {y : A} (hy : (y, 0) ∈ e.target) :
    (zeroFibreInverse F e hF x₀ y).val = e.symm (y, 0) := by
  simp only [zeroFibreInverse, dite_eq_left hy]

/-- Restrict an ambient local homeomorphism whose second component is `F`
to the zero fibre of `F`. Values of the inverse outside its target use `x₀`. -/
def zeroFibreChart : OpenPartialHomeomorph {x : E // F x = 0} A where
  toFun x := (e x.val).1
  invFun := zeroFibreInverse F e hF x₀
  source := Subtype.val ⁻¹' e.source
  target := (fun y : A => (y, (0 : B))) ⁻¹' e.target
  map_source' := by
    intro x hx
    have h : e x.val = ((e x.val).1, 0) :=
      Prod.ext rfl ((hF _ hx).trans x.property)
    exact h ▸ e.map_source hx
  map_target' := by
    intro y hy
    change (zeroFibreInverse F e hF x₀ y).val ∈ e.source
    rw [zeroFibreInverse_val F e hF x₀ hy]
    exact e.map_target hy
  left_inv' := by
    intro x hx
    have h : e x.val = ((e x.val).1, 0) :=
      Prod.ext rfl ((hF _ hx).trans x.property)
    apply Subtype.ext
    rw [zeroFibreInverse_val F e hF x₀ (h ▸ e.map_source hx), ← h]
    exact e.left_inv hx
  right_inv' := by
    intro y hy
    rw [zeroFibreInverse_val F e hF x₀ hy, e.right_inv hy]
  continuousOn_toFun :=
    continuous_fst.continuousOn.comp
      (e.continuousOn.comp continuous_subtype_val.continuousOn (fun _ hx => hx))
      (fun _ _ => mem_univ _)
  continuousOn_invFun := by
    apply Topology.IsInducing.subtypeVal.continuousOn_iff.mpr
    exact (e.continuousOn_symm.comp
      (continuous_id.prodMk continuous_const).continuousOn (fun _ hy => hy)).congr
      (fun y hy => zeroFibreInverse_val F e hF x₀ hy)
  open_source := e.open_source.preimage continuous_subtype_val
  open_target := e.open_target.preimage (continuous_id.prodMk continuous_const)

@[simp] theorem zeroFibreChart_source :
    (zeroFibreChart F e hF x₀).source = Subtype.val ⁻¹' e.source := rfl

@[simp] theorem zeroFibreChart_target :
    (zeroFibreChart F e hF x₀).target =
      (fun y : A => (y, (0 : B))) ⁻¹' e.target := rfl

@[simp] theorem zeroFibreChart_apply (x : {x : E // F x = 0}) :
    zeroFibreChart F e hF x₀ x = (e x.val).1 := rfl

theorem zeroFibreChart_symm_val {y : A}
    (hy : y ∈ (zeroFibreChart F e hF x₀).target) :
    ((zeroFibreChart F e hF x₀).symm y).val = e.symm (y, 0) :=
  zeroFibreInverse_val F e hF x₀ hy

end Topological

section Smooth

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {E A B : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
    [NormedAddCommGroup A] [NormedSpace 𝕜 A]
    [NormedAddCommGroup B] [NormedSpace 𝕜 B]
    {n : WithTop ℕ∞}
variable (F : E → B) (e : OpenPartialHomeomorph E (A × B))
    (hF : ∀ x ∈ e.source, (e x).2 = F x) (x₀ : {x : E // F x = 0})

/-- Smoothness of the inverse inclusion of a zero-fibre chart follows from
invertibility of the ambient derivative at the points of the fibre in its source. -/
theorem zeroFibreChart_contDiffOn_symm_val
    (hsmooth : ∀ x ∈ e.source, F x = 0 → ContDiffAt 𝕜 n e x)
    (hderiv : ∀ x ∈ e.source, F x = 0 →
      ∃ D : E ≃L[𝕜] (A × B), HasFDerivAt e (D : E →L[𝕜] (A × B)) x) :
    ContDiffOn 𝕜 n (fun y => ((zeroFibreChart F e hF x₀).symm y).val)
      (zeroFibreChart F e hF x₀).target := by
  have hinv : ContDiffOn 𝕜 n (fun y : A => e.symm (y, 0))
      (zeroFibreChart F e hF x₀).target := by
    intro y hy
    have hx := e.map_target hy
    have hz : F (e.symm (y, 0)) = 0 := by
      rw [← hF _ hx, e.right_inv hy]
    obtain ⟨D, hD⟩ := hderiv _ hx hz
    exact ((e.contDiffAt_symm hy hD (hsmooth _ hx hz)).comp y
      (contDiffAt_id.prodMk contDiffAt_const)).contDiffWithinAt
  exact hinv.congr (fun y hy => zeroFibreChart_symm_val F e hF x₀ hy)

end Smooth

end Langlands.AlgebraicGeometry.PointManifold
