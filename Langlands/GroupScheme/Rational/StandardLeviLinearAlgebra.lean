import Mathlib.Basic.Real.Basic
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.LinearAlgebra.PerfectPairing.Basic
import Mathlib.LinearAlgebra.Projection

/-! # Linear algebra for standard Levi decompositions -/

noncomputable section

namespace Langlands.LinearAlgebra.StandardLevi

section Pairing

variable {E F : Type*} [AddCommGroup E] [Module ℝ E]
  [AddCommGroup F] [Module ℝ F]
  (p : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) [p.IsPerfPair]

/-- Right annihilator for a bilinear pairing. -/
def rightAnn (P : Submodule ℝ E) : Submodule ℝ F :=
  P.dualAnnihilator.comap p.flip

/-- Left annihilator for a bilinear pairing. -/
def leftAnn (Q : Submodule ℝ F) : Submodule ℝ E :=
  Q.dualAnnihilator.comap p

omit [p.IsPerfPair] in
@[simp] theorem mem_rightAnn (P : Submodule ℝ E) (v : F) :
    v ∈ rightAnn p P ↔ ∀ x ∈ P, p x v = 0 := by
  simp [rightAnn]

omit [p.IsPerfPair] in
@[simp] theorem mem_leftAnn (Q : Submodule ℝ F) (x : E) :
    x ∈ leftAnn p Q ↔ ∀ v ∈ Q, p x v = 0 := by
  simp [leftAnn, Submodule.mem_dualAnnihilator]

/-- Perfect pairings recover a subspace by double annihilation. -/
theorem rightAnn_leftAnn (Q : Submodule ℝ F) : rightAnn p (leftAnn p Q) = Q := by
  ext v
  constructor
  · intro hv
    rw [← Subspace.dualAnnihilator_dualCoannihilator_eq (W := Q),
      Submodule.mem_dualCoannihilator]
    intro φ hφ
    obtain ⟨x, rfl⟩ := (LinearMap.IsPerfPair.bijective_left p).surjective φ
    exact (mem_rightAnn p _ _).mp hv x hφ
  · intro hv
    exact (mem_rightAnn p _ _).mpr fun x hx => (mem_leftAnn p _ _).mp hx v hv

/-- The symmetric double-annihilator identity. -/
theorem leftAnn_rightAnn (P : Submodule ℝ E) : leftAnn p (rightAnn p P) = P :=
  rightAnn_leftAnn p.flip P

/-- Annihilators transfer complements across a perfect pairing. -/
theorem rightAnn_isCompl {A P : Submodule ℝ E} (h : IsCompl A P) :
    IsCompl (rightAnn p A) (rightAnn p P) := by
  have hc := Submodule.isCompl_map p.flip.toPerfPair.symm
    (Subspace.isCompl_dualAnnihilator h)
  have he : (p.flip.toPerfPair : F →ₗ[ℝ] Module.Dual ℝ E) = p.flip := by
    ext v x
    rfl
  simpa only [Submodule.map_equiv_eq_comap_symm, LinearEquiv.symm_symm, rightAnn, he] using hc

/-- Complementary mutual annihilators carry a perfect restricted pairing. -/
theorem restricted_perfect [FiniteDimensional ℝ E]
    {P : Submodule ℝ E} {Q : Submodule ℝ F}
    (hE : IsCompl (leftAnn p Q) P)
    (hF : IsCompl (rightAnn p P) Q) :
    (p.domRestrict₁₂ (leftAnn p Q) (rightAnn p P)).IsPerfPair := by
  apply LinearMap.IsPerfPair.of_injective
  · apply LinearMap.ker_eq_bot.mp
    apply eq_bot_iff.mpr
    intro x hx
    have hz : (x : E) ∈ leftAnn p (rightAnn p P) := by
      rw [mem_leftAnn]
      intro v hv
      exact LinearMap.congr_fun (LinearMap.mem_ker.mp hx) ⟨v, hv⟩
    rw [leftAnn_rightAnn] at hz
    apply Subtype.ext
    exact Submodule.disjoint_def.mp hE.disjoint x x.2 hz
  · apply LinearMap.ker_eq_bot.mp
    apply eq_bot_iff.mpr
    intro v hv
    have hz : (v : F) ∈ rightAnn p (leftAnn p Q) := by
      rw [mem_rightAnn]
      intro x hx
      exact LinearMap.congr_fun (LinearMap.mem_ker.mp hv) ⟨x, hx⟩
    rw [rightAnn_leftAnn] at hz
    apply Subtype.ext
    exact Submodule.disjoint_def.mp hF.disjoint v v.2 hz

end Pairing

section Projection

variable {E I : Type*} [AddCommGroup E] [Module ℝ E]

/-- A complement restricts to every larger subspace containing it. -/
theorem nested_complement {A B Q : Submodule ℝ E} (h : IsCompl B Q) (hBA : B ≤ A) :
    Disjoint B (A ⊓ Q) ∧ B ⊔ (A ⊓ Q) = A := by
  refine ⟨h.disjoint.mono_right inf_le_right, ?_⟩
  rw [inf_comm A Q, ← sup_inf_assoc_of_le Q hBA, h.sup_eq_top, top_inf_eq]

/-- Projecting generators outside the smaller index set spans the Levi piece. -/
theorem projected_span (f : I → E) {J K : Set I} (hJK : J ⊆ K)
    {A : Submodule ℝ E} (h : IsCompl A (Submodule.span ℝ (f '' J))) :
    A ⊓ Submodule.span ℝ (f '' K) =
      Submodule.span ℝ {y | y ∈ A ∧ ∃ a ∈ K \ J,
        f a - y ∈ Submodule.span ℝ (f '' J)} := by
  classical
  let P := Submodule.span ℝ (f '' J)
  let Q := Submodule.span ℝ (f '' K)
  let S : Set E := {y | y ∈ A ∧ ∃ a ∈ K \ J, f a - y ∈ P}
  let π := A.projection P h
  have hPQ : P ≤ Q := Submodule.span_mono (Set.image_mono hJK)
  have hπ (a : I) (ha : a ∈ K \ J) : π (f a) ∈ S := by
    exact ⟨Submodule.projection_apply_mem h _, a, ha, Submodule.sub_projection_mem h _⟩
  apply le_antisymm
  · have hQ : Q ≤ (Submodule.span ℝ S).comap π := by
      apply Submodule.span_le.mpr
      rintro _ ⟨a, ha, rfl⟩
      change π (f a) ∈ Submodule.span ℝ S
      by_cases haJ : a ∈ J
      · have hz := Submodule.projection_apply_of_mem_right h
          (Submodule.subset_span (Set.mem_image_of_mem f haJ))
        change π (f a) = 0 at hz
        rw [hz]
        exact Submodule.zero_mem _
      · exact Submodule.subset_span (hπ a ⟨ha, haJ⟩)
    intro y hy
    have hy' := hQ hy.2
    change π y ∈ Submodule.span ℝ S at hy'
    rwa [show π y = y from Submodule.projection_apply_of_mem_left h hy.1] at hy'
  · apply Submodule.span_le.mpr
    rintro y ⟨hy, a, ha, hd⟩
    refine ⟨hy, ?_⟩
    have haQ : f a ∈ Q := Submodule.subset_span (Set.mem_image_of_mem f ha.1)
    have hdQ : f a - y ∈ Q := hPQ hd
    have := Q.sub_mem haQ hdQ
    change y ∈ Q
    simpa only [sub_sub_cancel] using this

end Projection

end Langlands.LinearAlgebra.StandardLevi
