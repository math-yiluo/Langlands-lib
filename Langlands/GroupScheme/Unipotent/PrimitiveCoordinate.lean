import Langlands.GroupScheme.Unipotent.HopfFixed
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.RingTheory.Bialgebra.Primitive

/-! # Nonzero primitive coordinates in unipotent bialgebras -/

noncomputable section

open TensorProduct Coalgebra Module

namespace Langlands.GroupScheme.Unipotent

open AffineLinearEmbedding Chevalley

variable {K : Type*} [Field K] {B : Type*} [Ring B] [Bialgebra K B]

/-- The counit evaluates a right translate by evaluating its functional. -/
theorem counit_rightAct (g : Module.Dual K B) (b : B) :
    counit (R := K) (rightAct g b) = g b := by
  rw [← apply_leftAct, leftAct_counit]

/-- Right translation preserves the line of constant functions. -/
theorem rightAct_mem_constants (g : Module.Dual K B) {b : B}
    (hb : b ∈ K ∙ (1 : B)) : rightAct g b ∈ K ∙ (1 : B) := by
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hb
  rw [map_smul, rightAct_one, smul_smul]
  exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)

/-- Left translation by a functional vanishing on `1` kills constant functions. -/
theorem leftAct_constants_eq_zero (θ : Module.Dual K B) (hθ : θ 1 = 0)
    {b : B} (hb : b ∈ K ∙ (1 : B)) : leftAct θ b = 0 := by
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hb
  rw [map_smul, leftAct_one, hθ, zero_smul, smul_zero]

/-- If a unipotent bialgebra has a nonconstant element, it has a nonzero primitive
element. No perfectness, smoothness or finite-type hypothesis is needed. -/
theorem exists_nonzero_primitive_of_oneMemStable (hB : OneMemStable K B)
    (hconst : ∃ a : B, a ∉ K ∙ (1 : B)) :
    ∃ b : B, b ≠ 0 ∧ Bialgebra.IsPrimitiveElem K b := by
  classical
  let C : Submodule K B := K ∙ (1 : B)
  let Q := B ⧸ C
  let T : Module.Dual K B → Q →ₗ[K] Q :=
    fun g => C.mapQ C (rightAct g) (fun _ hb => rightAct_mem_constants g hb)
  let I := {θ : Module.Dual K B // θ 1 = 0}
  let π : I → Q →ₗ[K] B := fun θ =>
    C.liftQ (leftAct θ.val) (fun _ hb =>
      LinearMap.mem_ker.2 (leftAct_constants_eq_zero θ.val θ.property hb))
  have hπ : ∀ i g m, π i (T g m) = rightAct g (π i m) := by
    intro i g m
    induction m using Submodule.Quotient.induction_on with
    | _ b =>
        change leftAct i.val (rightAct g b) = rightAct g (leftAct i.val b)
        exact (rightAct_leftAct g i.val b).symm
  have hsep : ∀ m : Q, (∀ i, π i m = 0) → m = 0 := by
    intro m hm
    rw [← Module.forall_dual_apply_eq_zero_iff K]
    intro ψ
    let θ : Module.Dual K B := ψ ∘ₗ C.mkQ
    have hθ : θ 1 = 0 := by
      change ψ (C.mkQ 1) = 0
      rw [show C.mkQ 1 = 0 from
        (Submodule.Quotient.mk_eq_zero C).2 (Submodule.mem_span_singleton_self _), map_zero]
    have h := hm ⟨θ, hθ⟩
    have heq : counit (R := K) (π ⟨θ, hθ⟩ m) = ψ m := by
      induction m using Submodule.Quotient.induction_on with
      | _ b =>
          change counit (R := K) (leftAct θ b) = ψ (C.mkQ b)
          exact counit_leftAct θ b
    rw [h, map_zero] at heq
    exact heq.symm
  obtain ⟨a, ha⟩ := hconst
  let V : Submodule K B := regularSpan ({a} : Finset B)
  let W : Submodule K Q := V.map C.mkQ
  have hW : ∀ g m, m ∈ W → T g m ∈ W := by
    rintro g _ ⟨b, hb, rfl⟩
    exact ⟨rightAct g b, rightAct_mem_regularSpan _ g hb, rfl⟩
  have hW0 : W ≠ ⊥ := by
    intro h
    have hm : C.mkQ a ∈ W :=
      ⟨a, subset_regularSpan {a} (Finset.mem_singleton_self a), rfl⟩
    rw [h, Submodule.mem_bot] at hm
    exact ha ((Submodule.Quotient.mk_eq_zero C).1 hm)
  obtain ⟨w, -, hw0, hw⟩ := exists_invariant hB T π hπ hsep W hW hW0
  obtain ⟨b, rfl⟩ := C.mkQ_surjective w
  let b₀ : B := b - counit (R := K) b • (1 : B)
  have hε : counit (R := K) b₀ = 0 := by
    simp [b₀, Bialgebra.counit_one]
  have hq : C.mkQ b₀ = C.mkQ b := by
    change C.mkQ (b - counit (R := K) b • (1 : B)) = C.mkQ b
    rw [map_sub, map_smul, show C.mkQ 1 = 0 from
      (Submodule.Quotient.mk_eq_zero C).2 (Submodule.mem_span_singleton_self _),
      smul_zero, sub_zero]
  have hb₀ : b₀ ≠ 0 := by
    intro h
    apply hw0
    rw [← hq, h, map_zero]
  have htrans : ∀ g : Module.Dual K B,
      rightAct g b₀ = g 1 • b₀ + g b₀ • (1 : B) := by
    intro g
    have hmem : rightAct g b₀ - g 1 • b₀ ∈ C := by
      apply (Submodule.Quotient.mk_eq_zero C).1
      change C.mkQ (rightAct g b₀ - g 1 • b₀) = 0
      rw [map_sub, map_smul]
      have h' : T g (C.mkQ b₀) = g 1 • C.mkQ b₀ := by
        rw [hq]
        exact hw g
      exact sub_eq_zero.2 h'
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 hmem
    have hc' : c = g b₀ := by
      have h := congrArg (counit (R := K)) hc
      rw [map_smul, Bialgebra.counit_one, smul_eq_mul, mul_one,
        map_sub, counit_rightAct, map_smul, smul_eq_mul] at h
      simpa only [hε, mul_zero, sub_zero] using h
    have hdiff : rightAct g b₀ - g 1 • b₀ = g b₀ • (1 : B) := by
      rw [← hc', hc]
    exact (sub_eq_iff_eq_add.1 hdiff).trans (add_comm _ _)
  refine ⟨b₀, hb₀, Bialgebra.isPrimitiveElem_iff_comul_eq_tmul_add_tmul.2 ?_⟩
  apply tensor_ext
  intro g
  rw [← rightAct_apply, htrans]
  simp only [map_add, LinearMap.lTensor_tmul, TensorProduct.rid_tmul]
  exact add_comm _ _

/-- A chosen nonzero primitive coordinate, together with its verified properties. -/
def nonzeroPrimitive (hB : OneMemStable K B)
    (hconst : ∃ a : B, a ∉ K ∙ (1 : B)) :
    {b : B // b ≠ 0 ∧ Bialgebra.IsPrimitiveElem K b} :=
  ⟨Classical.choose (exists_nonzero_primitive_of_oneMemStable hB hconst),
    Classical.choose_spec (exists_nonzero_primitive_of_oneMemStable hB hconst)⟩

end Langlands.GroupScheme.Unipotent
