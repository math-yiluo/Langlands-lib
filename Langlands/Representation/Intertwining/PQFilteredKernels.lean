import Langlands.Representation.Intertwining.PQRegularity

/-! # Action kernels in finite representation filtrations -/

noncomputable section

open CategoryTheory

namespace Langlands.PQFilteredKernels

universe uH uB uV uC vC

variable {H : Type uH} [Group H] {B : Type uB} [CommGroup B]
  {C : Type uC} [Category.{vC} C] {F : C ⥤ Rep.{uV} ℂ H}
  {n : ℕ} (s : RepFunctorFiltration F n) (X : C) (φ : B →* H)

/-- The intersection of the group-algebra action kernels of the actual grades. -/
def gradedKernel : Ideal (MonoidAlgebra ℂ B) :=
  ⨅ i : Fin n, groupAlgebraKernel (((s.graded i).obj X).ρ) φ

private theorem map_action
    {V W : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    {ρ : Representation ℂ H V} {σ : Representation ℂ H W}
    (f : ρ.IntertwiningMap σ) (φ : B →* H) (c : MonoidAlgebra ℂ B) (x : V) :
    f (Representation.asAlgebraHom (ρ.comp φ) c x) =
      Representation.asAlgebraHom (σ.comp φ) c (f x) := by
  induction c using MonoidAlgebra.induction_linear with
  | zero => simp
  | add a b ha hb => simp only [map_add, LinearMap.add_apply, ha, hb]
  | single b z =>
    simp only [Representation.asAlgebraHom_single, LinearMap.smul_apply, map_smul]
    exact congrArg (fun y => z • y)
      (Representation.IntertwiningMap.isIntertwining ρ σ f (φ b) x)

/-- Killing the ambient representation kills every actual graded quotient. -/
theorem kernel_le_gradedKernel :
    groupAlgebraKernel (F.obj X).ρ φ ≤ gradedKernel s X φ := by
  intro c hc
  rw [gradedKernel, Submodule.mem_iInf]
  intro i
  apply (mem_groupAlgebraKernel_iff _ φ c).mpr
  apply LinearMap.ext
  intro y
  obtain ⟨x, rfl⟩ := (s.step i.castSucc).quotientProjection_surjective (s.step i.succ) X y
  let ι : (((s.step i.succ).representation X).ρ).IntertwiningMap (F.obj X).ρ :=
    ((s.step i.succ).inclusion.app X).hom
  have hx : Representation.asAlgebraHom
      ((((s.step i.succ).representation X).ρ).comp φ) c x = 0 := by
    apply Subtype.val_injective
    change ι (Representation.asAlgebraHom
      ((((s.step i.succ).representation X).ρ).comp φ) c x) = 0
    rw [map_action ι φ, (mem_groupAlgebraKernel_iff _ φ c).mp hc]
    rfl
  exact (map_action ((s.step i.castSucc).quotientProjection (s.step i.succ) X).hom
    φ c x).symm.trans (by rw [hx]; exact map_zero _)

/-- An element killing every grade lowers every step by one. -/
theorem action_mem_previous {c : MonoidAlgebra ℂ B} (hc : c ∈ gradedKernel s X φ)
    (i : Fin n) {x : F.obj X} (hx : x ∈ (s.step i.succ).obj X) :
    Representation.asAlgebraHom ((F.obj X).ρ.comp φ) c x ∈ (s.step i.castSucc).obj X := by
  let T := s.step i.succ
  let S := s.step i.castSucc
  let ι : (T.representation X).ρ.IntertwiningMap (F.obj X).ρ := (T.inclusion.app X).hom
  let q : (T.representation X).ρ.IntertwiningMap ((s.graded i).obj X).ρ :=
    (S.quotientProjection T X).hom
  have hci : c ∈ groupAlgebraKernel ((s.graded i).obj X).ρ φ :=
    (iInf_le (fun j : Fin n => groupAlgebraKernel ((s.graded j).obj X).ρ φ) i) hc
  have hq : q (Representation.asAlgebraHom ((T.representation X).ρ.comp φ) c ⟨x, hx⟩) = 0 := by
    rw [map_action q φ, (mem_groupAlgebraKernel_iff _ φ c).mp hci]
    rfl
  have hm : Representation.asAlgebraHom ((T.representation X).ρ.comp φ) c ⟨x, hx⟩ ∈
      (S.lowerInUpper T X).toSubmodule :=
    (Submodule.Quotient.mk_eq_zero _).mp hq
  have he := map_action ι φ c ⟨x, hx⟩
  change (Representation.asAlgebraHom ((T.representation X).ρ.comp φ) c ⟨x, hx⟩ :
    F.obj X) = Representation.asAlgebraHom ((F.obj X).ρ.comp φ) c x at he
  rw [← he]
  exact hm

/-- The length-th power of an element killing every grade kills the ambient
representation. No semisimplicity or finite-dimensionality is required. -/
theorem pow_mem_kernel {c : MonoidAlgebra ℂ B} (hc : c ∈ gradedKernel s X φ) :
    c ^ n ∈ groupAlgebraKernel (F.obj X).ρ φ := by
  let a := Representation.asAlgebraHom ((F.obj X).ρ.comp φ) c
  have hkill : ∀ j : Fin (n + 1), ∀ x ∈ (s.step j).obj X, (a ^ j.val) x = 0 := by
    apply Fin.induction
    · intro x hx
      rw [s.zero X] at hx
      have hx0 : x = 0 := (Submodule.mem_bot ℂ).mp hx
      rw [hx0, map_zero]
    · intro i hi x hx
      change (a ^ (i.val + 1)) x = 0
      rw [pow_succ, Module.End.mul_apply]
      exact hi (a x) (action_mem_previous s X φ hc i hx)
  apply (mem_groupAlgebraKernel_iff _ φ _).mpr
  rw [map_pow]
  apply LinearMap.ext
  intro x
  exact hkill (Fin.last n) x (s.top X ▸ Submodule.mem_top)

/-- Ambient and graded action kernels have the same radical. -/
theorem radical_kernel_eq :
    (groupAlgebraKernel (F.obj X).ρ φ).radical = (gradedKernel s X φ).radical := by
  apply le_antisymm
  · exact Ideal.radical_mono (kernel_le_gradedKernel s X φ)
  · apply Ideal.radical_le_radical_iff.mpr
    intro c hc
    exact ⟨n, pow_mem_kernel s X φ hc⟩

/-- Comaximality against any fixed ideal can be tested on the graded kernels. -/
theorem sup_kernel_eq_top_iff (I : Ideal (MonoidAlgebra ℂ B)) :
    I ⊔ groupAlgebraKernel (F.obj X).ρ φ = ⊤ ↔ I ⊔ gradedKernel s X φ = ⊤ := by
  constructor
  · intro h
    exact top_unique (h ▸ sup_le_sup_left (kernel_le_gradedKernel s X φ) I)
  · intro h
    apply Ideal.radical_eq_top.mp
    apply top_unique
    rw [← h]
    refine sup_le (le_sup_left.trans Ideal.le_radical) ?_
    have hj : gradedKernel s X φ ≤ (groupAlgebraKernel (F.obj X).ρ φ).radical := by
      intro c hc
      exact ⟨n, pow_mem_kernel s X φ hc⟩
    exact hj.trans (Ideal.radical_mono le_sup_right)

end Langlands.PQFilteredKernels
