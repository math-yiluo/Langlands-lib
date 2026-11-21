import Langlands.HarmonicAnalysis.SchwartzBruhatProduct
import Mathlib.Topology.Homeomorph.Lemmas

/-! # Pure tensor test functions span the Schwartz–Bruhat space on a finite product -/

noncomputable section

namespace Langlands.HarmonicAnalysis.SchwartzBruhat

open Filter Topology

universe u v w

variable {ι : Type u} [Fintype ι] {X : ι → Type v} [∀ i, TopologicalSpace (X i)]

/-- The external product of a finite family of Schwartz–Bruhat functions. -/
def piTensor (f : ∀ i, SchwartzBruhat (X i)) : SchwartzBruhat (∀ i, X i) :=
  ⟨fun x => ∏ i, f i (x i), by
    rw [IsLocallyConstant.iff_eventually_eq]
    intro x
    have h : ∀ᶠ y in 𝓝 x, ∀ i, f i (y i) = f i (x i) :=
      Filter.eventually_all.mpr fun i =>
        ((f i).locallyConstant.comp_continuous (continuous_apply i)).eventually_eq x
    filter_upwards [h] with y hy
    exact Finset.prod_congr rfl fun i _ => hy i, by
    apply IsCompact.of_isClosed_subset (isCompact_univ_pi fun i => (f i).hasCompactSupport)
      (isClosed_tsupport _)
    apply closure_minimal _ (isClosed_set_pi fun _ _ => isClosed_tsupport _)
    intro x hx i _
    exact subset_tsupport _ (fun hi => hx (Finset.prod_eq_zero (Finset.mem_univ i) hi))⟩

@[simp]
theorem piTensor_apply (f : ∀ i, SchwartzBruhat (X i)) (x : ∀ i, X i) :
    piTensor f x = ∏ i, f i (x i) := rfl

/-- The support of a pure tensor is the product of the component supports. -/
theorem support_piTensor (f : ∀ i, SchwartzBruhat (X i)) :
    Function.support (piTensor f) = Set.pi Set.univ (fun i => Function.support (f i)) := by
  ext x
  simp [Function.mem_support, Finset.prod_ne_zero_iff]

private def testPullback {Z : Type v} {W : Type w}
    [TopologicalSpace Z] [TopologicalSpace W] [T2Space Z] (e : Z ≃ₜ W) :
    SchwartzBruhat W →ₗ[ℂ] SchwartzBruhat Z where
  toFun f := f.compLeftInverse e e.symm e.continuous e.symm.continuous e.symm_apply_apply
  map_add' f g := by ext x; rfl
  map_smul' c f := by ext x; rfl

@[simp]
private theorem testPullback_apply {Z : Type v} {W : Type w}
    [TopologicalSpace Z] [TopologicalSpace W] [T2Space Z] (e : Z ≃ₜ W)
    (f : SchwartzBruhat W) (x : Z) : testPullback e f x = f (e x) := rfl

private theorem linearMap_mem_span_range {A : Type*} {M : Type*} {N : Type*}
    [AddCommGroup M] [Module ℂ M] [AddCommGroup N] [Module ℂ N]
    (L : M →ₗ[ℂ] N) (g : A → M) (S : Submodule ℂ N)
    (h : ∀ a, L (g a) ∈ S) {x : M} (hx : x ∈ Submodule.span ℂ (Set.range g)) : L x ∈ S := by
  apply (Submodule.span_le (p := S.comap L)).mpr _ hx
  rintro _ ⟨a, rfl⟩
  exact h a

private def optionProductHomeomorph {α : Type u} (Y : Option α → Type v)
    [∀ i, TopologicalSpace (Y i)] : (∀ i, Y i) ≃ₜ Y none × (∀ i : α, Y (some i)) where
  toEquiv := Equiv.piOptionEquivProd
  continuous_toFun := (continuous_apply none).prodMk (continuous_pi fun i => continuous_apply (some i))
  continuous_invFun := continuous_pi fun i => by
    cases i with
    | none => exact continuous_fst
    | some i => exact (continuous_apply i).comp continuous_snd

/-- Every test function on a finite product is a finite linear combination of pure tensors. -/
theorem span_piTensor [∀ i, T2Space (X i)] :
    Submodule.span ℂ (Set.range (piTensor (X := X))) = ⊤ := by
  classical
  refine Fintype.induction_empty_option (P := fun ι _ =>
    ∀ (Y : ι → Type v) [∀ i, TopologicalSpace (Y i)] [∀ i, T2Space (Y i)],
      Submodule.span ℂ (Set.range (piTensor (X := Y))) = ⊤) ?_ ?_ ?_ ι X
  · intro α β _ e ih Y _ _
    let : Fintype α := Fintype.ofEquiv β e.symm
    apply Submodule.eq_top_iff'.mpr
    intro f
    let e' := Homeomorph.piCongrLeft (Y := Y) e
    let L := testPullback e'.symm
    have hx : testPullback e' f ∈ Submodule.span ℂ (Set.range (piTensor (X := fun i => Y (e i)))) := by
      rw [ih]
      exact Submodule.mem_top
    have hL : L (testPullback e' f) = f := by
      ext x
      simp only [L, testPullback_apply, e'.apply_symm_apply]
    rw [← hL]
    refine linearMap_mem_span_range L _ _ (fun g => ?_) hx
    apply Submodule.subset_span
    refine ⟨Equiv.piCongrLeft (fun i => SchwartzBruhat (Y i)) e g, ?_⟩
    ext x
    simp only [piTensor_apply, L, testPullback_apply, e', Homeomorph.piCongrLeft_symm_apply]
    exact (Fintype.prod_equiv e _ _ fun i => by rw [Equiv.piCongrLeft_apply_apply]).symm
  · intro Y _ _
    apply Submodule.eq_top_iff'.mpr
    intro f
    let x : ∀ i, Y i := fun i => isEmptyElim i
    let g : ∀ i, SchwartzBruhat (Y i) := fun i => isEmptyElim i
    have he : f = f x • piTensor g := by
      ext y
      obtain rfl := Subsingleton.elim y x
      simp
    rw [he]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨g, rfl⟩)
  · intro α _ ih Y _ _
    apply Submodule.eq_top_iff'.mpr
    intro f
    let e := optionProductHomeomorph Y
    let f' := testPullback e.symm f
    obtain ⟨N, g₀, g₁, h⟩ := exists_tensor_expansion f'
    let L (j : Fin N) : SchwartzBruhat (∀ i : α, Y (some i)) →ₗ[ℂ]
        SchwartzBruhat (∀ i, Y i) :=
      (testPullback e).comp
        ({ toFun := fun g => (g₀ j).tensor g
           map_add' := fun g g' => by
             ext z
             exact mul_add (g₀ j z.1) (g z.2) (g' z.2)
           map_smul' := fun c g => by
             ext z
             exact mul_left_comm (g₀ j z.1) c (g z.2) } :
           SchwartzBruhat (∀ i : α, Y (some i)) →ₗ[ℂ]
             SchwartzBruhat (Y none × (∀ i : α, Y (some i))))
    have hf : f = ∑ j, L j (g₁ j) := by
      ext x
      have hx := h (e x).1 (e x).2
      change f' (e x) = _ at hx
      simpa [L, f', tensor, e.symm_apply_apply] using hx
    rw [hf]
    apply Submodule.sum_mem
    intro j _
    have hj : g₁ j ∈ Submodule.span ℂ (Set.range (piTensor (X := fun i : α => Y (some i)))) := by
      rw [ih]
      exact Submodule.mem_top
    refine linearMap_mem_span_range (L j) _ _ (fun g => ?_) hj
    apply Submodule.subset_span
    let gs (i : Option α) : SchwartzBruhat (Y i) := Option.rec (g₀ j) g i
    refine ⟨gs, ?_⟩
    ext x
    change (∏ i, gs i (x i)) = g₀ j (x none) * ∏ i, g i (x (some i))
    rw [Fintype.prod_option]

end Langlands.HarmonicAnalysis.SchwartzBruhat
