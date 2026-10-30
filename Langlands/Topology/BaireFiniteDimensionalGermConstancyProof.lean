import Langlands.Topology.BaireFiniteDimensionalGermConstancyStatement
import Mathlib.LinearAlgebra.Dual.Lemmas

/-! Baire constancy proved using finitely many separating evaluations. -/

namespace Langlands.Topology

universe uX uY

/-- The assigned finite-dimensional germ is constant on a nonempty open set. -/
theorem baireFiniteDimensionalGermConstancy :
    BaireFiniteDimensionalGermConstancyStatement.{uX,uY} := by
  classical
  intro X Y _ _ _ D hD V _ hinj f v hf hevent
  have reconstruct (m : ℕ) :
      ∃ g : Y → V, IsLocallyConstant g ∧
        ∀ y, (∀ x ∈ D m, f y x = (v y : X → ℂ) x) → g y = v y := by
    let L : D m → V →ₗ[ℂ] ℂ := fun x =>
      (LinearMap.proj (R := ℂ) (φ := fun _ : X => ℂ) x.val).comp V.subtype
    have hspan : Submodule.span ℂ (Set.range L) = ⊤ := by
      apply top_unique
      intro K _
      apply FiniteDimensional.mem_span_of_iInf_ker_le_ker
      intro w hw
      have hwzero : w = 0 := by
        apply hinj m
        funext x
        exact ((Submodule.mem_iInf _).mp hw x)
      simp [hwzero]
    have hfg : (Submodule.span ℂ (Set.range L)).FG := by
      rw [hspan]
      exact Module.Finite.fg_top
    obtain ⟨s, hs, hsspan⟩ :=
      (Submodule.fg_span_iff_fg_span_finset_subset (Set.range L)).mp hfg
    have hsEval : ∀ i : s, ∃ x : D m, L x = i.val := fun i => hs i.property
    choose p hp using hsEval
    let R : V → s → ℂ := fun w i => i.val w
    have hR : Function.Injective R := by
      intro w z hwz
      have hforms : ∀ K ∈ Submodule.span ℂ (s : Set (V →ₗ[ℂ] ℂ)), K w = K z := by
        intro K hK
        induction hK using Submodule.span_induction with
        | mem K hK => exact congrFun hwz ⟨K, hK⟩
        | zero => simp
        | add K H _ _ hK hH => simp [hK, hH]
        | smul a K _ hK => simp [hK]
      apply hinj m
      funext x
      exact hforms (L x) (by rw [← hsspan, hspan]; trivial)
    let F : Y → s → ℂ := fun y i => f y (p i).val
    have hF : IsLocallyConstant F :=
      (LocallyConstant.unflip (fun i : s =>
        (⟨fun y : Y => f y (p i).val, hf (p i).val⟩ : LocallyConstant Y ℂ))).isLocallyConstant
    refine ⟨Function.invFun R ∘ F, hF.comp (Function.invFun R), ?_⟩
    intro y hy
    have hFy : F y = R (v y) := by
      funext i
      change f y (p i).val = i.val (v y)
      rw [← hp i]
      exact hy (p i).val (p i).property
    change Function.invFun R (F y) = v y
    rw [hFy]
    exact Function.leftInverse_invFun hR (v y)
  choose g hglocal hgrep using reconstruct
  let C : ℕ → Set Y := fun m => {y | ∀ x ∈ D m, f y x = (g m y : X → ℂ) x}
  have hCclosed (m : ℕ) : IsClosed (C m) := by
    have hC : C m = ⋂ x : D m, {y | f y x.val = (g m y : X → ℂ) x.val} := by
      ext y
      simp [C]
    rw [hC]
    apply isClosed_iInter
    intro x
    simpa only [Pi.sub_apply, Function.comp_apply, sub_eq_zero] using
      ((hf x.val).sub ((hglocal m).comp (fun w : V => (w : X → ℂ) x.val))).isClosed_fiber 0
  have hCcover : ⋃ m, C m = Set.univ := by
    apply Set.eq_univ_of_forall
    intro y
    obtain ⟨m, hm⟩ := hevent y
    apply Set.mem_iUnion.mpr
    refine ⟨m, ?_⟩
    change ∀ x ∈ D m, f y x = (g m y : X → ℂ) x
    rw [hgrep m y hm]
    exact hm
  have hCeq (m : ℕ) (y : Y) (hy : y ∈ C m) : g m y = v y := by
    obtain ⟨k, hk⟩ := hevent y
    apply hinj (max m k)
    funext x
    exact (hy x.val (hD (le_max_left m k) x.property)).symm.trans
      (hk x.val (hD (le_max_right m k) x.property))
  obtain ⟨m, y, hy⟩ := nonempty_interior_of_iUnion_of_closed hCclosed hCcover
  let O : Set Y := interior (C m) ∩ {z | g m z = g m y}
  refine ⟨O, isOpen_interior.inter ((hglocal m).isOpen_fiber (g m y)),
    ⟨y, hy, rfl⟩, ?_⟩
  intro z hz w hw
  exact (hCeq m z (interior_subset hz.1)).symm.trans
    ((hz.2.trans hw.2.symm).trans (hCeq m w (interior_subset hw.1)))

end Langlands.Topology
