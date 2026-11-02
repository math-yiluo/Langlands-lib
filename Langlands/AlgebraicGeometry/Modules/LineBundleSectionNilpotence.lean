import Langlands.AlgebraicGeometry.Modules.LineBundleSectionClearingProof

/-! # Nilpotence of line-bundle sections with empty generation open -/

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
open Langlands.Scheme.Modules Langlands.AlgebraicGeometry.Picard

namespace Langlands.SchemeModule

open SectionClearing

set_option backward.isDefEq.respectTransparency false in
/-- On a quasi-compact scheme, a line-bundle section with empty generation open
has a zero positive tensor power. -/
theorem exists_pos_sectionPow_eq_zero_of_trivializationOpen_eq_bot
    (X : Scheme.{u}) [CompactSpace X] (L : LineBundle X) (s : GlobalSections L.obj)
    (hs : trivializationOpen L.obj s = ⊥) :
    ∃ n : ℕ, 1 ≤ n ∧ sectionPow L.obj s n = 0 := by
  classical
  have hloc : ∀ x : X, ∃ V : X.Opens, x ∈ V ∧ ∃ k : ℕ,
      ∀ m : ℕ, k ≤ m →
        (tensorPow L.obj m).presheaf.map (homOfLE (le_top : V ≤ ⊤)).op
          (sectionPow L.obj s m) = 0 := by
    intro x
    obtain ⟨T, hxT, ⟨e⟩⟩ := L.property x
    obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVT⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open hxT T.isOpen
    change V ≤ T at hVT
    let c : Γ(X, T) := chartCoeff (chartMulOf T L.obj e (sectionHom L.obj s))
    let C : LocalChart (tensorPow L.obj) (sectionMulPow L.obj s) T c :=
      localChartOf (fun m => chartIso T L.obj e m) _ (chartIso_succ T L.obj e s)
    have hc : X.basicOpen (X.presheaf.map (homOfLE hVT).op c) = ⊥ := by
      rw [Scheme.basicOpen_res, show X.basicOpen c = T ⊓ trivializationOpen L.obj s from
        basicOpen_chartCoeff T L s e, hs, inf_bot_eq, inf_bot_eq]
    obtain ⟨k, hk⟩ :=
      (Scheme.isNilpotent_iff_basicOpen_eq_bot_of_isCompact hV.isCompact _).mpr hc
    refine ⟨V, hxV, k, fun m hm => C.injective m V hVT ?_⟩
    rw [C.E_pow (sectionPow L.obj s) (sectionMul_app_sectionPow L.obj s),
      pow_eq_zero_of_le hm hk, mul_zero, C.E_zero]
  choose V hxV k hk using hloc
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun x => (V x : Set X))
    (fun x => (V x).isOpen) (fun x _ => Set.mem_iUnion.mpr ⟨x, hxV x⟩)
  let n : ℕ := (Finset.univ.sup (fun i : t => k i.1)) + 1
  refine ⟨n, Nat.succ_le_succ (Nat.zero_le _), ?_⟩
  let F : TopCat.Sheaf Ab X := ⟨(tensorPow L.obj n).presheaf, (tensorPow L.obj n).isSheaf⟩
  have hcover : (⊤ : X.Opens) ≤ iSup (fun i : t => V i.1) := by
    intro x _
    have hxt := ht (Set.mem_univ x)
    simp only [Set.mem_iUnion] at hxt
    obtain ⟨i, hi, hxi⟩ := hxt
    exact Opens.mem_iSup.mpr ⟨⟨i, hi⟩, hxi⟩
  refine F.eq_of_locally_eq' (fun i : t => V i.1) ⊤ (fun _ => homOfLE le_top)
    hcover _ _ (fun i => ?_)
  change (tensorPow L.obj n).presheaf.map (homOfLE le_top).op
      (sectionPow L.obj s n) =
    (tensorPow L.obj n).presheaf.map (homOfLE le_top).op 0
  rw [map_zero]
  apply hk i.1 n
  change k i.1 ≤ Finset.univ.sup (fun j : t => k j.1) + 1
  exact (Finset.le_sup (f := fun j : t => k j.1) (Finset.mem_univ i)).trans
    (Nat.le_succ _)

end Langlands.SchemeModule
