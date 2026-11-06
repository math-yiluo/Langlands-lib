import Langlands.GroupScheme.Reductive.IntegralWeylVectorProperties
import Mathlib.LinearAlgebra.RootSystem.Finite.Nondegenerate
import Mathlib.LinearAlgebra.RootSystem.WeylGroup
import Mathlib.Tactic

/-! # Integral Weyl opposition for the weight rho -/

noncomputable section

universe u v w

namespace Langlands.IntegralWeylVector

variable {J : Type u} {X : Type v} {Y : Type w}
    [AddCommGroup X] [AddCommGroup Y]
    (P : RootDatum J X Y) (b : P.Base) (hspan : P.corootSpan ℤ = ⊤)

include hspan in
private theorem finite_aut [Finite J] : Finite P.Aut := by
  apply Finite.of_injective (RootPairing.Equiv.indexHom P)
  intro a c hac
  apply RootPairing.Equiv.coweightHom_injective P
  apply MulOpposite.unop_injective
  apply LinearEquiv.toLinearMap_injective
  apply LinearMap.ext_on_range hspan
  intro i
  change a.toHom.coweightMap (P.coroot i) = c.toHom.coweightMap (P.coroot i)
  rw [RootPairing.Hom.coroot_coweightMap_apply, RootPairing.Hom.coroot_coweightMap_apply]
  exact congrArg P.coroot
    (congrFun (congrArg Equiv.toFun (congrArg Equiv.symm hac)) i)

variable [Fintype J]

private theorem rootForm_root_pos (i : J) :
    0 < P.RootForm (P.root i) (P.root i) := by
  rw [P.rootForm_apply_apply]
  apply Finset.sum_pos'
  · intro j _
    exact mul_self_nonneg _
  · exact ⟨i, Finset.mem_univ _, by simp⟩

private theorem two_mul_rootForm_root (x : X) (i : J) :
    2 * P.RootForm x (P.root i) =
      P.RootForm (P.root i) (P.root i) * P.coroot' i x := by
  have h := congrArg (fun y : Y => P.toLinearMap x y)
    (P.rootForm_self_smul_coroot i)
  have hs : P.RootForm (P.root i) x = P.RootForm x (P.root i) :=
    P.rootForm_symmetric.eq _ _
  simp only [map_smul, map_nsmul, smul_eq_mul, nsmul_eq_mul] at h
  rw [P.toLinearMap_apply_apply_Polarization, hs] at h
  exact h.symm

private theorem rootForm_rho_simple_pos (i : b.support) :
    0 < P.RootForm (rho P b hspan) (P.root i) := by
  have h := two_mul_rootForm_root P (rho P b hspan) i
  have he : P.coroot' i (rho P b hspan) = 1 := pairing_rho_simple P b hspan i
  rw [he, mul_one] at h
  have hp := rootForm_root_pos P i
  omega

variable [P.IsReduced]

private theorem rootForm_rho_add_nonpos (x : X)
    (hx : ∀ i : b.support, P.coroot' i x ≤ -1) :
    P.RootForm (rho P b hspan) (x + rho P b hspan) ≤ 0 := by
  classical
  have hsimple (j : b.support) :
      P.RootForm (P.root j) (x + rho P b hspan) ≤ 0 := by
    have hv : P.coroot' j (x + rho P b hspan) ≤ 0 := by
      rw [map_add]
      have he : P.coroot' j (rho P b hspan) = 1 := pairing_rho_simple P b hspan j
      rw [he]
      have := hx j
      omega
    have he := two_mul_rootForm_root P (x + rho P b hspan) j
    have hp := rootForm_root_pos P j
    have hm := mul_nonpos_of_nonneg_of_nonpos hp.le hv
    have hs : P.RootForm (P.root j) (x + rho P b hspan) =
        P.RootForm (x + rho P b hspan) (P.root j) := by
      simpa only [RingHom.id_apply] using
        P.rootForm_symmetric.eq (P.root j) (x + rho P b hspan)
    omega
  have hroot (i : J) (hi : b.IsPos i) :
      P.RootForm (P.root i) (x + rho P b hspan) ≤ 0 := by
    obtain ⟨f, -, hf, he⟩ := b.exists_root_eq_sum_int i
    have hfnonneg : ∀ j, 0 ≤ f j := by
      rcases hf with hf | hf
      · exact hf.le
      · have hn : b.height i ≤ 0 := by
          rw [b.height_eq_sum he]
          exact Finset.sum_nonpos fun j _ => hf.le j
        exact False.elim ((not_le_of_gt hi) hn)
    rw [he, map_sum, LinearMap.sum_apply]
    apply Finset.sum_nonpos
    intro j hj
    rw [LinearMap.map_smul₂, smul_eq_mul]
    exact mul_nonpos_of_nonneg_of_nonpos (hfnonneg j) (hsimple ⟨j, hj⟩)
  have hs :
      P.RootForm ((2 : ℤ) • rho P b hspan) (x + rho P b hspan) ≤ 0 := by
    rw [two_smul_rho_eq_positiveRootSum P b hspan]
    unfold positiveRootSum
    rw [map_sum, LinearMap.sum_apply]
    exact Finset.sum_nonpos fun i hi => hroot i (Finset.mem_filter.mp hi).2
  rw [LinearMap.map_smul₂, smul_eq_mul] at hs
  omega

/-- A Weyl-orbit norm and negative simple-coroot values characterize negative rho. -/
theorem eq_neg_rho_of_simple_pairings_of_norm (x : X)
    (hx : ∀ i : b.support, P.coroot' i x ≤ -1)
    (hnorm : P.RootForm x x = P.RootForm (rho P b hspan) (rho P b hspan)) :
    x = -rho P b hspan := by
  have hi := rootForm_rho_add_nonpos P b hspan x hx
  have hnormadd :
      P.RootForm (x + rho P b hspan) (x + rho P b hspan) =
        2 * P.RootForm (rho P b hspan) (x + rho P b hspan) := by
    simp only [map_add, LinearMap.add_apply]
    have hs : P.RootForm x (rho P b hspan) = P.RootForm (rho P b hspan) x := by
      simpa only [RingHom.id_apply] using P.rootForm_symmetric.eq x (rho P b hspan)
    rw [hnorm, hs]
    ring
  have hzero : P.RootForm (x + rho P b hspan) (x + rho P b hspan) = 0 := by
    have hn := P.zero_le_rootForm (x + rho P b hspan)
    rw [hnormadd] at hn ⊢
    omega
  have hform : P.RootForm (x + rho P b hspan) = 0 :=
    P.rootForm_self_eq_zero_iff.mp hzero
  have hz : x + rho P b hspan = 0 := by
    apply eq_of_pairing_simple_eq P b hspan
    intro i
    have he := two_mul_rootForm_root P (x + rho P b hspan) i
    rw [hform, LinearMap.zero_apply, mul_zero] at he
    have hp := (rootForm_root_pos P i).ne'
    have hv : P.coroot' i (x + rho P b hspan) = 0 :=
      (mul_eq_zero.mp he.symm).resolve_left hp
    simpa using hv
  exact add_eq_zero_iff_eq_neg.mp hz

/-- A finite reduced integral root datum with full coroot span has a Weyl element
sending its integral rho to negative rho. -/
theorem exists_weyl_neg_rho :
    ∃ w : P.weylGroup, w • rho P b hspan = -rho P b hspan := by
  have : Finite P.Aut := finite_aut P hspan
  obtain ⟨w, hw⟩ := Finite.exists_min
    (fun w : P.weylGroup => P.RootForm (rho P b hspan) (w • rho P b hspan))
  refine ⟨w, eq_neg_rho_of_simple_pairings_of_norm P b hspan _ ?_ ?_⟩
  · intro i
    have hmin := hw (RootPairing.weylGroup.ofIdx P i * w)
    change P.RootForm (rho P b hspan) (w • rho P b hspan) ≤
      P.RootForm (rho P b hspan) (P.reflection i (w • rho P b hspan)) at hmin
    rw [P.reflection_apply, map_sub] at hmin
    have hs :
        P.RootForm (rho P b hspan)
            ((P.coroot' i (w • rho P b hspan)) • P.root i) =
          P.coroot' i (w • rho P b hspan) *
            P.RootForm (rho P b hspan) (P.root i) := by
      exact (P.RootForm (rho P b hspan)).map_smul
        (P.coroot' i (w • rho P b hspan)) (P.root i)
    rw [hs] at hmin
    have hp := rootForm_rho_simple_pos P b hspan i
    have hmul :
        P.coroot' i (w • rho P b hspan) *
          P.RootForm (rho P b hspan) (P.root i) ≤ 0 := by omega
    have hle : P.coroot' i (w • rho P b hspan) ≤ 0 :=
      nonpos_of_mul_nonpos_left hmul hp
    have he : P.coroot' i (w • rho P b hspan) =
        P.coroot' (w.val.indexEquiv.symm i) (rho P b hspan) := by
      simpa only [Equiv.apply_symm_apply] using!
        w.val.coroot'_weightEquiv (w.val.indexEquiv.symm i) (rho P b hspan)
    have hne : P.coroot' i (w • rho P b hspan) ≠ 0 := by
      rw [he]
      exact pairing_rho_coroot_ne_zero P b hspan _
    omega
  · exact RootPairing.InvariantForm.apply_weylGroup_smul P
      (B := P.toInvariantForm) w (rho P b hspan) (rho P b hspan)

/-- An actual Weyl element with its certificate of integral rho opposition. -/
def opposition : {w : P.weylGroup // w • rho P b hspan = -rho P b hspan} :=
  ⟨(exists_weyl_neg_rho P b hspan).choose, (exists_weyl_neg_rho P b hspan).choose_spec⟩

end Langlands.IntegralWeylVector
