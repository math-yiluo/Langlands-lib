import Langlands.AlgebraicGeometry.AffineCechDeRhamSquareZeroPullback
import Mathlib.Algebra.Module.Projective
import Mathlib.RingTheory.Ideal.Operations

/-! # Cocycle representatives for a lifted first Hodge step -/

universe u

open CategoryTheory AlgebraicGeometry
open scoped Pointwise

noncomputable section

namespace Langlands.AlgebraicGeometry.AffineCechDeRham

private lemma eq_of_sup_ideal_eq_of_projective_quotient {R H : Type u}
    [CommRing R] [AddCommGroup H] [Module R H] (I : Ideal R) (hI : I * I = ⊥)
    {N M : Submodule R H} [Module.Projective R (H ⧸ M)] (hNM : N ≤ M)
    (h : N ⊔ I • ⊤ = M ⊔ I • ⊤) : N = M := by
  obtain ⟨s, hs⟩ := M.mkQ.exists_rightInverse_of_surjective M.range_mkQ
  let p : H →ₗ[R] H := LinearMap.id - s.comp M.mkQ
  have hp (x : H) : p x ∈ M := by
    rw [← M.ker_mkQ, LinearMap.mem_ker]
    change M.mkQ (x - s (M.mkQ x)) = 0
    rw [map_sub, show M.mkQ (s (M.mkQ x)) = M.mkQ x from LinearMap.congr_fun hs _,
      sub_self]
  have hfix {x : H} (hx : x ∈ M) : p x = x := by
    change x - s (M.mkQ x) = x
    have hzero : M.mkQ x = 0 := LinearMap.mem_ker.mp (by rwa [Submodule.ker_mkQ])
    rw [hzero, map_zero, sub_zero]
  have hrange : LinearMap.range p = M := by
    apply le_antisymm
    · rintro _ ⟨x, rfl⟩
      exact hp x
    · exact fun x hx => ⟨x, hfix hx⟩
  have hmap (T : Submodule R H) (hT : T ≤ M) : T.map p = T := by
    apply le_antisymm
    · rintro _ ⟨x, hx, rfl⟩
      rwa [hfix (hT hx)]
    · exact fun x hx => ⟨x, hx, hfix (hT hx)⟩
  have he := congrArg (Submodule.map p) h
  rw [Submodule.map_sup, Submodule.map_sup, hmap N hNM, hmap M le_rfl,
    Submodule.map_smul'', Submodule.map_top, hrange,
    show M ⊔ I • M = M from sup_eq_left.mpr Submodule.smul_le_right] at he
  have hsmall : I • M ≤ N := calc
    I • M = I • (N ⊔ I • M) := congrArg (I • ·) he.symm
    _ = I • N := by rw [Submodule.smul_sup, ← Submodule.mul_smul, hI, Submodule.bot_smul,
      sup_bot_eq]
    _ ≤ N := Submodule.smul_le_right
  rwa [sup_eq_left.mpr hsmall] at he

variable {R : Type u} [CommRing R] {X : Scheme.{u}}
  {f : X ⟶ Spec (CommRingCat.of R)} {U : Scheme.AffineOpenCover.{u} X}
  [Smooth f] [IsSeparated f] [Finite U.I₀] {κ : Type u}

/-- Representatives of generators of a lifted summand obtained by adding
ideal multiples of degree-one cocycles to the original closed forms. -/
structure HodgeSummandCocycles (I : Ideal R) (b : κ → closedForms f U) (M : Submodule R (H1 f U)) where
  correction : κ → ↥(I • (⊤ : Submodule R (cocycles f U)))
  span_class : Submodule.span R (Set.range fun k =>
    closedFormClass f U (b k) + (boundaries f U).mkQ (correction k).val) = M

variable (I : Ideal R) (b : κ → closedForms f U) (M : Submodule R (H1 f U))

/-- Any summand with projective quotient and the same reduced span as the
first Hodge step has such representatives for the supplied generators. -/
theorem nonempty_hodgeSummandCocycles (hI : I * I = ⊥) [Module.Projective R (H1 f U ⧸ M)]
    (hb : Submodule.span R (Set.range (closedFormClass f U ∘ b)) = hodgeF1 f U)
    (hM : M ⊔ I • ⊤ = hodgeF1 f U ⊔ I • ⊤) :
    Nonempty (HodgeSummandCocycles I b M) := by
  classical
  let F := closedFormClass f U ∘ b
  have hlift (k : κ) : F k ∈ M ⊔ I • ⊤ := by
    rw [hM, ← hb]
    exact (le_sup_left : Submodule.span R (Set.range F) ≤ _)
      (Submodule.subset_span (Set.mem_range_self k))
  choose m hm x hx hmx using fun k => Submodule.mem_sup.mp (hlift k)
  let q := (boundaries f U).mkQ
  have hq : (I • (⊤ : Submodule R (cocycles f U))).map q = I • ⊤ := by
    rw [Submodule.map_smul'', Submodule.map_top, Submodule.range_mkQ]
  have hrep (k : κ) : ∃ c : ↥(I • (⊤ : Submodule R (cocycles f U))), q c.val = -x k := by
    have hmem : -x k ∈ (I • (⊤ : Submodule R (cocycles f U))).map q := by
      rw [hq]
      exact Submodule.neg_mem _ (hx k)
    obtain ⟨c, hc, hcx⟩ := hmem
    exact ⟨⟨c, hc⟩, hcx⟩
  choose c hc using hrep
  refine ⟨⟨c, ?_⟩⟩
  have hclass (k : κ) : closedFormClass f U (b k) + q (c k).val = m k := by
    change F k + q (c k).val = m k
    rw [hc, ← hmx]
    abel
  change Submodule.span R (Set.range fun k => closedFormClass f U (b k) + q (c k).val) = M
  simp only [hclass]
  let N := Submodule.span R (Set.range m)
  change N = M
  have hNM : N ≤ M := Submodule.span_le.mpr (Set.range_subset_iff.mpr hm)
  apply eq_of_sup_ideal_eq_of_projective_quotient I hI hNM
  refine le_antisymm (sup_le_sup_right hNM _) ?_
  rw [hM]
  refine sup_le ?_ le_sup_right
  rw [← hb]
  apply Submodule.span_le.mpr
  rintro _ ⟨k, rfl⟩
  exact Submodule.mem_sup.mpr ⟨m k, Submodule.subset_span (Set.mem_range_self k), x k, hx k, hmx k⟩

namespace HodgeSummandCocycles

variable {I b M} (G : HodgeSummandCocycles (f := f) (U := U) I b M)

/-- The degree-one cocycle formed by adding a correction to the original
closed form, viewed in the total complex. -/
def representative (k : κ) : cocycles f U :=
  (⟨(0, (b k).val), by
    have hb := (b k).property
    change cechD U (oneForms f) 0 (b k).val = 0 ∧
      cochainMap U (exteriorD1 f) 0 (b k).val = 0 at hb
    change D1 f U (0, (b k).val) = 0
    rw [D1_apply, map_zero, map_zero, sub_zero, hb.1, hb.2]
    rfl⟩ : cocycles f U) + (G.correction k).val

lemma span_representative :
    Submodule.span R (Set.range ((boundaries f U).mkQ ∘ G.representative)) = M := by
  have he (k : κ) : (boundaries f U).mkQ (G.representative k) =
      closedFormClass f U (b k) + (boundaries f U).mkQ (G.correction k).val := by
    rw [representative, map_add]
    rfl
  simpa only [Function.comp_def, he] using G.span_class

lemma representative_overlap_mem (k : κ) (τ : Fin 2 → U.I₀) :
    (G.representative k).val.1 τ ∈ I.map (algebraMap R (tupleSections f U τ)) := by
  let L : cocycles f U →ₗ[R] tupleSections f U τ :=
    (LinearMap.proj τ).comp ((LinearMap.fst R _ _).comp (cocycles f U).subtype)
  have h := Submodule.smul_top_le_comap_smul_top I L (G.correction k).property
  change L (G.correction k).val ∈ I • (⊤ : Submodule R (tupleSections f U τ)) at h
  rw [Ideal.smul_top_eq_map] at h
  change (0 : tupleSections f U τ) + L (G.correction k).val ∈ _
  rw [zero_add]
  exact h

lemma representative_form_sub_mem (k : κ) (τ : Fin 1 → U.I₀) :
    (G.representative k).val.2 τ - (b k).val τ ∈
      I • (⊤ : Submodule R Ω[(tupleSections f U τ)⁄R]) := by
  let L : cocycles f U →ₗ[R] Ω[(tupleSections f U τ)⁄R] :=
    (LinearMap.proj τ).comp ((LinearMap.snd R _ _).comp (cocycles f U).subtype)
  have h := Submodule.smul_top_le_comap_smul_top I L (G.correction k).property
  let a : Ω[(tupleSections f U τ)⁄R] := (b k).val τ
  change a + L (G.correction k).val - a ∈ _
  rw [add_sub_cancel_left]
  exact h

end HodgeSummandCocycles

end Langlands.AlgebraicGeometry.AffineCechDeRham
