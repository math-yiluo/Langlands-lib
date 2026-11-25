/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.Boundary
public import Mathlib.AlgebraicTopology.SimplicialSet.Degenerate
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
import Mathlib.CategoryTheory.Limits.Types.Pushouts

/-! # Gluing a simplex to a simplicial subset
Source: literature/stacks-project/simplicial.tex,
Lemma 018R (auxiliary; not a blueprint node)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open Simplicial
universe u

namespace SSet

/-- Adding one simplex to a simplicial subset is a pushout along its boundary.
Source: Stacks Project, Lemma 018R (auxiliary; not a blueprint node).
Proof:
1. The simplex `x` is nondegenerate: a lower-dimensional ancestor belongs to `U` by
   `hbelow`, contradicting `hx`. A non-surjective map to `[n]` factors through a missing
   face (lem-weil-pbc-simplex-face-factorization); that face of `x` lies in `U` by
   `hbelow`. Thus the simplex map restricts to a boundary map `b`. For `n = 0` the
   boundary is empty.
2. By unique nondegenerate decomposition
   (lem-weil-pbc-simplicial-set-nondegenerate-decomposition), every simplex outside `U`
   has a nondegenerate ancestor outside `U`. The ancestor cannot have degree below `n`
   by `hbelow`, or above `n` by `habove`; `hat` identifies it with `x`. Thus each new
   simplex is the image of `x` under a unique surjection. Such an image cannot lie in
   `U`, since an order-preserving section would then put `x` in `U`.
3. Given maps `g : U → Y` and `h : Δ[n] → Y` agreeing on the boundary, define the
   extension by `g` on `U` and by `h` on the unique surjections of step 2. Under a
   simplicial operator, a composite that remains surjective uses step 2; a composite
   that is not surjective uses step 1 and the boundary agreement. This proves naturality.
4. The same two cases show that the extension composed with the simplex map is `h`.
   Any extension agrees on `U` and on every degeneracy of `x`, so it is unique. This is
   the pushout universal property. When `n = 0`, all maps to `[0]` are surjective and
   the empty boundary makes this the coproduct `U ∐ Δ[0]`.
-/
theorem glue_simplex
    {X : SSet.{u}} (U V : X.Subcomplex) (hUV : U ≤ V)
    {n : ℕ}
    (x : (V.toSSet).obj (Opposite.op (SimplexCategory.mk n)))
    (hx : x.1 ∉ U.obj (Opposite.op (SimplexCategory.mk n)))
    (hbelow : ∀ i : ℕ, i < n →
      V.obj (Opposite.op (SimplexCategory.mk i)) = U.obj (Opposite.op (SimplexCategory.mk i)))
    (hat : V.obj (Opposite.op (SimplexCategory.mk n)) =
      U.obj (Opposite.op (SimplexCategory.mk n)) ∪ {x.1})
    (habove : ∀ j : ℕ, n < j → ∀ z : (V.toSSet).obj (Opposite.op (SimplexCategory.mk j)),
      z.1 ∉ U.obj (Opposite.op (SimplexCategory.mk j)) →
      z ∈ (V.toSSet).degenerate j) :
    ∃ b : (SSet.boundary n).toSSet ⟶ U.toSSet,
      b ≫ Subcomplex.homOfLE hUV = (SSet.boundary n).ι ≫ SSet.yonedaEquiv.symm x ∧
      IsPushout b (SSet.boundary n).ι (Subcomplex.homOfLE hUV)
        (SSet.yonedaEquiv.symm x) := by
  classical
  let a : Δ[n] ⟶ V.toSSet := SSet.yonedaEquiv.symm x
  -- The new simplex cannot come from a smaller degree.
  have hnd : x ∈ V.toSSet.nonDegenerate n := by
    rintro ⟨m, hm, f, y, hy⟩
    apply hx
    have hyU : y.1 ∈ U.obj (Opposite.op ⦋m⦌) := by
      rw [← hbelow m hm]
      exact y.2
    have h := U.map f.op hyU
    rw [← hy]
    exact h
  -- The preimage is the boundary: it contains all boundary generators and is proper.
  have hpre : U.preimage (a ≫ V.ι) = boundary n := by
    rw [stdSimplex.eq_boundary_iff]
    refine ⟨?_, ?_⟩
    · rw [Subcomplex.le_iff_contains_nonDegenerate]
      rintro m ⟨y, hy₁⟩ hy₂
      have hm : m < n := dim_lt_of_nonDegenerate (X := (boundary n).toSSet)
        ⟨⟨y, hy₂⟩, ((boundary n).mem_nonDegenerate_iff ⟨y, hy₂⟩).2 hy₁⟩ n
      change (a.app _ y).1 ∈ U.obj _
      rw [← hbelow m hm]
      exact (a.app _ y).2
    · intro h
      have hmem := h.symm.le _
        (show stdSimplex.objEquiv.symm (𝟙 ⦋n⦌) ∈ (⊤ : (Δ[n]).Subcomplex).obj _ by simp)
      change (a.app _ (stdSimplex.objEquiv.symm (𝟙 ⦋n⦌))).1 ∈ U.obj _ at hmem
      apply hx
      change X.map (𝟙 (Opposite.op ⦋n⦌)) x.1 ∈ U.obj _ at hmem
      simpa only [Functor.map_id_apply] using hmem
  have hbound : Subcomplex.range ((boundary n).ι ≫ a ≫ V.ι) ≤ U := by
    rw [Subcomplex.range_comp, Subcomplex.image_le_iff, hpre]
    rintro m y ⟨z, rfl⟩
    exact z.2
  let b : (boundary n).toSSet ⟶ U.toSSet :=
    Subcomplex.lift ((boundary n).ι ≫ a ≫ V.ι) hbound
  have hw : b ≫ Subcomplex.homOfLE hUV = (boundary n).ι ≫ a := by
    rw [← cancel_mono V.ι]
    simp [b]
  -- A nondegenerate ancestor outside U must be the single new n-simplex.
  have hcover (m : ℕ) (z : V.toSSet _⦋m⦌)
      (hz : z.1 ∉ U.obj (Opposite.op ⦋m⦌)) :
      ∃ f : ⦋m⦌ ⟶ ⦋n⦌, z = V.toSSet.map f.op x := by
    obtain ⟨r, f, hf, y, hy⟩ := V.toSSet.exists_nonDegenerate z
    have hyU : y.1.1 ∉ U.obj (Opposite.op ⦋r⦌) := by
      intro hyU
      apply hz
      rw [hy]
      exact U.map f.op hyU
    have hr : r = n := by
      apply le_antisymm
      · by_contra hr
        exact y.2 (habove r (by omega) y.1 hyU)
      · by_contra hr
        apply hyU
        rw [← hbelow r (by omega)]
        exact y.1.2
    subst r
    have hyx : y.1 = x := by
      apply Subtype.ext
      have h := hat.le y.1.2
      simpa only [Set.mem_singleton_iff] using h.resolve_left hyU
    exact ⟨f, by simpa only [hyx] using hy⟩
  refine ⟨b, hw, ?_⟩
  -- Check the pullback, coverage, and injectivity conditions degree by degree.
  apply IsPushout.of_forall_isPushout_app
  rintro ⟨⟨m⟩⟩
  refine Types.isPushout_of_isPullback_of_mono' ?_ ?_ ?_
  · rw [Types.isPullback_iff]
    refine ⟨NatTrans.congr_app hw _, ?_, ?_⟩
    · intro p q h
      exact Subtype.ext h.2
    · intro y z h
      have hz : z ∈ (boundary n).obj (Opposite.op ⦋m⦌) := by
        rw [← hpre]
        change (a.app _ z).1 ∈ U.obj _
        have hval := congrArg Subtype.val h
        change y.1 = (a.app _ z).1 at hval
        rw [← hval]
        exact y.2
      refine ⟨⟨z, hz⟩, ?_, rfl⟩
      apply Subtype.ext
      change (a.app _ z).1 = y.1
      exact congrArg Subtype.val h.symm
  · apply Set.eq_univ_of_forall
    intro z
    by_cases hz : z.1 ∈ U.obj (Opposite.op ⦋m⦌)
    · exact Or.inl ⟨⟨z.1, hz⟩, rfl⟩
    · obtain ⟨f, hf⟩ := hcover m z hz
      exact Or.inr ⟨stdSimplex.objEquiv.symm f,
        (yonedaEquiv_symm_app_objEquiv_symm x f).trans hf.symm⟩
  · intro p q hp _ h
    have hp' : p ∉ (boundary n).obj (Opposite.op ⦋m⦌) :=
      fun hp' ↦ hp ⟨⟨p, hp'⟩, rfl⟩
    obtain ⟨f, rfl⟩ := stdSimplex.objEquiv.symm.surjective p
    obtain ⟨g, rfl⟩ := stdSimplex.objEquiv.symm.surjective q
    have hf : Epi f := by
      simpa [SimplexCategory.epi_iff_surjective, boundary] using! hp'
    have hfg : V.toSSet.map f.op x = V.toSSet.map g.op x := h
    have hfg' := V.toSSet.unique_nonDegenerate_map _ f ⟨x, hnd⟩ rfl
      g ⟨x, hnd⟩ hfg
    exact congrArg stdSimplex.objEquiv.symm hfg'

end SSet
