/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Modules.ExteriorPower
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
import all WeilConjectures.AlgebraicGeometry.Modules.ExteriorTensorLiftHomExt
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Free

/-!
# Vanishing of a wedge with too many factors from a finite locally free sheaf
-/

@[expose] public section

universe v
open CategoryTheory Opposite MonoidalCategory
namespace AlgebraicGeometry.Scheme.Modules

private theorem alternating_zero_on_large_image
    {R M N D ι : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] [AddCommGroup D] [Module R D]
    (r : ℕ) (b : Module.Basis (Fin r) R M) (f : M →ₗ[R] N)
    (w : N [⋀^ι]→ₗ[R] D) (x : ι → N) (t : Finset ι)
    (ht : r < t.card) (hx : ∀ i ∈ t, ∃ a, f a = x i) : w x = 0 := by
  classical
  let m := (w.toMultilinearMap.domDomRestrict (fun i ↦ i ∈ t)
    (fun i ↦ x i)).compLinearMap (fun _ ↦ f)
  let g : M [⋀^{i : ι // i ∈ t}]→ₗ[R] D :=
    { m with
      map_eq_zero_of_eq' := by
        intro a i j hij hne
        apply w.map_eq_zero_of_eq _ (i := i.val) (j := j.val)
        · simpa [m] using congrArg f hij
        · exact fun h ↦ hne (Subtype.ext h) }
  have hg : g = 0 := by
    apply b.ext_alternating
    intro a ha
    have hcard := Fintype.card_le_of_injective a ha
    simp only [Fintype.card_fin, Fintype.card_coe] at hcard
    omega
  choose a ha using hx
  have heq : (fun i ↦ if h : i ∈ t then f (a i h) else x i) = x := by
    funext i
    split_ifs with h
    · exact ha i h
    · rfl
  have h := DFunLike.congr_fun hg (fun i ↦ a i.val i.property)
  change w (fun i ↦ if h : i ∈ t then f (a i h) else x i) = 0 at h
  simpa only [heq] using h

private theorem alternating_append_image_zero
    {R M N D : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] [AddCommGroup D] [Module R D]
    (r s : ℕ) (b : Module.Basis (Fin r) R M) (f : M →ₗ[R] N)
    (w : N [⋀^Fin (r + s)]→ₗ[R] D) (a : Fin r → M) (c : Fin s → N)
    (j : Fin s) (d : M) (hc : c j = f d) :
    w (Fin.append (fun k ↦ f (a k)) c) = 0 := by
  classical
  let t := (Finset.univ : Finset (Fin r)).image (Fin.castAdd s)
  have hj : Fin.natAdd r j ∉ t := by
    simp only [t, Finset.mem_image, Finset.mem_univ, true_and, not_exists]
    intro i hi
    have := congrArg Fin.val hi
    simp only [Fin.val_castAdd, Fin.val_natAdd] at this
    omega
  apply alternating_zero_on_large_image r b f w _ (insert (Fin.natAdd r j) t)
  · rw [Finset.card_insert_of_notMem hj]
    have ht : t.card = r := by
      dsimp only [t]
      rw [Finset.card_image_of_injective _ (Fin.castAdd_injective r s)]
      simp
    omega
  · intro i hi
    rcases Finset.mem_insert.mp hi with h | h
    · subst i
      exact ⟨d, by simpa using hc.symm⟩
    · obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp h
      exact ⟨a k, by simp⟩

set_option backward.isDefEq.respectTransparency false in
/-- Wedging a full-rank tuple with an additional image from that sheaf gives zero. -/
theorem exteriorSheaf_rank_wedge_eq_zero {X : Scheme.{v}} {A B : X.Modules}
    (f : A ⟶ B) (r n s : ℕ) (hr : n = r + s) [A.IsFiniteLocallyFreeOfRank r]
    (U : X.Opens) (a : Fin r → A.val.obj (op U))
    (c : Fin s → B.val.obj (op U)) (j : Fin s) (d : A.val.obj (op U))
    (hc : c j = f.val.app (op U) d) :
    wedge (M := B) (r := n) (U := U)
      (fun i ↦ Fin.append (fun k ↦ f.val.app (op U) (a k)) c (Fin.cast hr i)) = 0 := by
  classical
  subst n
  obtain ⟨q, hq, hqr⟩ :=
    SheafOfModules.IsFiniteLocallyFreeOfRank.exists_localGeneratorsData (M := A) (r := r)
  let := hq
  apply ((exteriorPower B (r + s)).isSheaf_presheaf_comp_forget _
    (q.coversTop U)).isSeparatedFor.ext
  rintro V k ⟨i, ⟨l⟩⟩
  let e : A.over (q.X i) ≅ SheafOfModules.free (ULift.{v} (Fin r)) :=
    (asIso (q.generators i).π).symm ≪≫ SheafOfModules.freeFunctor.mapIso
      ((hqr i).some.trans Equiv.ulift.symm).toIso
  let E := SheafOfModules.sectionsLinearEquivOfIsoFree e (op (Over.mk l))
  let b : Module.Basis (Fin r) (X.presheaf.obj (op V)) (A.val.obj (op V)) :=
    ((Pi.basisFun _ (ULift.{v} (Fin r))).map E.symm).reindex Equiv.ulift
  change (exteriorPower B (r + s)).val.map k.op
    (wedge (M := B) (r := (r + s)) (U := U) _) =
      (exteriorPower B (r + s)).val.map k.op 0
  rw [map_zero, exterior_section_map]
  have hnat (x : A.val.obj (op U)) :
      B.val.map k.op (f.val.app (op U) x) =
        f.val.app (op V) (A.val.map k.op x) :=
    (PresheafOfModules.naturality_apply f.val k.op x).symm
  have hx :
      (fun i ↦ B.val.map k.op
        (Fin.append (fun k ↦ f.val.app (op U) (a k)) c (Fin.cast rfl i))) =
      Fin.append (fun i ↦ f.val.app (op V) (A.val.map k.op (a i)))
        (fun i ↦ B.val.map k.op (c i)) := by
    funext i
    refine Fin.addCases (fun i ↦ ?_) (fun i ↦ ?_) i
    · simp only [Fin.cast_refl, id_eq, Fin.append_left]
      exact hnat (a i)
    · simp
  rw [hx]
  unfold wedge
  have hw := alternating_append_image_zero r s b (f.val.app (op V)).hom
    (_root_.exteriorPower.ιMulti (X.presheaf.obj (op V)) (r + s))
    (fun i ↦ A.val.map k.op (a i)) (fun i ↦ B.val.map k.op (c i)) j
    (A.val.map k.op d) (by rw [hc, hnat])
  erw [hw]
  exact map_zero _

end AlgebraicGeometry.Scheme.Modules
