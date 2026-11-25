/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.RingTheory.Ideal.Span
public import WeilConjectures.CategoryTheory.RingedIdealGenerators
import WeilConjectures.AlgebraicGeometry.FiniteGeneratorsLocalSpan

/-! # Equality of section ideals on common slice refinements

Source: Stacks Project, algebraization.tex, Tag 099E.
(auxiliary; not a blueprint node).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Opposite
open scoped BigOperators
namespace CategoryTheory
variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
variable (O : Sheaf J CommRingCat.{u})
variable (I : ringedSiteModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O))
variable (ι : I ⟶ SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O))

private theorem generatingList_section_value
    (U : C) (r : ℕ) (f : Fin r → O.obj.obj (op U))
    (σ : (I.over U).GeneratingSections) (e : σ.I ≃ Fin r)
    (h : ∀ i, (SheafOfModules.sectionsMap (ι.over U) (σ.s i)).val
      (op (Over.mk (𝟙 U))) = f (e i))
    (W : C) (a : W ⟶ U) (i : σ.I) :
    ι.val.app (op W) ((σ.s i).val (op (Over.mk a))) = O.obj.map a.op (f (e i)) := by
  let k : Over.mk a ⟶ Over.mk (𝟙 U) := Over.homMk a (by simp)
  have hn := (SheafOfModules.sectionsMap (ι.over U) (σ.s i)).property k.op
  change O.obj.map a.op
    ((SheafOfModules.sectionsMap (ι.over U) (σ.s i)).val (op (Over.mk (𝟙 U)))) = _ at hn
  rw [h] at hn
  exact hn.symm

private theorem exists_cover_mem_span_generatingList
    (U : C) (r : ℕ) (f : Fin r → O.obj.obj (op U))
    (hf : IsRingedIdealGeneratingList O I ι U r f)
    (W : C) (a : W ⟶ U) {T : Type u} [Finite T]
    (s : T → I.val.obj (op W)) :
    ∃ S ∈ J W, ∀ (V : C) (k : V ⟶ W), S k → ∀ j,
      ι.val.app (op V) (I.val.map k.op (s j)) ∈
        Ideal.span (Set.range (fun i ↦ O.obj.map (k ≫ a).op (f i))) := by
  classical
  obtain ⟨σ, e, he⟩ := hf
  let := Fintype.ofEquiv (Fin r) e.symm
  obtain ⟨S, hS, hs⟩ := SheafOfModules.exists_cover_linearCombination_generators
    (I.over U) σ (Over.mk a) s
  refine ⟨Sieve.overEquiv (Over.mk a) S, (J.mem_over_iff S).1 hS, ?_⟩
  intro V k hk j
  let l : Over.mk (k ≫ a) ⟶ Over.mk a := Over.homMk k rfl
  have hl : S l := by
    have hh : ((Sieve.overEquiv (Over.mk a)).symm
        (Sieve.overEquiv (Over.mk a) S)) l := hk
    simpa only [OrderIso.symm_apply_apply] using hh
  obtain ⟨c, hc⟩ := hs (Over.mk (k ≫ a)) l hl j
  change I.val.map k.op (s j) = ∑ i, c i •
    (show I.val.obj (op V) from (σ.s i).val (op (Over.mk (k ≫ a)))) at hc
  rw [hc, map_sum]
  change (∑ i, (show O.obj.obj (op V) from ι.val.app (op V)
    (c i • (show I.val.obj (op V) from (σ.s i).val (op (Over.mk (k ≫ a))))))) ∈ _
  apply Submodule.sum_mem
  intro i _
  have hi := (ι.val.app (op V)).hom.map_smul
    (show ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O).obj.obj (op V) from c i)
    (show I.val.obj (op V) from (σ.s i).val (op (Over.mk (k ≫ a))))
  change (show O.obj.obj (op V) from ι.val.app (op V)
      (c i • (show I.val.obj (op V) from (σ.s i).val (op (Over.mk (k ≫ a)))))) =
    (show O.obj.obj (op V) from c i) *
      (show O.obj.obj (op V) from ι.val.app (op V)
        ((σ.s i).val (op (Over.mk (k ≫ a))))) at hi
  rw [hi, generatingList_section_value O I ι U r f σ e he V (k ≫ a) i]
  exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨e i, rfl⟩)

/-- Two finite lists generating one ideal sheaf generate equal section ideals locally
on every common test span. The cover lies on the original site, without fibre products.
Source: Stacks Project, Tag 099E, independence of generating ideals.
(auxiliary; not a blueprint node).

Proof: choose the generating sections witnessing both lists. On a test span, lift the
finitely many sections of either family through the other family's free epimorphism.
Intersect the two resulting covering sieves. Naturality identifies their images with
the restrictions of the specified lists, so each ideal's generators belong to the other
ideal. This includes the empty lists because finite simultaneous lifting includes them. -/
theorem exists_cover_generatingLists_ideal_eq
    (U : C) (r : ℕ) (f : Fin r → O.obj.obj (op U))
    (hf : IsRingedIdealGeneratingList O I ι U r f)
    (V : C) (s : ℕ) (g : Fin s → O.obj.obj (op V))
    (hg : IsRingedIdealGeneratingList O I ι V s g)
    (W : C) (a : W ⟶ U) (b : W ⟶ V) :
    ∃ S ∈ J W, ∀ (T : C) (k : T ⟶ W), S k →
      Ideal.span (Set.range (fun i ↦ O.obj.map (k ≫ a).op (f i))) =
        Ideal.span (Set.range (fun i ↦ O.obj.map (k ≫ b).op (g i))) := by
  classical
  obtain ⟨σ, e, he⟩ := hf
  obtain ⟨τ, d, hd⟩ := hg
  let := Finite.of_equiv (Fin r) e.symm
  let := Finite.of_equiv (Fin s) d.symm
  obtain ⟨S, hS, hs⟩ := exists_cover_mem_span_generatingList O I ι V s g ⟨τ, d, hd⟩ W b
    (fun i : σ.I ↦ (σ.s i).val (op (Over.mk a)))
  obtain ⟨T, hT, ht⟩ := exists_cover_mem_span_generatingList O I ι U r f ⟨σ, e, he⟩ W a
    (fun i : τ.I ↦ (τ.s i).val (op (Over.mk b)))
  refine ⟨S ⊓ T, J.intersection_covering hS hT, ?_⟩
  intro Z k hk
  apply le_antisymm
  · apply Ideal.span_le.2
    rintro x ⟨i, rfl⟩
    have hi := hs Z k hk.1 (e.symm i)
    have hn := (σ.s (e.symm i)).property
      (Over.homMk (U := Over.mk (k ≫ a)) (V := Over.mk a) k rfl).op
    change I.val.map k.op ((σ.s (e.symm i)).val (op (Over.mk a))) = _ at hn
    rw [hn, generatingList_section_value O I ι U r f σ e he Z (k ≫ a),
      Equiv.apply_symm_apply] at hi
    exact hi
  · apply Ideal.span_le.2
    rintro x ⟨i, rfl⟩
    have hi := ht Z k hk.2 (d.symm i)
    have hn := (τ.s (d.symm i)).property
      (Over.homMk (U := Over.mk (k ≫ b)) (V := Over.mk b) k rfl).op
    change I.val.map k.op ((τ.s (d.symm i)).val (op (Over.mk b))) = _ at hn
    rw [hn, generatingList_section_value O I ι V s g τ d hd Z (k ≫ b),
      Equiv.apply_symm_apply] at hi
    exact hi

end CategoryTheory
