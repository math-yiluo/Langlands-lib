/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Ample
import WeilConjectures.AlgebraicGeometry.AffineCapSectionOpen
import WeilConjectures.AlgebraicGeometry.Ample.AmpleFiniteSetAffine
import WeilConjectures.AlgebraicGeometry.AmpleIdealSection
import WeilConjectures.AlgebraicGeometry.Closed.ClosedSubsetQcIdeal
import WeilConjectures.RingTheory.GradedPrimeAvoidance
import WeilConjectures.AlgebraicGeometry.AmpleProjCanonicalMap
import WeilConjectures.AlgebraicGeometry.Modules.ProjectionFormula

/-! # Affine section neighbourhoods of finite sets

Source: Stacks Project, Properties, Lemma 09NV
(blueprint: lem-sc-ample-finite-principal-affine).
-/

@[expose] public section

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- An ample invertible module has a positive-power section with affine nonvanishing locus
containing a prescribed finite set and contained in a prescribed open neighbourhood.
Source: Stacks Project, Properties, Lemma 09NV
(blueprint: lem-sc-ample-finite-principal-affine).

Proof: For nonempty `E`, choose an affine open `U'` containing `E` using
`lem-sc-ample-finite-set-affine` (01ZY), and put `U = U' ∩ W`.
In the graded section ring, consider the homogeneous primes of sections vanishing at
points of `E` and the positive-degree ideal of sections vanishing outside `U`.
Use `lem-sc-closed-subset-qc-ideal` to realize the complement by an ideal sheaf.
Quasi-compactness, supplied by ampleness, and `lem-sc-ample-ideal-section` give a section
of this ideal times a positive tensor power nonvanishing at each individual point of `E`.
Thus the graded ideal is contained in none of those primes. Apply
`lem-sc-graded-prime-avoidance` (00JS) to obtain one positive-degree homogeneous section
avoiding all of them. Its nonvanishing locus contains `E` and lies in `U`, hence in `W`.
It is affine by `lem-sc-affine-cap-section-open` (01PV), since it lies in the affine `U'`.
For empty `E`, use the zero section of the first tensor power; its locus is empty and affine.
-/
theorem exists_affine_section_neighbourhood_of_finite
    (Y : Scheme.{u}) (M : Y.Modules) [M.IsInvertible] (hM : IsAmple Y M)
    (E : Set Y) (hE : E.Finite) (W : Y.Opens) (hEW : E ⊆ (W : Set Y)) :
    ∃ n : ℕ, 0 < n ∧
      ∃ s : (M.tensorPow n).val.presheaf.obj (Opposite.op ⊤), ∃ U : Y.Opens,
        E ⊆ (U : Set Y) ∧ U ≤ W ∧ IsAffineOpen U ∧
          ∀ y : Y, y ∈ U ↔
            (TopCat.Presheaf.germ (M.tensorPow n).val.presheaf ⊤ y trivial) s ∉
              (IsLocalRing.maximalIdeal (Y.presheaf.stalk y)) •
                (⊤ : Submodule (Y.presheaf.stalk y)
                  ↑(TopCat.Presheaf.stalk (M.tensorPow n).val.presheaf y)) := by
  open CategoryTheory MonoidalCategory in
  classical
  obtain ⟨A, hA, hEA⟩ := Scheme.exists_affineOpen_of_isAmple Y M hM E hE
  let B : Y.Opens := A ⊓ W
  obtain ⟨J, hJ⟩ := Scheme.exists_idealSheafData_support_eq Y
    (B : Set Y)ᶜ B.isOpen.isClosed_compl
  have hcover : ∀ y : Y, ∃ (d : ℕ) (s : sectionRingGrade M d),
      0 < d ∧ y ∈ nonvanishingLocus (M.tensorPow d) (s.val d) := by
    intro y
    obtain ⟨d, hd, s, V, hyV, _, hV⟩ := hM.2 y
    let x : InvertibleSectionRing M := DirectSum.of (SectionRingComponent M) d s
    have hx : x ∈ sectionRingGrade M d := ⟨s, rfl⟩
    refine ⟨d, ⟨x, hx⟩, hd, ?_⟩
    change y ∈ nonvanishingLocus (M.tensorPow d)
      ((DirectSum.of (SectionRingComponent M) d) s d)
    rw [DirectSum.of_eq_same]
    exact (hV y).1 hyV
  obtain ⟨f, hf⟩ := exists_sectionRing_proj_morphism Y M hcover
  let p (y : Y) : HomogeneousIdeal (sectionRingGrade M) := (f y).asHomogeneousIdeal
  have hp (y : Y) : (p y).toIdeal.IsPrime := (f y).isPrime
  have hpmem (y : Y) (n : ℕ) (hn : 0 < n) (x : InvertibleSectionRing M)
      (hx : x ∈ sectionRingGrade M n) :
      x ∈ p y ↔ y ∉ nonvanishingLocus (M.tensorPow n) (x n) := by
    have hset := (hf n hn ⟨x, hx⟩).1
    have hpoint := Set.ext_iff.mp hset y
    change (x ∉ p y) ↔ y ∈ nonvanishingLocus (M.tensorPow n) (x n) at hpoint
    exact ⟨fun hx hy ↦ (hpoint.2 hy) hx,
      fun hy ↦ not_not.mp (fun hx ↦ hy (hpoint.1 hx))⟩
  let I : HomogeneousIdeal (sectionRingGrade M) :=
    HomogeneousIdeal.irrelevant (sectionRingGrade M) ⊓
      ⨅ z : {y : Y // y ∉ B}, p z.val
  have hI : I ≤ HomogeneousIdeal.irrelevant (sectionRingGrade M) := inf_le_left
  have hIpoint (x : InvertibleSectionRing M) (hx : x ∈ I) (y : Y)
      (hy : y ∉ B) : x ∈ p y :=
    (show I ≤ p y from inf_le_right.trans
      (iInf_le (fun z : {y : Y // y ∉ B} ↦ p z.val) ⟨y, hy⟩)) hx
  have hvanish (J : Y.IdealSheafData) (N : Y.Modules) [N.IsInvertible]
      (v : Γ(J.toModules.tensorObj N, ⊤)) :
      nonvanishingLocus N
        (((tensorHom J.toModulesι (𝟙 N) ≫
          (leftUnitor N).hom).app ⊤) v) ⊆
            (J.support : Set Y)ᶜ := by
    intro y hy hyJ
    have := Scheme.Modules.IsInvertible.sheafOfModules_isInvertible N
    obtain ⟨U, hyU, _, e, he⟩ := Scheme.Modules.exists_isFreeGenerator N (x := y)
      (W := ⊤) trivial
    obtain ⟨a, ha⟩ := (he.bijective_tmulSection_right (M := J.toModules) le_rfl).2
      ((J.toModules.tensorObj N).presheaf.map (homOfLE (le_top : U.1 ≤ ⊤)).op v)
    have ha' : Scheme.Modules.tmulSection a e =
        (J.toModules.tensorObj N).presheaf.map (homOfLE (le_top : U.1 ≤ ⊤)).op v := by
      simpa using ha
    let c : Γ(Y, U.1) := J.toModulesι.app U.1 a
    have hc : c ∈ J.ideal U := (J.range_toModulesι_app U).subset ⟨a, rfl⟩
    have hyc : y ∉ Y.basicOpen c :=
      (Y.mem_zeroLocus_iff _ y).1 ((J.mem_support_iff_of_mem hyU).1 hyJ) c hc
    have hcgerm : Y.presheaf.germ U.1 y hyU c ∈
        IsLocalRing.maximalIdeal (Y.presheaf.stalk y) := by
      rw [IsLocalRing.mem_maximalIdeal]
      exact fun hunit ↦ hyc ((Y.mem_basicOpen c y hyU).2 hunit)
    let φ := tensorHom J.toModulesι (𝟙 N) ≫ (leftUnitor N).hom
    have hres : N.presheaf.map (homOfLE (le_top : U.1 ≤ ⊤)).op (φ.app ⊤ v) = c • e := by
      rw [← Scheme.Modules.Hom.app_presheaf_map, ← ha', Scheme.Modules.Hom.comp_app,
        ConcreteCategory.comp_apply, Scheme.Modules.tensorHom_app_tmulSection]
      simp only [Scheme.Modules.Hom.id_app, ConcreteCategory.id_apply]
      erw [Scheme.Modules.leftUnitor_hom_app_tmulSection']
      rfl
    apply hy
    change (TopCat.Presheaf.germ N.val.presheaf ⊤ y trivial) (φ.app ⊤ v) ∈ _
    rw [← TopCat.Presheaf.germ_res_apply N.val.presheaf
      (homOfLE (le_top : U.1 ≤ ⊤)) y hyU]
    erw [hres]
    rw [PresheafOfModules.germ_smul (R := Y.presheaf) N.val]
    exact Submodule.smul_mem_smul hcgerm (Submodule.mem_top)
  have hnotle (y : Y) (hy : y ∈ B) : ¬ I ≤ p y := by
    have : CompactSpace Y := hM.1
    have hyJ : y ∉ (J.support : Set Y) := by
      rw [hJ]
      exact not_not_intro hy
    obtain ⟨n, hn, s, v, hsv, hys⟩ := J.exists_section_of_ample_ideal M hM hyJ
    have hsB : nonvanishingLocus (M.tensorPow n) s ⊆ (B : Set Y) := by
      intro z hz
      have hzJ := hvanish J (M.tensorPow n) v
      rw [← hsv, hJ] at hzJ
      exact not_not.mp (hzJ hz)
    let x : InvertibleSectionRing M := DirectSum.of (SectionRingComponent M) n s
    have hxgrade : x ∈ sectionRingGrade M n := ⟨s, rfl⟩
    have hxn : x n = s :=
      DirectSum.of_eq_same (β := SectionRingComponent M) n s
    have hxI : x ∈ I := by
      change x ∈ HomogeneousIdeal.irrelevant (sectionRingGrade M) ∧
        x ∈ (⨅ z : {y : Y // y ∉ B}, p z.val)
      refine ⟨HomogeneousIdeal.mem_irrelevant_of_mem (sectionRingGrade M) hn hxgrade, ?_⟩
      change x ∈ (⨅ z : {y : Y // y ∉ B}, p z.val).toIdeal
      rw [HomogeneousIdeal.toIdeal_iInf]
      simp only [Ideal.mem_iInf]
      intro z
      apply (hpmem z.val n hn x hxgrade).2
      rw [hxn]
      exact fun hz ↦ z.property (hsB hz)
    intro hle
    have hyvan := (hpmem y n hn x hxgrade).1 (hle hxI)
    rw [hxn] at hyvan
    exact hyvan hys
  let : Fintype E := hE.fintype
  let e : Fin (Fintype.card E) ≃ E := (Fintype.equivFin E).symm
  obtain ⟨n, hn, x, hxgrade, hxI, hxavoid⟩ :=
    HomogeneousIdeal.exists_homogeneous_mem_notMem_of_isPrime (sectionRingGrade M)
      (Fintype.card E) (fun i ↦ p (e i).val) (fun i ↦ hp (e i).val) I hI
      (fun i ↦ hnotle (e i).val ⟨hEA (e i).property, hEW (e i).property⟩)
  have hsB : nonvanishingLocus (M.tensorPow n) (x n) ⊆ (B : Set Y) := by
    intro y hy
    by_contra hyB
    exact (hpmem y n hn x hxgrade).1 (hIpoint x hxI y hyB) hy
  have hEs : E ⊆ nonvanishingLocus (M.tensorPow n) (x n) := by
    intro y hy
    have havoid : x ∉ p y := by
      simpa only [e.apply_symm_apply] using hxavoid (e.symm ⟨y, hy⟩)
    exact not_not.mp (fun hvan ↦ havoid ((hpmem y n hn x hxgrade).2 hvan))
  obtain ⟨U, hU, hUmem⟩ :=
    (affine_cap_section_open Y M (0 : M.val.presheaf.obj (Opposite.op ⊤)) A hA).2
      n hn (x n)
  refine ⟨n, hn, x n, U, ?_, ?_, hU, ?_⟩
  · intro y hy
    exact (hUmem y).2 ⟨hEA hy, hEs hy⟩
  · intro y hy
    exact (hsB ((hUmem y).1 hy).2).2
  · intro y
    exact (hUmem y).trans ⟨And.right, fun hy ↦ ⟨(hsB hy).1, hy⟩⟩

end AlgebraicGeometry.Scheme.Modules
