/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.CategoryTheory.Functor.OfSequence
import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLEGT
import WeilConjectures.CategoryTheory.Triangulated.ProZeroMiddle

/-!
# Uniformly bounded derived towers with pro-zero cohomology

Source: Stacks Project, Derived Categories, Tag 0G3B, specialized to zero-valued systems
(auxiliary; not a blueprint node).
-/

@[expose] public section

universe w v u

open CategoryTheory CategoryTheory.Limits Opposite

namespace DerivedCategory

private lemma map_eq_zero_of_single_degree
    {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]
    {K L : DerivedCategory A} (r : ℤ)
    [K.IsGE r] [K.IsLE r] [L.IsGE r] [L.IsLE r]
    (f : K ⟶ L) (hf : (homologyFunctor A r).map f = 0) : f = 0 := by
  obtain ⟨M, ⟨e⟩⟩ := exists_iso_singleFunctor_obj_of_isGE_of_isLE K r
  obtain ⟨N, ⟨e'⟩⟩ := exists_iso_singleFunctor_obj_of_isGE_of_isLE L r
  obtain ⟨g, hg⟩ := (singleFunctor A r).map_surjective (e.inv ≫ f ≫ e'.hom)
  have : (singleFunctor A r ⋙ homologyFunctor A r).Faithful :=
    Functor.Faithful.of_iso (singleFunctorCompHomologyFunctorIso A r).symm
  have hz : (singleFunctor A r ⋙ homologyFunctor A r).map g = 0 := by
    dsimp only [Functor.comp_map]
    rw [hg, Functor.map_comp, Functor.map_comp, hf]
    simp
  have hg0 : g = 0 := by
    apply (singleFunctor A r ⋙ homologyFunctor A r).map_injective
    simpa using hz
  rw [hg0, Functor.map_zero] at hg
  apply (cancel_epi e.inv).1
  apply (cancel_mono e'.hom).1
  simpa using hg.symm

private lemma homology_truncLEι_mono
    {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]
    (K : DerivedCategory A) (a q : ℤ) (hq : q ≤ a) :
    Mono ((homologyFunctor A q).map ((TStructure.t.truncLEι a).app K)) := by
  let T := (TStructure.t.triangleLEGE a (a + 1) rfl).obj K
  have hT := TStructure.t.triangleLEGE_distinguished a (a + 1) rfl K
  have : T.obj₃.IsGE (a + 1) := TStructure.t.isGE_truncGE_obj K (a + 1) (a + 1)
  apply (HomologySequence.mono_homologyMap_mor₁_iff T hT (q - 1) q (by omega)).2
  exact (isZero_of_isGE T.obj₃ (a + 1) (q - 1) (by omega)).eq_of_src _ _

private lemma homology_truncGEπ_epi
    {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]
    (K : DerivedCategory A) (a q : ℤ) (hq : a < q) :
    Epi ((homologyFunctor A q).map ((TStructure.t.truncGEπ (a + 1)).app K)) := by
  let T := (TStructure.t.triangleLEGE a (a + 1) rfl).obj K
  have hT := TStructure.t.triangleLEGE_distinguished a (a + 1) rfl K
  have : T.obj₁.IsLE a := TStructure.t.isLE_truncLE_obj K a a
  apply (HomologySequence.epi_homologyMap_mor₂_iff T hT q (q + 1) rfl).2
  exact (isZero_of_isLE T.obj₁ a (q + 1) (by omega)).eq_of_tgt _ _

private lemma homology_truncLE_map_zero
    {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]
    {K L : DerivedCategory A} (f : K ⟶ L) (a q : ℤ) (hq : q ≤ a)
    (hf : (homologyFunctor A q).map f = 0) :
    (homologyFunctor A q).map ((TStructure.t.truncLE a).map f) = 0 := by
  have := homology_truncLEι_mono L a q hq
  apply (cancel_mono ((homologyFunctor A q).map ((TStructure.t.truncLEι a).app L))).1
  rw [zero_comp, ← Functor.map_comp, (TStructure.t.truncLEι a).naturality]
  simp only [Functor.map_comp, Functor.id_map, hf, comp_zero]

private lemma homology_truncGE_map_zero
    {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]
    {K L : DerivedCategory A} (f : K ⟶ L) (a q : ℤ) (hq : a < q)
    (hf : (homologyFunctor A q).map f = 0) :
    (homologyFunctor A q).map ((TStructure.t.truncGE (a + 1)).map f) = 0 := by
  have := homology_truncGEπ_epi K a q hq
  apply (cancel_epi
    ((homologyFunctor A q).map ((TStructure.t.truncGEπ (a + 1)).app K))).1
  rw [comp_zero, ← Functor.map_comp, ← (TStructure.t.truncGEπ (a + 1)).naturality]
  simp only [Functor.map_comp, Functor.id_map, hf, zero_comp]

/-- A uniformly bounded tower whose cohomology towers are pro-zero is itself pro-zero.
The index `n : ℕ` represents the paper's index `n + 1`; the functor laws encode identity
and composition of all transition maps.

Source: Stacks Project, Derived Categories, Tag 0G3B
(auxiliary; not a blueprint node).

Proof plan: for a fixed target index choose a later index dominating the finitely many
indices killing the cohomology maps in degrees `[a, b]`; outside this interval cohomology
is zero. Apply the functorial canonical truncation triangle at `a`
(lem-sf-derived-truncation-triangle). Its lower term is `H^a(X)[-a]`, since lower
cohomology vanishes, and its transitions are the shifted cohomology maps. The upper
terms have cohomology in `[a + 1, b]`. Induct on `b - a`; for `a = b` use the
single-degree identification (lem-sf-derived-concentrated-single). In the induction
step both outer towers are pro-zero, so the zero-valued two-out-of-three lemma
(lem-weil-pbc-essentially-constant-zero-triangle, Tag 0G3A) makes the middle tower
pro-zero. -/
theorem tower_proZero_of_bounded_homology_proZero
    {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]
    (X : ℕᵒᵖ ⥤ DerivedCategory A) (a b : ℤ) (hab : a ≤ b)
    (hbounded : ∀ (n : ℕ) (q : ℤ), q < a ∨ b < q →
      IsZero ((homologyFunctor A q).obj (X.obj (op n))))
    (hpro : ∀ (q : ℤ) (n : ℕ), ∃ (k : ℕ) (h : n ≤ k),
      (homologyFunctor A q).map (X.map (homOfLE h).op) = 0) :
    ∀ (n : ℕ), ∃ (k : ℕ) (h : n ≤ k), X.map (homOfLE h).op = 0 := by
  generalize hd : (b - a).toNat = d
  induction d generalizing X a b with
  | zero =>
    have hba : b = a := by omega
    subst b
    intro n
    obtain ⟨k, hnk, hk⟩ := hpro a n
    have : (X.obj (op k)).IsGE a :=
      (isGE_iff _ _).2 (fun q hq ↦ hbounded k q (Or.inl hq))
    have : (X.obj (op k)).IsLE a :=
      (isLE_iff _ _).2 (fun q hq ↦ hbounded k q (Or.inr hq))
    have : (X.obj (op n)).IsGE a :=
      (isGE_iff _ _).2 (fun q hq ↦ hbounded n q (Or.inl hq))
    have : (X.obj (op n)).IsLE a :=
      (isLE_iff _ _).2 (fun q hq ↦ hbounded n q (Or.inr hq))
    exact ⟨k, hnk, map_eq_zero_of_single_degree a _ hk⟩
  | succ d ih =>
    have hab' : a + 1 ≤ b := by omega
    let Y := X ⋙ TStructure.t.truncGE (a + 1)
    have hYbounded : ∀ (n : ℕ) (q : ℤ), q < a + 1 ∨ b < q →
        IsZero ((homologyFunctor A q).obj (Y.obj (op n))) := by
      intro n q hq
      have : (X.obj (op n)).IsLE b :=
        (isLE_iff _ _).2 (fun q hq ↦ hbounded n q (Or.inr hq))
      have : (Y.obj (op n)).IsGE (a + 1) :=
        TStructure.t.isGE_truncGE_obj _ _ _
      have : (Y.obj (op n)).IsLE b := by
        change TStructure.t.IsLE ((TStructure.t.truncGE (a + 1)).obj _) b
        infer_instance
      rcases hq with hq | hq
      · exact isZero_of_isGE _ (a + 1) q hq
      · exact isZero_of_isLE _ b q hq
    have hYpro : ∀ (q : ℤ) (n : ℕ), ∃ (k : ℕ) (h : n ≤ k),
        (homologyFunctor A q).map (Y.map (homOfLE h).op) = 0 := by
      intro q n
      by_cases hq : a < q
      · obtain ⟨k, hnk, hk⟩ := hpro q n
        exact ⟨k, hnk, homology_truncGE_map_zero _ a q hq hk⟩
      · refine ⟨n, le_rfl, ?_⟩
        exact (hYbounded n q (Or.inl (by omega))).eq_of_tgt _ _
    have hY := ih Y (a + 1) b hab' hYbounded hYpro (by omega)
    let T := X ⋙ TStructure.t.triangleLEGE a (a + 1) rfl
    apply Pretriangulated.proZero_middle_of_distinguished_tower T
      (fun n ↦ TStructure.t.triangleLEGE_distinguished a (a + 1) rfl (X.obj (op n)))
    intro n
    obtain ⟨m, hnm, hm⟩ := hpro a n
    have hlow : (TStructure.t.truncLE a).map (X.map (homOfLE hnm).op) = 0 := by
      have : (X.obj (op m)).IsGE a :=
        (isGE_iff _ _).2 (fun q hq ↦ hbounded m q (Or.inl hq))
      have : (X.obj (op n)).IsGE a :=
        (isGE_iff _ _).2 (fun q hq ↦ hbounded n q (Or.inl hq))
      have : ((TStructure.t.truncLE a).obj (X.obj (op m))).IsGE a := by
        infer_instance
      have : ((TStructure.t.truncLE a).obj (X.obj (op n))).IsGE a := by
        infer_instance
      have : ((TStructure.t.truncLE a).obj (X.obj (op m))).IsLE a :=
        TStructure.t.isLE_truncLE_obj _ _ _
      have : ((TStructure.t.truncLE a).obj (X.obj (op n))).IsLE a :=
        TStructure.t.isLE_truncLE_obj _ _ _
      apply map_eq_zero_of_single_degree a
      exact homology_truncLE_map_zero _ a a le_rfl hm
    obtain ⟨k, hnk, hk⟩ := hY n
    let l := max m k
    have hnl : n ≤ l := hnm.trans (le_max_left _ _)
    have hcompm : (homOfLE hnl).op =
        (homOfLE (le_max_left m k)).op ≫ (homOfLE hnm).op := Subsingleton.elim _ _
    have hcompk : (homOfLE hnl).op =
        (homOfLE (le_max_right m k)).op ≫ (homOfLE hnk).op := Subsingleton.elim _ _
    refine ⟨l, hnl, ?_, ?_⟩
    · change (TStructure.t.truncLE a).map (X.map (homOfLE hnl).op) = 0
      rw [hcompm, X.map_comp, Functor.map_comp, hlow, comp_zero]
    · change Y.map (homOfLE hnl).op = 0
      rw [hcompk, Y.map_comp, hk, comp_zero]

end DerivedCategory
