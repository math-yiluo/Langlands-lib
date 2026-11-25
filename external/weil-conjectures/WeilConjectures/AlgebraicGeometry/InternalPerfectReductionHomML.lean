/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Internal.InternalPerfectReductionHomData
public import WeilConjectures.AlgebraicGeometry.FiniteConstantModel.FiniteConstantModelResolutionSupplement
public import WeilConjectures.AlgebraicGeometry.AdmissibleScalarRealization.AdmissibleScalarRealizationExactSupplement
public import WeilConjectures.CategoryTheory.DerivedCategory.Perfect
public import Mathlib.CategoryTheory.Monoidal.Mod
public import Mathlib.CategoryTheory.Sites.Monoidal
public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import Mathlib.CategoryTheory.Monoidal.Preadditive
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Preadditive
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Sites.Localization
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Sites.Sheafification
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
public import WeilConjectures.CategoryTheory.Sites.WeaklyContractible
public import WeilConjectures.Algebra.Homology.ModuleHomComplex
public import Mathlib.Algebra.Category.ModuleCat.Ulift
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import Mathlib.Algebra.Homology.TotalComplex
public import Mathlib.CategoryTheory.CofilteredSystem
public import Mathlib.Algebra.Module.Torsion.Basic

import WeilConjectures.AlgebraicGeometry.InternalPerfectDualTensorFinite
import WeilConjectures.CategoryTheory.FiniteTripleMittagLeffler
import WeilConjectures.AlgebraicGeometry.InternalPerfectEndomorphismQuotientComparison
import Mathlib.CategoryTheory.CofilteredSystem

/-! # Uniform stable images for internal perfect reduction Hom

Source: literature/stacks-project/proetale.tex, Tag 09C5;
current blueprint proposition-local-structure-integral-constructible-complexes, Compatible
isomorphisms, paragraph beginning These Hom groups can be infinite
(blueprint: lem-pe-internal-perfect-reduction-hom-ml).

Natural-number index n denotes the positive exponent n+1. The scalar model uses
constant discrete scalar modules extended to continuous integral coefficients.
The Hom transitions use the actual quotient-associativity comparisons.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
namespace AlgebraicGeometry.ProEtale

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]


private theorem functor_conjugate_id {C D : Type*} [Category* C] [Category* D]
    (F : C ⥤ D) (Z : C) {W : D} (e : F.obj Z ≅ W) :
    e.inv ≫ F.map (𝟙 Z) ≫ e.hom = 𝟙 W := by
  simp only [CategoryTheory.Functor.map_id, Category.id_comp, Iso.inv_hom_id]

private theorem homStep_id
    (W : Scheme.{u})
    (T : DerivedCategory (AdicCompletion.Modules l E W)) (n : ℕ) :
    internalReductionHomStep l E W T T n (𝟙 _) = 𝟙 _ := by
  exact functor_conjugate_id (AdicCompletion.finiteExtend l E W n)
    ((AdicCompletion.derivedReduction l E W (n + 1)).obj T)
    ((AdicCompletion.reductionComp l E W n).app T)

private theorem homStep_comp
    (W : Scheme.{u})
    (T M N : DerivedCategory (AdicCompletion.Modules l E W)) (n : ℕ)
    (a : (AdicCompletion.derivedReduction l E W (n + 1)).obj T ⟶
      (AdicCompletion.derivedReduction l E W (n + 1)).obj M)
    (b : (AdicCompletion.derivedReduction l E W (n + 1)).obj M ⟶
      (AdicCompletion.derivedReduction l E W (n + 1)).obj N) :
    internalReductionHomStep l E W T N n (a ≫ b) =
      internalReductionHomStep l E W T M n a ≫ internalReductionHomStep l E W M N n b := by
  simp [internalReductionHomStep, Category.assoc]

private theorem homTower_map_id
    (W : Scheme.{u})
    (T : DerivedCategory (AdicCompletion.Modules l E W))
    {n m : ℕᵒᵖ} (f : m ⟶ n) :
    (internalReductionHomTower l E W T T).map f (𝟙 _) = 𝟙 _ := by
  obtain ⟨n⟩ := n
  obtain ⟨m⟩ := m
  have hnm : n ≤ m := leOfHom f.unop
  obtain rfl : f = (homOfLE hnm).op := Subsingleton.elim _ _
  induction m, hnm using Nat.le_induction with
  | base => simp
  | succ m hnm ih =>
    have he : (homOfLE (hnm.trans (Nat.le_succ m))).op =
        (homOfLE (Nat.le_succ m)).op ≫ (homOfLE hnm).op := Subsingleton.elim _ _
    rw [he, Functor.map_comp]
    simp only [types_comp_apply]
    have hs : (internalReductionHomTower l E W T T).map
        (homOfLE (Nat.le_succ m)).op (𝟙 _) = 𝟙 _ := by
      dsimp only [internalReductionHomTower]
      rw [Functor.ofOpSequence_map_homOfLE_succ]
      exact homStep_id l E W T m
    rw [hs, ih]

private theorem homTower_map_comp
    (W : Scheme.{u})
    (T M N : DerivedCategory (AdicCompletion.Modules l E W))
    {n m : ℕᵒᵖ} (f : m ⟶ n)
    (a : (internalReductionHomTower l E W T M).obj m)
    (b : (internalReductionHomTower l E W M N).obj m) :
    (internalReductionHomTower l E W T N).map f (a ≫ b) =
      (internalReductionHomTower l E W T M).map f a ≫
        (internalReductionHomTower l E W M N).map f b := by
  obtain ⟨n⟩ := n
  obtain ⟨m⟩ := m
  have hnm : n ≤ m := leOfHom f.unop
  obtain rfl : f = (homOfLE hnm).op := Subsingleton.elim _ _
  induction m, hnm using Nat.le_induction with
  | base => simp
  | succ m hnm ih =>
    have he : (homOfLE (hnm.trans (Nat.le_succ m))).op =
        (homOfLE (Nat.le_succ m)).op ≫ (homOfLE hnm).op := Subsingleton.elim _ _
    simp only [he, Functor.map_comp, types_comp_apply]
    have hs : (internalReductionHomTower l E W T N).map
        (homOfLE (Nat.le_succ m)).op (a ≫ b) =
        (internalReductionHomTower l E W T M).map (homOfLE (Nat.le_succ m)).op a ≫
        (internalReductionHomTower l E W M N).map (homOfLE (Nat.le_succ m)).op b := by
      dsimp only [internalReductionHomTower]
      rw [Functor.ofOpSequence_map_homOfLE_succ,
        Functor.ofOpSequence_map_homOfLE_succ, Functor.ofOpSequence_map_homOfLE_succ]
      exact homStep_comp l E W T M N m a b
    rw [hs]
    exact ih _ _

private def homTower_mapIso
    (W : Scheme.{u})
    (T M : DerivedCategory (AdicCompletion.Modules l E W))
    {n m : ℕᵒᵖ} (f : m ⟶ n)
    (e : (AdicCompletion.derivedReduction l E W m.unop).obj T ≅
      (AdicCompletion.derivedReduction l E W m.unop).obj M) :
    (AdicCompletion.derivedReduction l E W n.unop).obj T ≅
      (AdicCompletion.derivedReduction l E W n.unop).obj M where
  hom := (internalReductionHomTower l E W T M).map f e.hom
  inv := (internalReductionHomTower l E W M T).map f e.inv
  hom_inv_id := by
    rw [← homTower_map_comp, e.hom_inv_id, homTower_map_id]
  inv_hom_id := by
    rw [← homTower_map_comp, e.inv_hom_id, homTower_map_id]

private theorem homTower_finiteComparison
    (W : Scheme.{u})
    (T M : DerivedCategory (AdicCompletion.Modules l E W))
    (he : ∀ n : ℕ, Nonempty ((AdicCompletion.derivedReduction l E W n).obj T ≅
      (AdicCompletion.derivedReduction l E W n).obj M)) :
    Functor.FiniteTripleRangeComparison (internalReductionHomTower l E W T M)
      (internalReductionHomTower l E W T T) := by
  intro n m t f g
  obtain ⟨e⟩ := he t.unop
  let em := homTower_mapIso l E W T M g e
  let en := homTower_mapIso l E W T M (g ≫ f) e
  have hbij : ∀ {n : ℕ} (a : (AdicCompletion.derivedReduction l E W n).obj T ≅
      (AdicCompletion.derivedReduction l E W n).obj M),
      Function.Bijective (fun x : (internalReductionHomTower l E W T M).obj (op n) ↦
        x ≫ a.inv) := by
    intro n a
    constructor
    · intro x y h
      have h' := congrArg (fun k ↦ k ≫ a.hom) h
      simpa only [Category.assoc, a.inv_hom_id, Category.comp_id] using h'
    · intro x
      refine ⟨x ≫ a.hom, ?_⟩
      simp only [Category.assoc, a.hom_inv_id, Category.comp_id]
  refine ⟨(fun x ↦ x ≫ en.inv), (fun x ↦ x ≫ em.inv), (fun x ↦ x ≫ e.inv),
    hbij en, hbij em, hbij e, ?_, ?_⟩
  · intro x
    rw [homTower_map_comp]
    change _ ≫ (internalReductionHomTower l E W M T).map (g ≫ f) e.inv =
      _ ≫ (internalReductionHomTower l E W M T).map f
        ((internalReductionHomTower l E W M T).map g e.inv)
    rw [Functor.map_comp]
    rfl
  · intro x
    exact (homTower_map_comp l E W T M T (g ≫ f) x e.inv).symm


private theorem finiteComparison_range_eq
    {J : Type*} [Category J] {F G : J ⥤ Type*}
    (h : Functor.FiniteTripleRangeComparison F G)
    {n m N : J} (f : m ⟶ n) (g : N ⟶ m)
    (heq : Set.range (G.map (g ≫ f)) = Set.range (G.map f)) :
    Set.range (F.map (g ≫ f)) = Set.range (F.map f) := by
  obtain ⟨en, em, eN, hen, hem, heN, hf, hgf⟩ := h f g
  apply Set.Subset.antisymm
  · rintro y ⟨x, rfl⟩
    obtain ⟨z, hz⟩ := heq.subset ⟨eN x, (hgf x).symm⟩
    obtain ⟨w, hw⟩ := hem.surjective z
    refine ⟨w, hen.injective ?_⟩
    rw [hf, hw]
    exact hz
  · rintro y ⟨x, rfl⟩
    obtain ⟨z, hz⟩ := heq.symm.subset ⟨em x, (hf x).symm⟩
    obtain ⟨w, hw⟩ := heN.surjective z
    refine ⟨w, hen.injective ?_⟩
    rw [hgf, hw]
    exact hz

private theorem uniformRange_mittagLeffler (F : ℕᵒᵖ ⥤ Type*) (e : ℕ)
    (h : ∀ (n m N : ℕ) (hnm : n + e ≤ m) (hmN : m ≤ N),
      Set.range (F.map (homOfLE
        ((Nat.le_add_right n e).trans (hnm.trans hmN))).op) =
      Set.range (F.map (homOfLE ((Nat.le_add_right n e).trans hnm)).op)) :
    F.IsMittagLeffler := by
  apply (Functor.isMittagLeffler_iff_subset_range_comp F).2
  intro n
  refine ⟨op (n.unop + e), (homOfLE (Nat.le_add_right n.unop e)).op, ?_⟩
  intro N g
  have hN : n.unop + e ≤ N.unop := leOfHom g.unop
  have hh := h n.unop (n.unop + e) N.unop le_rfl hN
  have hg : g ≫ (homOfLE (Nat.le_add_right n.unop e)).op =
      (homOfLE ((Nat.le_add_right n.unop e).trans (le_rfl.trans hN))).op :=
    Subsingleton.elim _ _
  rw [hg, hh]

private theorem homTower_uniformRange
    (W : Scheme.{u}) (T K : DerivedCategory (AdicCompletion.Modules l E W))
    (he : ∀ n : ℕ, Nonempty ((AdicCompletion.derivedReduction l E W n).obj T ≅
      (AdicCompletion.derivedReduction l E W n).obj K))
    (e : ℕ)
    (h : ∀ (n m N : ℕ) (hnm : n + e ≤ m) (hmN : m ≤ N),
      Set.range ((internalReductionHomTower l E W T T).map (homOfLE
        ((Nat.le_add_right n e).trans (hnm.trans hmN))).op) =
      Set.range ((internalReductionHomTower l E W T T).map
        (homOfLE ((Nat.le_add_right n e).trans hnm)).op)) :
    ∀ (n m N : ℕ) (hnm : n + e ≤ m) (hmN : m ≤ N),
      Set.range ((internalReductionHomTower l E W T K).map (homOfLE
        ((Nat.le_add_right n e).trans (hnm.trans hmN))).op) =
      Set.range ((internalReductionHomTower l E W T K).map
        (homOfLE ((Nat.le_add_right n e).trans hnm)).op) := by
  intro n m N hnm hmN
  have hcomp : (homOfLE hmN).op ≫
      (homOfLE ((Nat.le_add_right n e).trans hnm)).op =
      (homOfLE ((Nat.le_add_right n e).trans (hnm.trans hmN))).op :=
    Subsingleton.elim _ _
  have hh := finiteComparison_range_eq (homTower_finiteComparison l E W T K he)
    (homOfLE ((Nat.le_add_right n e).trans hnm)).op (homOfLE hmN).op
  rw [hcomp] at hh
  exact hh (h n m N hnm hmN)

private theorem locallyConstant_range_eq {Y : Type*} [TopologicalSpace Y]
    {A B C : Type*} (f : A → C) (g : B → C)
    (h : Set.range f = Set.range g) :
    Set.range (LocallyConstant.map (X := Y) f) =
      Set.range (LocallyConstant.map (X := Y) g) := by
  classical
  apply Set.Subset.antisymm
  · rintro y ⟨x, rfl⟩
    have hlift : ∀ a : A, ∃ b : B, g b = f a := fun a ↦ h.subset ⟨a, rfl⟩
    choose lift hlift using hlift
    refine ⟨LocallyConstant.map lift x, ?_⟩
    ext t
    exact hlift (x t)
  · rintro y ⟨x, rfl⟩
    have hlift : ∀ b : B, ∃ a : A, f a = g b := fun b ↦ h.symm.subset ⟨b, rfl⟩
    choose lift hlift using hlift
    refine ⟨LocallyConstant.map lift x, ?_⟩
    ext t
    exact hlift (x t)

/-- Uniform stable images for the internal perfect reduction Hom tower, hence ML.
Source: literature/stacks-project/proetale.tex, Tag 09C5; current blueprint
proposition-local-structure-integral-constructible-complexes, Compatible isomorphisms, uniform-bound
paragraph (blueprint: lem-pe-internal-perfect-reduction-hom-ml).

Proof:
1. Identify the site over W with W_proet by weakly-etale localization. The DVR and
finite-quotient lemmas identify each internal finite-coefficient module category with
ordinary modules over the constant finite quotient ring, on arbitrary schemes.
2. Choose bases of P. Internal-section tensor comparison and bounded-flat K-flatness
represent its derived reductions by constant P/pi^j. Pure-tensor normalization makes
these identifications respect quotient associativity and the actual comparisons.
3. Weak contractibility makes sections exact. Bounded free constant complexes are
K-projective; the K-projective derived-Hom bijection computes maps modulo homotopy.
4. Signed finite-free evaluation identifies their Hom complexes with constant Q/pi^j.
The formula on homogeneous tensors is lambda tensor v applied to x equals
(-1)^(degree(v)*degree(x)) lambda(x)v. Its differential is df=d_P f-(-1)^degree(f)f d_P.
Degree-zero cycles are chain maps and boundaries are null-homotopic maps.
5. Exact constant sheafification and exact sections preserve cohomology and images.
6. In bases, actual derived coefficient extension reduces each chain-map matrix entry.
It also reduces homotopies, so this identification respects every finite reduction diagram.
7. For N >= m >= n+e choose only one isomorphism at level N and reduce it to m and n.
Postcomposition by those reductions identifies both Hom images with the endomorphism
images using one common bijection at n; no independently chosen lower isomorphism is used.
8. Apply lemma-perfect-complexes-over-oe (2), q=0, to Q with the specified torsion exponent.
Both images in H^0(Q/pi^n) equal the integral image. Exact constant sheaves and sections,
then the common bijection, give equality of the actual Hom transition images.
9. The witness c(n)=n+e gives the recorded Mittag-Leffler condition. No completeness
or inverse-limit identification of K has entered the proof. -/
theorem internalPerfectReductionHom_mittagLeffler
    (X : Scheme.{u}) (W : X.ProEt) (_hAffine : IsAffine W.left)
    (_hweak : (Scheme.ProEt.topology X).IsWeaklyContractible.{u + 1} W)
    (P : CochainComplex (ModuleCat.{u} (Padic.coefficientExtensionIntegers l E)) ℤ)
    (a b : ℤ) (_ha : P.IsStrictlyGE a) (_hb : P.IsStrictlyLE b)
    (_hfree : ∀ i : ℤ, Module.Finite (Padic.coefficientExtensionIntegers l E) (P.X i) ∧
      Module.Free (Padic.coefficientExtensionIntegers l E) (P.X i))
    (K : DerivedCategory (AdicCompletion.Modules l E W.left))
    (_hiso : ∀ n : ℕ, Nonempty
      ((AdicCompletion.derivedReduction l E W.left n).obj
        (internalPerfectScalarModel l E W.left P) ≅
          (AdicCompletion.derivedReduction l E W.left n).obj K))
    (e : ℕ)
    (_hkill : ∀ x : (internalPerfectScalarDualTensor l E P).homology 1,
      x ∈ Submodule.torsion (Padic.coefficientExtensionIntegers l E)
        ((internalPerfectScalarDualTensor l E P).homology 1) →
      (Padic.coefficientExtensionUniformizer l E) ^ e • x = 0) :
    (∀ (n m N : ℕ) (hnm : n + e ≤ m) (hmN : m ≤ N),
      Set.range ((internalReductionHomTower l E W.left
        (internalPerfectScalarModel l E W.left P) K).map
          (homOfLE ((Nat.le_add_right n e).trans (hnm.trans hmN))).op) =
      Set.range ((internalReductionHomTower l E W.left
        (internalPerfectScalarModel l E W.left P) K).map
          (homOfLE ((Nat.le_add_right n e).trans hnm)).op)) ∧
    (internalReductionHomTower l E W.left
      (internalPerfectScalarModel l E W.left P) K).IsMittagLeffler := by
  obtain ⟨c, d, hc, hd, hQ⟩ :=
    internalPerfectScalarDualTensor_finite l E P a b _ha _hb _hfree
  obtain ⟨eQ, heQ⟩ := internalPerfectEndomorphism_quotientComparison l E X W
    _hAffine _hweak P a b _ha _hb _hfree
  have hT : ∀ (n m N : ℕ) (hnm : n + e ≤ m) (hmN : m ≤ N),
      Set.range ((internalReductionHomTower l E W.left
        (internalPerfectScalarModel l E W.left P)
        (internalPerfectScalarModel l E W.left P)).map
          (homOfLE ((Nat.le_add_right n e).trans (hnm.trans hmN))).op) =
      Set.range ((internalReductionHomTower l E W.left
        (internalPerfectScalarModel l E W.left P)
        (internalPerfectScalarModel l E W.left P)).map
          (homOfLE ((Nat.le_add_right n e).trans hnm)).op) := by
    intro n m N hnm hmN
    have hNm : n + 1 + e ≤ N + 1 := by omega
    have hmm : n + 1 + e ≤ m + 1 := by omega
    have hN := Padic.integral_scalar_cohomology_images l E
      (internalPerfectScalarDualTensor l E P) c d hc hd hQ 0 e _hkill
      (N + 1) (n + 1) (by omega) hNm
    have hm := Padic.integral_scalar_cohomology_images l E
      (internalPerfectScalarDualTensor l E P) c d hc hd hQ 0 e _hkill
      (m + 1) (n + 1) (by omega) hmm
    have hscalar := hN.trans hm.symm
    have hLC := locallyConstant_range_eq (Y := ConnectedComponents W.left) _ _ hscalar
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      have hx := hLC.subset ⟨eQ N x, rfl⟩
      obtain ⟨z, hz⟩ := hx
      refine ⟨(eQ m).symm z, (eQ n).injective ?_⟩
      rw [heQ, Equiv.apply_symm_apply, heQ]
      exact hz
    · rintro ⟨x, rfl⟩
      have hx := hLC.symm.subset ⟨eQ m x, rfl⟩
      obtain ⟨z, hz⟩ := hx
      refine ⟨(eQ N).symm z, (eQ n).injective ?_⟩
      rw [heQ, Equiv.apply_symm_apply, heQ]
      exact hz
  have hK := homTower_uniformRange l E W.left
    (internalPerfectScalarModel l E W.left P) K _hiso e hT
  exact ⟨hK, uniformRange_mittagLeffler _ e hK⟩

end AlgebraicGeometry.ProEtale
