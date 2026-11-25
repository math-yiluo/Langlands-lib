/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Algebra.Homology.Single
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import WeilConjectures.Algebra.Homology.ZeroDifferentialFreeCoproduct

/-!
# A free two-term cover of a cochain complex

Source: Stacks Project, Differential Graded Algebra, Lemma 15.60.8 (Tag 09KN),
proof (blueprint: lem-pc-derived-free-complex-cover).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace CochainComplex

private abbrev CoverCycles
    {A : Type u} [CommRing A]
    (M : CochainComplex (ModuleCat.{u} A) ℤ) (n : ℤ) :=
  {z : M.X n // M.d n (n + 1) z = 0}

private abbrev CoverLower
    {A : Type u} [CommRing A]
    (M : CochainComplex (ModuleCat.{u} A) ℤ) (n : ℤ) :=
  M.X n →₀ A

private abbrev CoverUpper
    {A : Type u} [CommRing A]
    (M : CochainComplex (ModuleCat.{u} A) ℤ) (n : ℤ) :=
  (M.X (n - 1) →₀ A) × (CoverCycles M n →₀ A)

private noncomputable def coverMove
    {A : Type u} [CommRing A]
    (M : CochainComplex (ModuleCat.{u} A) ℤ) (n : ℤ) :
    CoverLower M n →ₗ[A] (M.X (n + 1 - 1) →₀ A) :=
  Finsupp.lmapDomain A A (M.XIsoOfEq (add_sub_cancel_right n 1).symm).hom

private noncomputable def coverDelta
    {A : Type u} [CommRing A]
    (M : CochainComplex (ModuleCat.{u} A) ℤ) (n : ℤ) :
    CoverLower M n →ₗ[A] CoverUpper M (n + 1) :=
  (LinearMap.inl A _ _).comp (coverMove M n)

private noncomputable def coverD
    {A : Type u} [CommRing A]
    (M : CochainComplex (ModuleCat.{u} A) ℤ) (n : ℤ) :
    ModuleCat.of A (CoverUpper M n × CoverLower M n) ⟶
      ModuleCat.of A (CoverUpper M (n + 1) × CoverLower M (n + 1)) :=
  ModuleCat.ofHom
    (((coverDelta M n).comp (LinearMap.snd A _ _)).prod 0)

private theorem coverD_sq
    {A : Type u} [CommRing A]
    (M : CochainComplex (ModuleCat.{u} A) ℤ) (n : ℤ) :
    coverD M n ≫ coverD M (n + 1) = 0 := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  simp [coverD, LinearMap.prod_apply, LinearMap.comp_apply]

private noncomputable def coverQ
    {A : Type u} [CommRing A]
    (M : CochainComplex (ModuleCat.{u} A) ℤ) :
    CochainComplex (ModuleCat.{u} A) ℤ :=
  CochainComplex.of (fun n ↦ ModuleCat.of A (CoverUpper M n × CoverLower M n))
    (coverD M) (coverD_sq M)

private noncomputable def coverLeft
    {A : Type u} [CommRing A]
    (M : CochainComplex (ModuleCat.{u} A) ℤ) :
    CochainComplex (ModuleCat.{u} A) ℤ :=
  CochainComplex.of (fun n ↦ ModuleCat.of A (CoverUpper M n)) (fun _ ↦ 0)
    (fun _ ↦ zero_comp)

private noncomputable def coverRight
    {A : Type u} [CommRing A]
    (M : CochainComplex (ModuleCat.{u} A) ℤ) :
    CochainComplex (ModuleCat.{u} A) ℤ :=
  CochainComplex.of (fun n ↦ ModuleCat.of A (CoverLower M n)) (fun _ ↦ 0)
    (fun _ ↦ zero_comp)

private noncomputable def coverIn
    {A : Type u} [CommRing A]
    (M : CochainComplex (ModuleCat.{u} A) ℤ) :
    coverLeft M ⟶ coverQ M :=
  CochainComplex.ofHom (fun _ ↦ ModuleCat.ofHom (LinearMap.inl A _ _)) (by
    intro n
    ext x
    simp [coverLeft, coverQ, coverD])

private noncomputable def coverOut
    {A : Type u} [CommRing A]
    (M : CochainComplex (ModuleCat.{u} A) ℤ) :
    coverQ M ⟶ coverRight M :=
  CochainComplex.ofHom (fun _ ↦ ModuleCat.ofHom (LinearMap.snd A _ _)) (by
    intro n
    ext x
    simp [coverRight, coverQ, coverD])

private theorem coverIn_out
    {A : Type u} [CommRing A]
    (M : CochainComplex (ModuleCat.{u} A) ℤ) :
    coverIn M ≫ coverOut M = 0 := by
  apply HomologicalComplex.hom_ext
  intro n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  rfl

private noncomputable def coverSES
    {A : Type u} [CommRing A]
    (M : CochainComplex (ModuleCat.{u} A) ℤ) :
    ShortComplex (CochainComplex (ModuleCat.{u} A) ℤ) :=
  ShortComplex.mk (coverIn M) (coverOut M) (coverIn_out M)

private noncomputable def coverSplitting
    {A : Type u} [CommRing A]
    (M : CochainComplex (ModuleCat.{u} A) ℤ) (n : ℤ) :
    ((coverSES M).map
      (HomologicalComplex.eval (ModuleCat.{u} A) (ComplexShape.up ℤ) n)).Splitting where
  r := ModuleCat.ofHom (LinearMap.fst A _ _)
  s := ModuleCat.ofHom (LinearMap.inr A _ _)
  f_r := by ext x; rfl
  s_g := by ext x; rfl
  id := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change (x.1 + 0, 0 + x.2) = x
    exact Prod.ext (add_zero _) (zero_add _)

private noncomputable def coverUpperEval
    {A : Type u} [CommRing A]
    (M : CochainComplex (ModuleCat.{u} A) ℤ) (n : ℤ) :
    CoverUpper M n →ₗ[A] M.X n :=
  ((M.d (n - 1) n).hom.comp (Finsupp.linearCombination A id)).coprod
    (Finsupp.linearCombination A (fun z : CoverCycles M n ↦ z.val))

private noncomputable def coverEval
    {A : Type u} [CommRing A]
    (M : CochainComplex (ModuleCat.{u} A) ℤ) (n : ℤ) :
    (CoverUpper M n × CoverLower M n) →ₗ[A] M.X n :=
  (coverUpperEval M n).coprod (Finsupp.linearCombination A id)

private theorem coverUpperEval_d
    {A : Type u} [CommRing A]
    (M : CochainComplex (ModuleCat.{u} A) ℤ) (n : ℤ) (x : CoverUpper M n) :
    M.d n (n + 1) (coverUpperEval M n x) = 0 := by
  rcases x with ⟨x, z⟩
  have hd (y : M.X (n - 1)) : M.d n (n + 1) (M.d (n - 1) n y) = 0 := by
    exact DFunLike.congr_fun (congrArg ModuleCat.Hom.hom (M.d_comp_d (n - 1) n (n + 1))) y
  change M.d n (n + 1)
    ((M.d (n - 1) n) (Finsupp.linearCombination A id x) +
      Finsupp.linearCombination A (fun z : CoverCycles M n ↦ z.val) z) = 0
  rw [map_add, hd, zero_add, Finsupp.apply_linearCombination]
  have hz : (fun z : CoverCycles M n ↦ M.d n (n + 1) z.val) = 0 := by
    funext z
    exact z.property
  change Finsupp.linearCombination A (fun z : CoverCycles M n ↦ M.d n (n + 1) z.val) z = 0
  rw [hz]
  exact Finsupp.linearCombination_zero_apply A z

private theorem coverUpperEval_delta
    {A : Type u} [CommRing A]
    (M : CochainComplex (ModuleCat.{u} A) ℤ) (n : ℤ) (x : CoverLower M n) :
    coverUpperEval M (n + 1) (coverDelta M n x) =
      M.d n (n + 1) (Finsupp.linearCombination A id x) := by
  have he : ∀ y : M.X n,
      M.d (n + 1 - 1) (n + 1)
        ((M.XIsoOfEq (add_sub_cancel_right n 1).symm).hom y) = M.d n (n + 1) y := by
    intro y
    exact DFunLike.congr_fun (congrArg ModuleCat.Hom.hom
      (M.XIsoOfEq_hom_comp_d (add_sub_cancel_right n 1).symm (n + 1))) y
  simp only [coverUpperEval, coverDelta, coverMove, LinearMap.comp_apply,
    LinearMap.coprod_apply, LinearMap.inl_apply, map_zero, add_zero,
    Finsupp.lmapDomain_apply, Finsupp.linearCombination_mapDomain]
  change (M.d (n + 1 - 1) (n + 1)).hom
    (Finsupp.linearCombination A (M.XIsoOfEq (add_sub_cancel_right n 1).symm).hom x) = _
  rw [Finsupp.apply_linearCombination]
  simp only [Function.comp_def, he]
  exact (Finsupp.apply_linearCombination A (M.d n (n + 1)).hom id x).symm

private theorem coverEval_comm
    {A : Type u} [CommRing A]
    (M : CochainComplex (ModuleCat.{u} A) ℤ) (n : ℤ) :
    ModuleCat.ofHom (coverEval M n) ≫ M.d n (n + 1) =
      (coverQ M).d n (n + 1) ≫ ModuleCat.ofHom (coverEval M (n + 1)) := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change M.d n (n + 1) (coverEval M n x) =
    coverEval M (n + 1) ((coverQ M).d n (n + 1) x)
  simp [coverEval, coverQ, coverD, LinearMap.coprod_apply,
    coverUpperEval_d, coverUpperEval_delta]

private noncomputable def coverMap
    {A : Type u} [CommRing A]
    (M : CochainComplex (ModuleCat.{u} A) ℤ) :
    coverQ M ⟶ M :=
  CochainComplex.ofHom (fun n ↦ ModuleCat.ofHom (coverEval M n)) (coverEval_comm M)

private theorem coverSES_shortExact
    {A : Type u} [CommRing A]
    (M : CochainComplex (ModuleCat.{u} A) ℤ) :
    (coverSES M).ShortExact := by
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
    (C := ModuleCat.{u} A) (c := ComplexShape.up ℤ) (coverSES M)
  intro n
  exact (coverSplitting M n).shortExact

/-- (blueprint: lem-pc-derived-free-complex-cover) Specialize the construction in
Stacks, Tag 09KN, to a ring with zero differential. For each element in every degree,
take a two-term free complex with differential the identity and map its generators
to that element and its differential. Add a one-term free complex for each cocycle.
These summands give degreewise and cocycle surjectivity. The upper generators and
the added cocycle summands form the left, zero-differential subcomplex; the lower
generators form the zero-differential quotient. Their underlying modules split in
each degree. -/
theorem exists_freeComplexCover {A : Type u} [CommRing A]
    (M : CochainComplex (ModuleCat.{u} A) ℤ) :
    ∃ (S : ShortComplex (CochainComplex (ModuleCat.{u} A) ℤ))
      (f : S.X₂ ⟶ M),
      (∀ n : ℤ, Function.Surjective (f.f n)) ∧
      (∀ (n : ℤ) (z : M.X n), M.d n (n + 1) z = 0 →
        ∃ x : S.X₂.X n, S.X₂.d n (n + 1) x = 0 ∧ f.f n x = z) ∧
      S.ShortExact ∧
      (∀ n : ℤ,
        Nonempty
          (S.map (HomologicalComplex.eval (ModuleCat.{u} A) (ComplexShape.up ℤ) n)).Splitting) ∧
      ∃ (I₁ I₃ : Type u) (d₁ : I₁ → ℤ) (d₃ : I₃ → ℤ),
        Nonempty (S.X₁ ≅ ∐ (fun i : I₁ =>
          (HomologicalComplex.single (ModuleCat.{u} A) (ComplexShape.up ℤ) (d₁ i)).obj
            (ModuleCat.of A A))) ∧
        Nonempty (S.X₃ ≅ ∐ (fun i : I₃ =>
          (HomologicalComplex.single (ModuleCat.{u} A) (ComplexShape.up ℤ) (d₃ i)).obj
            (ModuleCat.of A A))) := by
  classical
  refine ⟨coverSES M, coverMap M, ?_, ?_, ?_, ?_, ?_⟩
  · intro n z
    refine ⟨((0, 0), Finsupp.single z 1), ?_⟩
    change coverEval M n ((0, 0), Finsupp.single z 1) = z
    simp [coverEval, coverUpperEval, LinearMap.coprod_apply]
  · intro n z hz
    refine ⟨((0, Finsupp.single ⟨z, hz⟩ 1), 0), ?_, ?_⟩
    · change (coverQ M).d n (n + 1) ((0, Finsupp.single ⟨z, hz⟩ 1), 0) = 0
      simp [coverQ, coverD]
    · change coverEval M n ((0, Finsupp.single ⟨z, hz⟩ 1), 0) = z
      simp [coverEval, coverUpperEval, LinearMap.coprod_apply]
  · exact coverSES_shortExact M
  · exact fun n ↦ ⟨coverSplitting M n⟩
  · refine ⟨(Σ n : ℤ, (M.X (n - 1) ⊕ CoverCycles M n)),
      (Σ n : ℤ, M.X n), Sigma.fst, Sigma.fst, ?_, ?_⟩
    · exact nonempty_iso_coproduct_single_of_zero_d (coverLeft M)
        (fun n ↦ M.X (n - 1) ⊕ CoverCycles M n)
        (fun _ ↦ (Finsupp.sumFinsuppLEquivProdFinsupp A).symm)
        (fun i j ↦ by simp [coverLeft, CochainComplex.of.d])
    · exact nonempty_iso_coproduct_single_of_zero_d (coverRight M)
        (fun n ↦ M.X n) (fun _ ↦ LinearEquiv.refl A _)
        (fun i j ↦ by simp [coverRight, CochainComplex.of.d])


end CochainComplex
