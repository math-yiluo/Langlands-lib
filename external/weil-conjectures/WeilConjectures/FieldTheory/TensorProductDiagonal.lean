/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
public import Mathlib.RingTheory.Kaehler.Basic
public import Mathlib.Algebra.Category.Ring.Basic
public import Mathlib.CategoryTheory.Filtered.Basic
public import Mathlib.CategoryTheory.Limits.IsLimit

/-!
# The diagonal of `E ⊗_F E` for an algebraic extension

Let `E/F` be an algebraic field extension. The kernel of the multiplication map
`E ⊗_F E → E` dies in `E ⊗_L E` for some intermediate field `L` finite over `F`: the kernel is
spanned by the elements `1 ⊗ s - s ⊗ 1`, and finitely many `s` lie in a finite subextension.
Equivalently, `E` is the filtered colimit of the rings `E ⊗_L E` over the finite subextensions
`L`, so that `Spec E` is the limit of the schemes `Spec (E ⊗_L E)`, with `Spec E` embedded
diagonally.

## Main statements

- `IntermediateField.exists_finiteDimensional_mapOfCompatibleSMul_eq_zero`
-/

@[expose] public section

universe u

open TensorProduct

namespace IntermediateField

section Kernel

variable {F E : Type*} [Field F] [Field E] [Algebra F E]

/-- For `s ∈ L`, the elements `1 ⊗ s` and `s ⊗ 1` of `E ⊗_L E` agree. -/
lemma one_tmul_eq_tmul_one (L : IntermediateField F E) {s : E} (hs : s ∈ L) :
    (1 : E) ⊗ₜ[L] s = s ⊗ₜ[L] (1 : E) := by
  have h : s = (⟨s, hs⟩ : L) • (1 : E) := by
    rw [Algebra.smul_def, mul_one]
    rfl
  rw [h, smul_tmul]

/-- **The kernel of multiplication dies at a finite level.** Let `E/F` be algebraic and let
`x ∈ E ⊗_F E` be killed by the multiplication map `E ⊗_F E → E`. Then the image of `x` in
`E ⊗_L E` vanishes for some intermediate field `L` which is finite over `F`. -/
theorem exists_finiteDimensional_mapOfCompatibleSMul_eq_zero [Algebra.IsAlgebraic F E]
    (x : E ⊗[F] E) (hx : Algebra.TensorProduct.lmul' F x = 0) :
    ∃ L : IntermediateField F E, FiniteDimensional F L ∧
      mapOfCompatibleSMul L F E E E x = 0 := by
  have hmem : x ∈ (KaehlerDifferential.ideal F E).restrictScalars E := by
    change x ∈ RingHom.ker (Algebra.TensorProduct.lmul' F (S := E))
    exact hx
  rw [← KaehlerDifferential.submodule_span_range_eq_ideal,
    Finsupp.mem_span_range_iff_exists_finsupp] at hmem
  obtain ⟨c, rfl⟩ := hmem
  let L := IntermediateField.adjoin F (c.support : Set E)
  have hL : FiniteDimensional F L :=
    IntermediateField.finiteDimensional_adjoin fun s _ ↦ Algebra.IsIntegral.isIntegral s
  refine ⟨L, hL, ?_⟩
  rw [Finsupp.sum, map_sum]
  refine Finset.sum_eq_zero fun s hs ↦ ?_
  rw [map_smul, map_sub, mapOfCompatibleSMul_tmul, mapOfCompatibleSMul_tmul,
    one_tmul_eq_tmul_one L (IntermediateField.subset_adjoin F _ hs), sub_self, smul_zero]




end Kernel

section Colimit

open CategoryTheory Limits

variable (F E : Type u) [Field F] [Field E] [Algebra F E]

/-- The intermediate fields of `E/F` which are finite over `F`, ordered by inclusion. -/
abbrev FiniteSubext : Type u := {L : IntermediateField F E // FiniteDimensional F L}

instance FiniteSubext.instNonempty : Nonempty (FiniteSubext F E) := ⟨⟨⊥, inferInstance⟩⟩

instance FiniteSubext.instIsDirected : IsDirected (FiniteSubext F E) (· ≤ ·) where
  directed L₁ L₂ := by
    have := L₁.2
    have := L₂.2
    exact ⟨⟨L₁.1 ⊔ L₂.1, IntermediateField.finiteDimensional_sup _ _⟩, le_sup_left (a := L₁.1),
      le_sup_right (a := L₁.1)⟩

instance FiniteSubext.instIsFiltered : IsFiltered (FiniteSubext F E) :=
  @isFiltered_of_directed_le_nonempty _ _ (FiniteSubext.instIsDirected F E) _

/-- The diagram `L ↦ E ⊗_L E` over the finite subextensions of `E/F`. -/
noncomputable def diagonalDiagram : FiniteSubext F E ⥤ CommRingCat.{u} where
  obj L := .of (E ⊗[L.1] E)
  map {L L'} f :=
    letI : Algebra L.1 L'.1 := (IntermediateField.inclusion (leOfHom f)).toRingHom.toAlgebra
    haveI : IsScalarTower L.1 L'.1 E := IsScalarTower.of_algebraMap_eq (fun _ ↦ rfl)
    CommRingCat.ofHom
      (Algebra.TensorProduct.mapOfCompatibleSMul L'.1 L.1 E E E).toRingHom
  map_id L := by
    refine CommRingCat.hom_ext (RingHom.ext fun x ↦ ?_)
    induction x using TensorProduct.inductionOn with
    | tmul a b => rfl
    | add x y hx hy => simp_all
  map_comp f g := by
    refine CommRingCat.hom_ext (RingHom.ext fun x ↦ ?_)
    induction x using TensorProduct.inductionOn with
    | tmul a b => rfl
    | add x y hx hy => simp_all

/-- `E` as a cocone over the diagram `L ↦ E ⊗_L E`, through the multiplication maps. -/
noncomputable def diagonalCocone : Cocone (diagonalDiagram F E) where
  pt := .of E
  ι :=
    { app L := CommRingCat.ofHom (Algebra.TensorProduct.lmul' L.1 (S := E)).toRingHom
      naturality L L' f := by
        refine CommRingCat.hom_ext (RingHom.ext fun x ↦ ?_)
        induction x using TensorProduct.inductionOn with
        | tmul a b => rfl
        | add x y hx hy => simp_all }

variable {F E} [Algebra.IsAlgebraic F E]

/-- The finite subextension `F(x)` of `E/F`. -/
noncomputable def FiniteSubext.adjoin (x : E) : FiniteSubext F E :=
  ⟨IntermediateField.adjoin F {x},
    IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral x)⟩

/-- In a cocone over `L ↦ E ⊗_L E`, the images of `c ⊗ 1` and `1 ⊗ c` do not depend on `L` and
agree. -/
lemma diagonalCocone_aux (s : Cocone (diagonalDiagram F E)) (L : FiniteSubext F E) (c : E) :
    (s.ι.app L).hom (c ⊗ₜ 1) = (s.ι.app ⟨⊥, inferInstance⟩).hom (c ⊗ₜ 1) ∧
      (s.ι.app L).hom (1 ⊗ₜ c) = (s.ι.app ⟨⊥, inferInstance⟩).hom (c ⊗ₜ 1) := by
  have h₀ (M : FiniteSubext F E) (d : E) :
      (s.ι.app M).hom (d ⊗ₜ 1) = (s.ι.app ⟨⊥, inferInstance⟩).hom (d ⊗ₜ 1) :=
    ConcreteCategory.congr_hom (s.w (homOfLE (show (⟨⊥, inferInstance⟩ : FiniteSubext F E) ≤ M from
      (bot_le : (⊥ : IntermediateField F E) ≤ M.1)))) (d ⊗ₜ 1)
  refine ⟨h₀ L c, ?_⟩
  obtain ⟨M, hLM, hcM⟩ :=
    @directed_of (FiniteSubext F E) (· ≤ ·) (FiniteSubext.instIsDirected F E) L
    (FiniteSubext.adjoin (F := F) c)
  have hc : c ∈ M.1 := hcM (IntermediateField.mem_adjoin_simple_self F c)
  have h1 := ConcreteCategory.congr_hom (s.w (homOfLE hLM))
    (show (diagonalDiagram F E).obj L from (1 : E) ⊗ₜ c)
  refine h1.symm.trans ((congrArg (s.ι.app M).hom (one_tmul_eq_tmul_one M.1 hc)).trans ?_)
  exact h₀ M c

/-- **`E` is the filtered colimit of the rings `E ⊗_L E`** over the finite subextensions `L` of
an algebraic extension `E/F`. -/
noncomputable def isColimitDiagonalCocone : IsColimit (diagonalCocone F E) where
  desc s := CommRingCat.ofHom ((s.ι.app ⟨⊥, inferInstance⟩).hom.comp
    Algebra.TensorProduct.includeLeftRingHom)
  fac s L := by
    refine CommRingCat.hom_ext (RingHom.ext fun x ↦ ?_)
    induction x using TensorProduct.inductionOn with
    | tmul a b =>
      have hab : (a ⊗ₜ[L.1] b : E ⊗[L.1] E) = (a ⊗ₜ 1) * (1 ⊗ₜ b) := by
        rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
      change (s.ι.app ⟨⊥, inferInstance⟩).hom ((a * b) ⊗ₜ 1) = (s.ι.app L).hom (a ⊗ₜ b)
      rw [hab, map_mul, (diagonalCocone_aux s L a).1, (diagonalCocone_aux s L b).2]
      erw [← map_mul]
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one]
      rfl
    | add x y hx hy => simp_all
  uniq s m hm := by
    ext e
    have h := ConcreteCategory.congr_hom (hm ⟨⊥, inferInstance⟩)
      (show (diagonalDiagram F E).obj ⟨⊥, inferInstance⟩ from e ⊗ₜ (1 : E))
    change m.hom (e * 1) = _ at h
    rw [mul_one] at h
    exact h

variable (F E) in
/-- The diagram `L ↦ L` of the finite subextensions of `E/F`. -/
noncomputable def subextDiagram : FiniteSubext F E ⥤ CommRingCat.{u} where
  obj L := .of L.1
  map {L L'} f := CommRingCat.ofHom (IntermediateField.inclusion (leOfHom f)).toRingHom

variable (F E) in
/-- `E` as a cocone over its finite subextensions. -/
noncomputable def subextCocone : Cocone (subextDiagram F E) where
  pt := .of E
  ι := { app L := CommRingCat.ofHom (algebraMap L.1 E) }

/-- In a cocone over the finite subextensions, the image of `x ∈ L` does not depend on `L`. -/
lemma subextCocone_aux (s : Cocone (subextDiagram F E)) (L : FiniteSubext F E) (x : L.1) :
    (s.ι.app (FiniteSubext.adjoin (x : E))).hom
      ⟨x, IntermediateField.mem_adjoin_simple_self F (x : E)⟩ = (s.ι.app L).hom x := by
  obtain ⟨M, hLM, hxM⟩ :=
    @directed_of (FiniteSubext F E) (· ≤ ·) (FiniteSubext.instIsDirected F E) L
      (FiniteSubext.adjoin (x : E))
  exact (ConcreteCategory.congr_hom (s.w (homOfLE hxM))
    ⟨x, IntermediateField.mem_adjoin_simple_self F (x : E)⟩).symm.trans
    (ConcreteCategory.congr_hom (s.w (homOfLE hLM)) x)

/-- **`E` is the filtered colimit of its finite subextensions**, for `E/F` algebraic. -/
noncomputable def isColimitSubextCocone : IsColimit (subextCocone F E) where
  desc s := CommRingCat.ofHom
    { toFun x := (s.ι.app (FiniteSubext.adjoin x)).hom
        ⟨x, IntermediateField.mem_adjoin_simple_self F x⟩
      map_one' := (subextCocone_aux s ⟨⊥, inferInstance⟩ 1).trans (map_one _)
      map_mul' x y := by
        obtain ⟨M, hM₁, hM₂⟩ := @directed_of (FiniteSubext F E) (· ≤ ·)
          (FiniteSubext.instIsDirected F E) (FiniteSubext.adjoin x) (FiniteSubext.adjoin y)
        have hx : x ∈ M.1 := hM₁ (IntermediateField.mem_adjoin_simple_self F x)
        have hy : y ∈ M.1 := hM₂ (IntermediateField.mem_adjoin_simple_self F y)
        exact (subextCocone_aux s M ⟨x * y, mul_mem hx hy⟩).trans
          ((map_mul (s.ι.app M).hom (⟨x, hx⟩ : M.1) ⟨y, hy⟩).trans (congrArg₂ (· * ·)
            (subextCocone_aux s M ⟨x, hx⟩).symm (subextCocone_aux s M ⟨y, hy⟩).symm))
      map_zero' := (subextCocone_aux s ⟨⊥, inferInstance⟩ 0).trans (map_zero _)
      map_add' x y := by
        obtain ⟨M, hM₁, hM₂⟩ := @directed_of (FiniteSubext F E) (· ≤ ·)
          (FiniteSubext.instIsDirected F E) (FiniteSubext.adjoin x) (FiniteSubext.adjoin y)
        have hx : x ∈ M.1 := hM₁ (IntermediateField.mem_adjoin_simple_self F x)
        have hy : y ∈ M.1 := hM₂ (IntermediateField.mem_adjoin_simple_self F y)
        exact (subextCocone_aux s M ⟨x + y, add_mem hx hy⟩).trans
          ((map_add (s.ι.app M).hom (⟨x, hx⟩ : M.1) ⟨y, hy⟩).trans (congrArg₂ (· + ·)
            (subextCocone_aux s M ⟨x, hx⟩).symm (subextCocone_aux s M ⟨y, hy⟩).symm)) }
  fac s L := by
    refine CommRingCat.hom_ext (RingHom.ext fun x ↦ ?_)
    exact subextCocone_aux s L x
  uniq s m hm := by
    refine CommRingCat.hom_ext (RingHom.ext fun (x : E) ↦ ?_)
    exact (ConcreteCategory.congr_hom (hm (FiniteSubext.adjoin x))
      ⟨x, IntermediateField.mem_adjoin_simple_self F x⟩)

end Colimit

end IntermediateField
