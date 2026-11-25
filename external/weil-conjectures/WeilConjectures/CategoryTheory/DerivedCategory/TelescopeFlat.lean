/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
public import WeilConjectures.CategoryTheory.DerivedCategory.Telescope

/-!
# Reduction to bounded complexes of flat objects

Let `τ : F ⟶ G` be a natural transformation, compatible with the shifts, between triangulated
functors out of `D(C)` which commute with countable coproducts.

* A complex `L` is the union of its stupid truncations `σ^{≥ -n} L`, so `τ` is an isomorphism at
  `L` if it is an isomorphism at all of them
  (`DerivedCategory.isIso_app_Q_obj_of_isIso_app_Q_obj_stupidTrunc`).
* Hence `τ` is an isomorphism if it is an isomorphism at all the strictly bounded complexes
  (`DerivedCategory.isIso_app_of_isIso_app_Q_obj_bounded`), first reducing to bounded above
  complexes by canonical truncations.
* If `C` is a Grothendieck abelian monoidal category with functorial flat resolutions, then `τ`
  is an isomorphism if it is an isomorphism at all the strictly bounded complexes of flat objects
  (`DerivedCategory.isIso_app_of_isIso_app_Q_obj_flat`): a bounded above complex has a bounded
  above flat resolution, which is the union of its stupid truncations.
-/

@[expose] public section

universe w v u

open CategoryTheory Category Limits

namespace CochainComplex

variable {C : Type*} [Category* C] [Abelian C]

/-- The stupid truncation `σ^{≥ a} L` of a complex which is strictly `≤ b` is strictly `≤ b`. -/
instance isStrictlyLE_stupidTrunc (L : CochainComplex C ℤ) (a b : ℤ) [L.IsStrictlyLE b] :
    CochainComplex.IsStrictlyLE (L.stupidTrunc (ComplexShape.embeddingUpIntGE a)) b := by
  rw [isStrictlyLE_iff]
  intro i hi
  exact IsZero.of_mono ((L.ιStupidTrunc (ComplexShape.embeddingUpIntGE a)).f i)
    (L.isZero_of_isStrictlyLE b i hi)

/-- A property of objects containing zero and closed under isomorphisms which holds for all the
terms of a complex holds for all the terms of its stupid truncations. -/
lemma prop_stupidTrunc_X (P : ObjectProperty C) [P.IsClosedUnderIsomorphisms] [P.ContainsZero]
    (L : CochainComplex C ℤ) (hL : ∀ n, P (L.X n)) (a n : ℤ) :
    P ((L.stupidTrunc (ComplexShape.embeddingUpIntGE a)).X n) := by
  by_cases hn : a ≤ n
  · obtain ⟨k, hk⟩ := Int.le.dest hn
    have : IsIso ((L.ιStupidTrunc (ComplexShape.embeddingUpIntGE a)).f n) :=
      L.isIso_ιStupidTrunc_f _ (i := k) (by rw [ComplexShape.embeddingUpIntGE_f]; lia)
    exact P.prop_of_iso (asIso ((L.ιStupidTrunc (ComplexShape.embeddingUpIntGE a)).f n)).symm
      (hL n)
  · exact P.prop_of_isZero (L.isZero_stupidTrunc_X (ComplexShape.embeddingUpIntGE a) n
      ((ComplexShape.notMem_range_embeddingUpIntGE_iff a n).2 (by lia)))

end CochainComplex

namespace DerivedCategory

section

variable {C : Type*} [Category* C] [Abelian C] [HasDerivedCategory C] [HasCoproductsOfShape ℕ C]
  [Abelian.HasKInjectiveResolutions C]
  {T : Type*} [Category* T] [Preadditive T] [HasZeroObject T] [HasShift T ℤ]
  [∀ n : ℤ, (CategoryTheory.shiftFunctor T n).Additive] [Pretriangulated T]
  {F G : DerivedCategory C ⥤ T} [F.CommShift ℤ] [G.CommShift ℤ] [F.IsTriangulated]
  [G.IsTriangulated] (τ : F ⟶ G) [NatTrans.CommShift τ ℤ]
  [PreservesColimitsOfShape (Discrete ℕ) F] [PreservesColimitsOfShape (Discrete ℕ) G]

/-- The sequence `n ↦ -n` in `ℤᵒᵖ`, indexing the stupid truncations `σ^{≥ -n}`. -/
noncomputable def negNatFunctor : ℕ ⥤ ℤᵒᵖ where
  obj n := Opposite.op (-(n : ℤ))
  map f := (homOfLE (by have := leOfHom f; lia)).op

/-- If `τ` is an isomorphism at all the stupid truncations `σ^{≥ -n} L` of a complex `L`, it is
an isomorphism at `L`. -/
lemma isIso_app_Q_obj_of_isIso_app_Q_obj_stupidTrunc (L : CochainComplex C ℤ)
    (h : ∀ n : ℕ,
      IsIso (τ.app (Q.obj (L.stupidTrunc (ComplexShape.embeddingUpIntGE (-(n : ℤ))))))) :
    IsIso (τ.app (Q.obj L)) :=
  isIso_app_Q_obj_of_cocone τ (negNatFunctor ⋙ L.stupidFiltrationGE)
    (L.coconeStupidFiltrationGE.whisker negNatFunctor)
    (fun i ↦ ⟨(-i).toNat, fun n hn ↦ by
      obtain ⟨k, hk⟩ := Int.le.dest (show -(n : ℤ) ≤ i by lia)
      exact L.isIso_ιStupidTrunc_f _ (i := k) (by simp [negNatFunctor]; lia)⟩)
    h

/-- If `τ` is an isomorphism at all the strictly bounded complexes, it is an isomorphism. -/
lemma isIso_app_of_isIso_app_Q_obj_bounded
    (h : ∀ (L : CochainComplex C ℤ) (a b : ℤ), L.IsStrictlyGE a → L.IsStrictlyLE b →
      IsIso (τ.app (Q.obj L)))
    (K : DerivedCategory C) : IsIso (τ.app K) :=
  isIso_app_of_isIso_app_Q_obj_isStrictlyLE τ (fun L b _ ↦
    isIso_app_Q_obj_of_isIso_app_Q_obj_stupidTrunc τ L fun n ↦
      h _ (-(n : ℤ)) b inferInstance inferInstance) K

end

section Flat

variable {C : Type u} [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{v} C]
  [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalClosed C] [BraidedCategory C]
  [Abelian.HasFunctorialFlatResolution C] [HasDerivedCategory.{w} C]
  {T : Type*} [Category* T] [Preadditive T] [HasZeroObject T] [HasShift T ℤ]
  [∀ n : ℤ, (CategoryTheory.shiftFunctor T n).Additive] [Pretriangulated T]
  {F G : DerivedCategory C ⥤ T} [F.CommShift ℤ] [G.CommShift ℤ] [F.IsTriangulated]
  [G.IsTriangulated] (τ : F ⟶ G) [NatTrans.CommShift τ ℤ]
  [PreservesColimitsOfShape (Discrete ℕ) F] [PreservesColimitsOfShape (Discrete ℕ) G]

/-- If `τ` is an isomorphism at all the strictly bounded complexes of flat objects, it is an
isomorphism. -/
lemma isIso_app_of_isIso_app_Q_obj_flat
    (h : ∀ (P : CochainComplex C ℤ) (a b : ℤ), P.IsStrictlyGE a → P.IsStrictlyLE b →
      (∀ n, ObjectProperty.flat (P.X n)) → IsIso (τ.app (Q.obj P)))
    (K : DerivedCategory C) : IsIso (τ.app K) := by
  refine isIso_app_of_isIso_app_Q_obj_isStrictlyLE τ (fun L b _ ↦ ?_) K
  obtain ⟨P, _, π, _, hP⟩ := CochainComplex.exists_quasiIso_flat_of_isStrictlyLE L b
  rw [← NatTrans.isIso_app_iff_of_iso τ (asIso (Q.map π))]
  exact isIso_app_Q_obj_of_isIso_app_Q_obj_stupidTrunc τ P fun n ↦
    h _ (-(n : ℤ)) b inferInstance inferInstance
      (CochainComplex.prop_stupidTrunc_X _ P hP _)

end Flat

end DerivedCategory
