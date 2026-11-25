/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Diagonal.DiagonalTowerLimitInterface

/-! # Categorical assembly of the completed diagonal limit

The existence and uniqueness argument is checked before specializing its categories.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u v w a b c vc r
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.ProEtale

private theorem diagonalUniqueLift
    {C : Type a} [Category.{v} C] {B : Type b} [Category.{u} B]
    (F : C ⥤ B) {P Q : C} {K J : B} (s : F.obj P ⟶ K) (t : F.obj Q ⟶ J)
    [IsIso t] (f : K ⟶ J)
    (hF : Function.Bijective (fun δ : P ⟶ Q ↦ F.map δ)) :
    ∃! δ : P ⟶ Q, F.map δ ≫ t = s ≫ f := by
  obtain ⟨δ, hδ⟩ := hF.2 (s ≫ f ≫ inv t)
  have he : F.map δ ≫ t = s ≫ f := by
    simpa only [Category.assoc, IsIso.inv_hom_id, Category.comp_id] using
      congrArg (fun g ↦ g ≫ t) hδ
  refine ⟨δ, he, ?_⟩
  intro ε hε
  apply hF.1
  exact (cancel_mono t).1 (hε.trans he.symm)

/-- Assemble normalized completed data from endpoint comparisons and finite
comparison equations. Source: diagonal tower limit, paragraph (3)
(blueprint: lem-sfb-diagonal-completed-data-assembly).
Proof: lift the conjugated underlying arrow by the assumed hom-set bijection;
cancel the invertible target comparison for uniqueness, and retain all supplied
endpoint and finite-reduction normalizations. -/
theorem diagonalCompleteData_of_bijective
    {A : Type a} [Category.{v} A] [Abelian A]
    {B : Type b} [Category.{u} B] [Abelian B]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w} B]
    [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ A)] [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ B)]
    [HasLimitsOfShape ℕᵒᵖ B]
    (ℓ : ℕ) (F : A ⥤ B) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (P Q : A) (S H : ℕᵒᵖ ⥤ B) (K J : DerivedCategory (ℕᵒᵖ ⥤ B))
    (f : K ⟶ J)
    (a : K ≅ (DerivedCategory.singleFunctor _ 0).obj S)
    (b : J ≅ ((DerivedCategory.singleFunctor _ 0).obj H)⟦(2 : ℤ)⟧)
    (sourceNorm : (F.obj P ≅ limit S) → Prop)
    (targetNorm : (F.obj Q ≅ limit H) → Prop)
    (L : DiagonalRlim B) (M : DiagonalCompletedReductionData ℓ A)
    (s : F.obj P ≅ limit S) (t : F.obj Q ≅ limit H)
    (hs : sourceNorm s) (ht : targetNorm t)
    (hsource : IsIso (diagonalSingleLimitComparison F L P S K s a))
    (htarget : IsIso (diagonalShiftedSingleLimitComparison F L Q H J t b))
    (hP : ∀ V : DerivedCategory A, IsIso (ℓ • 𝟙 V) →
      Subsingleton (V ⟶ (DerivedCategory.singleFunctor _ 0).obj P))
    (hQ : ∀ V : DerivedCategory A, IsIso (ℓ • 𝟙 V) →
      Subsingleton (V ⟶ ((DerivedCategory.singleFunctor _ 0).obj Q)⟦(2 : ℤ)⟧))
    (hF : Function.Bijective (fun δ : (DerivedCategory.singleFunctor _ 0).obj P ⟶
      ((DerivedCategory.singleFunctor _ 0).obj Q)⟦(2 : ℤ)⟧ ↦ F.mapDerivedCategory.map δ))
    (hfinite : ∀ δ : (DerivedCategory.singleFunctor _ 0).obj P ⟶
        ((DerivedCategory.singleFunctor _ 0).obj Q)⟦(2 : ℤ)⟧,
      F.mapDerivedCategory.map δ ≫ diagonalShiftedSingleLimitComparison F L Q H J t b =
        diagonalSingleLimitComparison F L P S K s a ≫ L.R.map f → ∀ n : ℕ,
      ∃ (e : F.mapDerivedCategory.obj
            ((((evaluation ℕᵒᵖ A).obj (op n)).mapDerivedCategory).obj
              (M.derived.T.obj ((DerivedCategory.singleFunctor _ 0).obj P))) ≅
            (((evaluation ℕᵒᵖ B).obj (op n)).mapDerivedCategory).obj K)
        (g : F.mapDerivedCategory.obj
            ((((evaluation ℕᵒᵖ A).obj (op n)).mapDerivedCategory).obj
              (M.derived.T.obj (((DerivedCategory.singleFunctor _ 0).obj Q)⟦(2 : ℤ)⟧))) ≅
            (((evaluation ℕᵒᵖ B).obj (op n)).mapDerivedCategory).obj J),
        F.mapDerivedCategory.map ((M.unit n).app _) ≫ e.hom =
          diagonalSingleLimitComparison F L P S K s a ≫ (L.projection n).app K ∧
        F.mapDerivedCategory.map ((M.unit n).app _) ≫ g.hom =
          diagonalShiftedSingleLimitComparison F L Q H J t b ≫ (L.projection n).app J ∧
        F.mapDerivedCategory.map
            ((((evaluation ℕᵒᵖ A).obj (op n)).mapDerivedCategory).map (M.derived.T.map δ)) =
          e.hom ≫ (((evaluation ℕᵒᵖ B).obj (op n)).mapDerivedCategory).map f ≫ g.inv) :
    diagonalCompleteDataAssertion ℓ F P Q S H K J f a b sourceNorm targetNorm := by
  have := htarget
  refine ⟨L, M, s, t, hs, ht, hsource, htarget, hP, hQ, ?_, ?_⟩
  · exact diagonalUniqueLift F.mapDerivedCategory _ _ (L.R.map f) hF
  · intro δ hδ n
    obtain ⟨e, g, he, hg, hmap⟩ := hfinite δ hδ n
    exact ⟨e, g, he, hg, hmap⟩

/-- Finite endpoint comparisons with their heterogeneous class equations.
Source: the finite normalization definitions
(blueprint: lem-sfb-diagonal-completed-data-assembly). -/
def diagonalFiniteCycleNormalizationHEq
    {A : Type a} [Category.{v} A] [Abelian A]
    [HasExt.{w} A] [HasExt.{w} (ℕᵒᵖ ⥤ A)]
    (S H : ℕᵒᵖ ⥤ A) (c : Ext.{w} S H 2)
    (P Q : ℕ → A)
    (sourceNorm : ∀ n : ℕ, (S.obj (op n) ≅ P n) → Prop)
    (targetNorm : ∀ n : ℕ, (H.obj (op n) ≅ Q n) → Prop)
    (finiteClass : ∀ n : ℕ, Ext.{w} (P n) (Q n) 2) : Prop :=
  ∀ n : ℕ, ∃ (s : S.obj (op n) ≅ P n) (t : H.obj (op n) ≅ Q n),
    sourceNorm n s ∧ targetNorm n t ∧
    HEq ((Ext.mk₀.{w} s.inv).comp
      ((c.mapExactFunctor ((evaluation ℕᵒᵖ A).obj (op n))).comp
        (Ext.mk₀.{w} t.hom) (add_zero 2)) (zero_add 2)) (finiteClass n)

/-- Replace homogeneous heterogeneous equalities by equalities in the finite
normalization. Source: the finite normalization definitions
(blueprint: lem-sfb-diagonal-completed-data-assembly).
Proof: retain each pair of endpoint isomorphisms and apply eq_of_heq to its equation. -/
theorem diagonalFiniteCycleNormalization_of_heq
    {A : Type a} [Category.{v} A] [Abelian A]
    [HasExt.{w} A] [HasExt.{w} (ℕᵒᵖ ⥤ A)]
    (S H : ℕᵒᵖ ⥤ A) (c : Ext.{w} S H 2)
    (P Q : ℕ → A)
    (sourceNorm : ∀ n : ℕ, (S.obj (op n) ≅ P n) → Prop)
    (targetNorm : ∀ n : ℕ, (H.obj (op n) ≅ Q n) → Prop)
    (finiteClass : ∀ n : ℕ, Ext.{w} (P n) (Q n) 2)
    (h : diagonalFiniteCycleNormalizationHEq S H c P Q sourceNorm targetNorm finiteClass) :
    diagonalFiniteCycleNormalization S H c P Q sourceNorm targetNorm finiteClass := by
  intro n
  obtain ⟨s, t, hs, ht, he⟩ := h n
  exact ⟨s, t, hs, ht, eq_of_heq he⟩

/-- The strict-system part of the diagonal limit assertion, retaining its Ext
class and finite normalization. Source: the system and limit interfaces
(blueprint: lem-sfb-diagonal-completed-data-assembly). -/
def DiagonalStrictDataSpec
    (ℓ : ℕ) {A : Type a} [Category.{v} A] [Abelian A] [HasExt.{w} A]
    {B : Type b} [Category.{u} B] [Abelian B]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ B)]
    [HasExt.{w} (ℕᵒᵖ ⥤ B)]
    (L₀ : A ⥤ B) (D : DiagonalDerivedReduction ℓ L₀)
    (S U : A) (boundary : Ext S U 1)
    (root : (ℕᵒᵖ ⥤ B) → Type r)
    (finite : ∀ H : ℕᵒᵖ ⥤ B, root H → Ext (D.ordinary.E.obj S) H 2 → Prop) : Prop :=
  ∃ (H : ℕᵒᵖ ⥤ B) (roots : root H)
      (a : D.T.obj ((DerivedCategory.singleFunctor A 0).obj S) ≅
        (DerivedCategory.singleFunctor _ 0).obj (D.ordinary.E.obj S))
      (b : D.T.obj (((DerivedCategory.singleFunctor A 0).obj U)⟦(1 : ℤ)⟧) ≅
        ((DerivedCategory.singleFunctor _ 0).obj H)⟦(2 : ℤ)⟧)
      (cycle : Ext (D.ordinary.E.obj S) H 2),
      a.hom = diagonalDerivedSingleCounit ℓ L₀ D S ∧
      cycle.hom = a.inv ≫ D.T.map boundary.hom ≫ b.hom ∧ finite H roots cycle

/-- Map only the finite predicate of strict data, preserving all witnesses.
Source: strict-system normalization (blueprint: lem-sfb-diagonal-completed-data-assembly).
Proof: unpack the witnesses and apply the supplied implication to their finite equation. -/
theorem diagonalStrictData_map_finite
    (ℓ : ℕ) {A : Type a} [Category.{v} A] [Abelian A] [HasExt.{w} A]
    {B : Type b} [Category.{u} B] [Abelian B]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ B)]
    [HasExt.{w} (ℕᵒᵖ ⥤ B)]
    (L₀ : A ⥤ B) (D : DiagonalDerivedReduction ℓ L₀)
    (S U : A) (boundary : Ext S U 1)
    (root : (ℕᵒᵖ ⥤ B) → Type r)
    (finite : ∀ H : ℕᵒᵖ ⥤ B, root H → Ext (D.ordinary.E.obj S) H 2 → Prop)
    (inputFinite : ∀ H : ℕᵒᵖ ⥤ B, root H → Ext (D.ordinary.E.obj S) H 2 → Prop)
    (system : DiagonalStrictDataSpec ℓ L₀ D S U boundary root inputFinite)
    (normalize : ∀ H roots cycle, inputFinite H roots cycle → finite H roots cycle) :
    DiagonalStrictDataSpec ℓ L₀ D S U boundary root finite := by
  obtain ⟨H, roots, a, b, cycle, ha, hc, hf⟩ := system
  exact ⟨H, roots, a, b, cycle, ha, hc, normalize H roots cycle hf⟩

/-- Combine the strict-system part with completed compatibility.
Source: the simultaneous diagonal limit assertion
(blueprint: lem-sfb-diagonal-completed-data-assembly).
Proof: unpack the strict witnesses and retain completed compatibility for the same
endpoint identifications. -/
theorem diagonalLimitData_of_strict
    (ℓ : ℕ) {A : Type a} [Category.{v} A] [Abelian A] [HasExt.{w} A]
    {B : Type b} [Category.{u} B] [Abelian B]
    {C : Type c} [Category.{vc} C] [Abelian C]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w} B]
    [HasDerivedCategory.{w} C] [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ B)]
    [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ C)] [HasExt.{w} (ℕᵒᵖ ⥤ B)]
    [HasLimitsOfShape ℕᵒᵖ B]
    (L₀ : A ⥤ B) (D : DiagonalDerivedReduction ℓ L₀)
    (S U : A) (boundary : Ext S U 1)
    (F : C ⥤ B) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (P Q : C) (root : (ℕᵒᵖ ⥤ B) → Type r)
    (finite : ∀ H : ℕᵒᵖ ⥤ B, root H → Ext (D.ordinary.E.obj S) H 2 → Prop)
    (sourceNorm : (F.obj P ≅ limit (D.ordinary.E.obj S)) → Prop)
    (targetNorm : ∀ H : ℕᵒᵖ ⥤ B, root H → (F.obj Q ≅ limit H) → Prop)
    (system : DiagonalStrictDataSpec ℓ L₀ D S U boundary root finite)
    (completed : ∀ H roots a b,
      diagonalCompleteDataAssertion ℓ F P Q (D.ordinary.E.obj S) H _ _
        (D.T.map boundary.hom) a b sourceNorm (targetNorm H roots)) :
    DiagonalLimitDataSpec ℓ L₀ D S U boundary F P Q root finite sourceNorm targetNorm := by
  obtain ⟨H, roots, a, b, cycle, ha, hc, hf⟩ := system
  exact ⟨H, roots, a, b, cycle, ha, hc, hf, completed H roots a b⟩

end AlgebraicGeometry.ProEtale
