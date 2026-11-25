/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.HypercohomologyLeftEdge
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusBaseChange
public import WeilConjectures.CategoryTheory.IdentityDerivedHomologyComparison
public import WeilConjectures.CategoryTheory.RightDerivedBaseChangeZeroUnit

/-!
# Exact comparison and the hypercohomology left edge

Source: Stacks Project, Derived Categories, Tag 015J, functoriality of the truncation
spectral object; the canonical derived base-change unit equation.
(blueprint: lem-pur-hypercohomology-edge-exact-comparison).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe uB vB uB' vB' uC vC

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Abelian.SpectralObject

/-- The left edge map is natural with respect to any natural transformation between the
functors `hⁿ` of two first quadrant spectral objects; compatibility with the connecting
maps is not needed. -/
lemma leftEdge_naturality_of_natTrans {C : Type*} [Category C] [Abelian C]
    {Y Y' : SpectralObject C EInt} [Y.IsFirstQuadrant] [Y'.IsFirstQuadrant] (n : ℤ)
    (φ : Y.H n ⟶ Y'.H n) :
    φ.app _ ≫ Y'.leftEdge n = Y.leftEdge n ≫ φ.app _ := by
  have := Y.isIso_H_map_self_succ_top n
  have := Y'.isIso_H_map_self_succ_top n
  rw [leftEdge, leftEdge, Category.assoc, ← NatTrans.naturality_assoc]
  congr 1
  rw [IsIso.eq_inv_comp, NatTrans.naturality_assoc, IsIso.hom_inv_id, Category.comp_id]

end CategoryTheory.Abelian.SpectralObject

namespace CategoryTheory.Functor

section ETrunc

variable {C D : Type*} [Category C] [Category D] [Preadditive C] [HasZeroObject C]
  [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  [Preadditive D] [HasZeroObject D] [HasShift D ℤ]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D] [CategoryTheory.IsTriangulated D]
  (F : C ⥤ D) [F.CommShift ℤ] [F.IsTriangulated] (t₁ : Triangulated.TStructure C)
  (t₂ : Triangulated.TStructure D) [F.IsTExact t₁ t₂]

/-- On the full interval `[⊥, ⊤)` both extended truncations are identities, and so is the
comparison `F(τ_{≥ ⊥} τ_{< ⊤} X) ≅ τ_{≥ ⊥} τ_{< ⊤} F(X)`. -/
lemma eTruncGELTIsoApp_bot_top_hom (X : C) :
    (F.eTruncGELTIsoApp t₁ t₂ ⊥ ⊤ X).hom = 𝟙 _ := by
  have h₁ := F.eTruncLTIsoApp_hom_eTruncLTι_app t₁ t₂ ⊤ X
  have h₂ := F.eTruncGEπ_app_eTruncGEIsoApp_hom t₁ t₂ ⊥ ((t₁.eTruncLT.obj ⊤).obj X)
  simp only [Triangulated.TStructure.eTruncLT_ι_top, Triangulated.TStructure.eTruncGEπ_bot,
    NatTrans.id_app] at h₁ h₂
  erw [Category.comp_id, Functor.map_id] at h₁
  erw [Functor.map_id, Category.id_comp] at h₂
  rw [eTruncGELTIsoApp, Iso.trans_hom, Functor.mapIso_hom, h₁, h₂]
  erw [Functor.map_id, Category.comp_id]
  rfl

end ETrunc

/-- The isomorphism `Hᵃ(F(X⟦n⟧)) ≅ Hᵃ'(F(X))`, for `n + a = a'`, attached to a functor `F`
between bounded below derived categories which commutes with the shifts. -/
noncomputable def homologyFunctorCommShiftIso {D₁ D₂ : Type*} [Category D₁] [Category D₂]
    [Abelian D₁] [Abelian D₂] [HasDerivedCategory D₁] [HasDerivedCategory D₂]
    (F : DerivedCategory.Plus D₁ ⥤ DerivedCategory.Plus D₂) [F.CommShift ℤ]
    (n a a' : ℤ) (h : n + a = a') :
    shiftFunctor (DerivedCategory.Plus D₁) n ⋙ F ⋙ DerivedCategory.Plus.homologyFunctor D₂ a ≅
      F ⋙ DerivedCategory.Plus.homologyFunctor D₂ a' :=
  isoWhiskerRight (F.commShiftIso n) (DerivedCategory.Plus.homologyFunctor D₂ a) ≪≫
    isoWhiskerLeft F ((DerivedCategory.Plus.homologyFunctor D₂ 0).shiftIso n a a' h)

variable {B : Type uB} [Category.{vB} B] [Abelian B]
  [IsGrothendieckAbelian.{vB} B] [HasDerivedCategory.{vB} B]
  {B' : Type uB'} [Category.{vB'} B'] [Abelian B']
  [IsGrothendieckAbelian.{vB'} B'] [HasDerivedCategory.{vB'} B']
  {C : Type uC} [Category.{vC} C] [Abelian C]
  [IsGrothendieckAbelian.{vC} C] [HasDerivedCategory.{vC} C]
  (G : B ⥤ C) (G' : B' ⥤ C) (β : B ⥤ B')
  [G.Additive] [G'.Additive] [β.Additive]
  [PreservesFiniteLimits G] [PreservesFiniteLimits G']
  [PreservesFiniteLimits β] [PreservesFiniteColimits β]

/-- Remove the derived identity from the canonical derived comparison.
Source: the unit definition of derived base change
(blueprint: lem-pur-hypercohomology-edge-exact-comparison). -/
abbrev normalizedDerivedBaseChange (e : G ⋙ 𝟭 C ⟶ β ⋙ G') :
    G.rightDerivedFunctorPlus ⟶ β.mapDerivedCategoryPlus ⋙ G'.rightDerivedFunctorPlus :=
  G.rightDerivedFunctorPlus.rightUnitor.inv ≫
    whiskerLeft G.rightDerivedFunctorPlus (mapDerivedCategoryPlusIdIso C).inv ≫
    rightDerivedFunctorPlusBaseChange e

omit [IsGrothendieckAbelian.{vC} C] in
open DerivedCategory.Plus in
/-- The component of the canonical left-edge target identification, written with the
shift comparison `homologyFunctorCommShiftIso` of `RG` as a single factor. -/
lemma hypercohomologyLeftEdgeTargetIso_hom_app (n : ℕ) (K : DerivedCategory.Plus B) :
    (G.hypercohomologyLeftEdgeTargetIso n).hom.app K =
      (homologyFunctor C n).map (G.rightDerivedFunctorPlus.map
        ((eTruncLTCompETruncGEIso (n : ℤ)).hom.app K)) ≫
      (homologyFunctor C n).map (G.rightDerivedFunctorPlus.map
        (((singleFunctors B).shiftIso (-(n : ℤ)) n 0 (by simp)).inv.app
          ((homologyFunctor B n).obj K))) ≫
      (homologyFunctorCommShiftIso G.rightDerivedFunctorPlus (-(n : ℤ)) n 0 (by simp)).hom.app
        ((singleFunctor B 0).obj ((homologyFunctor B n).obj K)) ≫
      (G.singleFunctorCompRightDerivedFunctorPlusCompHomologyFunctorIso 0).hom.app
        ((homologyFunctor B n).obj K) ≫
      G.rightDerivedZeroIsoSelf.hom.app ((homologyFunctor B n).obj K) :=
  congrArg (fun f ↦ _ ≫ _ ≫ f) (Category.assoc _ _ _).symm

omit [IsGrothendieckAbelian.{vC} C] in
open DerivedCategory.Plus in
/-- `Functor.hypercohomologyLeftEdgeTargetIso_hom_app`, followed by an arbitrary morphism. -/
lemma hypercohomologyLeftEdgeTargetIso_hom_app_comp (n : ℕ) (K : DerivedCategory.Plus B)
    {Z : C} (h : (homologyFunctor B n ⋙ G).obj K ⟶ Z) :
    (G.hypercohomologyLeftEdgeTargetIso n).hom.app K ≫ h =
      (homologyFunctor C n).map (G.rightDerivedFunctorPlus.map
        ((eTruncLTCompETruncGEIso (n : ℤ)).hom.app K)) ≫
      (homologyFunctor C n).map (G.rightDerivedFunctorPlus.map
        (((singleFunctors B).shiftIso (-(n : ℤ)) n 0 (by simp)).inv.app
          ((homologyFunctor B n).obj K))) ≫
      (homologyFunctorCommShiftIso G.rightDerivedFunctorPlus (-(n : ℤ)) n 0 (by simp)).hom.app
        ((singleFunctor B 0).obj ((homologyFunctor B n).obj K)) ≫
      (G.singleFunctorCompRightDerivedFunctorPlusCompHomologyFunctorIso 0).hom.app
        ((homologyFunctor B n).obj K) ≫
      G.rightDerivedZeroIsoSelf.hom.app ((homologyFunctor B n).obj K) ≫ h := by
  have key {X₀ X₁ X₂ X₃ X₄ X₅ X₆ : C} (f₁ : X₀ ⟶ X₁) (f₂ : X₁ ⟶ X₂) (f₃ : X₂ ⟶ X₃)
      (f₄ : X₃ ⟶ X₄) (f₅ : X₄ ⟶ X₅) (f₆ : X₅ ⟶ X₆) :
      (f₁ ≫ f₂ ≫ f₃ ≫ f₄ ≫ f₅) ≫ f₆ = f₁ ≫ f₂ ≫ f₃ ≫ f₄ ≫ f₅ ≫ f₆ := by
    simp only [Category.assoc]
  rw [hypercohomologyLeftEdgeTargetIso_hom_app]
  exact key _ _ _ _ _ _

omit [IsGrothendieckAbelian.{vC} C] in
/-- The degree-zero form of the normalized derived comparison on a single object `A[0]`:
through the identifications `H⁰(RG(A[0])) ≅ G(A)` and `H⁰(RG'(β(A)[0])) ≅ G'(β(A))`, it is
the component `e.app A`. -/
lemma normalizedDerivedBaseChange_singleFunctor_zero (e : G ⋙ 𝟭 C ⟶ β ⋙ G') (A : B) :
    (DerivedCategory.Plus.homologyFunctor C 0).map ((normalizedDerivedBaseChange G G' β e).app
        ((DerivedCategory.Plus.singleFunctor B 0).obj A)) ≫
      (DerivedCategory.Plus.homologyFunctor C 0).map (G'.rightDerivedFunctorPlus.map
        ((β.mapDerivedCategoryPlusSingleFunctor 0).hom.app A)) ≫
      (G'.singleFunctorCompRightDerivedFunctorPlusCompHomologyFunctorIso 0).hom.app (β.obj A) ≫
      G'.rightDerivedZeroIsoSelf.hom.app (β.obj A) =
    (G.singleFunctorCompRightDerivedFunctorPlusCompHomologyFunctorIso 0).hom.app A ≫
      G.rightDerivedZeroIsoSelf.hom.app A ≫ e.app A := by
  have hz := rightDerivedBaseChange_zero_unit e A
  rw [rightDerivedBaseChange_app, identityDerivedHomologyComparison] at hz
  have hz' := congrArg (fun f ↦
    (G.singleFunctorCompRightDerivedFunctorPlusCompHomologyFunctorIso 0).hom.app A ≫
      G.rightDerivedZeroIsoSelf.hom.app A ≫ f ≫ G'.rightDerivedZeroIsoSelf.hom.app (β.obj A)) hz
  simp only [Functor.id_map, Category.assoc, rightDerivedZeroIsoSelf_hom_inv_id_app_assoc,
    rightDerivedZeroIsoSelf_inv_hom_id_app, Iso.hom_inv_id_app_assoc] at hz'
  erw [Category.comp_id] at hz'
  rw [← hz']
  simp [normalizedDerivedBaseChange]

omit [IsGrothendieckAbelian.{vC} C] [PreservesFiniteLimits G] [PreservesFiniteLimits G'] in
/-- On homology, the normalized derived comparison is the identity homology comparison
followed by the derived base change morphism. -/
lemma homologyFunctor_map_normalizedDerivedBaseChange_app (e : G ⋙ 𝟭 C ⟶ β ⋙ G') (n : ℤ)
    (N : DerivedCategory.Plus B) :
    (DerivedCategory.Plus.homologyFunctor C n).map
        ((normalizedDerivedBaseChange G G' β e).app N) =
      ((𝟭 C).mapDerivedCategoryPlusHomologyFunctorIso n).hom.app
          (G.rightDerivedFunctorPlus.obj N) ≫
        (DerivedCategory.Plus.homologyFunctor C n).map
          ((rightDerivedFunctorPlusBaseChange e).app N) := by
  rw [identityDerivedHomologyComparison]
  simp [normalizedDerivedBaseChange]

omit [IsGrothendieckAbelian.{vC} C] [PreservesFiniteLimits G] [PreservesFiniteLimits G'] in
/-- On homology, the normalized derived comparison commutes with the shift comparisons
`Functor.homologyFunctorCommShiftIso` of `RG` and `RG'`. -/
lemma homologyFunctor_map_normalizedDerivedBaseChange_shift (e : G ⋙ 𝟭 C ⟶ β ⋙ G')
    (Y : DerivedCategory.Plus B) (m a a' : ℤ) (h : m + a = a') :
    (homologyFunctorCommShiftIso G.rightDerivedFunctorPlus m a a' h).hom.app Y ≫
      (DerivedCategory.Plus.homologyFunctor C a').map
        ((normalizedDerivedBaseChange G G' β e).app Y) =
    (DerivedCategory.Plus.homologyFunctor C a).map
        ((normalizedDerivedBaseChange G G' β e).app (Y⟦m⟧)) ≫
      (DerivedCategory.Plus.homologyFunctor C a).map
        (G'.rightDerivedFunctorPlus.map ((β.mapDerivedCategoryPlus.commShiftIso m).hom.app Y)) ≫
      (homologyFunctorCommShiftIso G'.rightDerivedFunctorPlus m a a' h).hom.app
        (β.mapDerivedCategoryPlus.obj Y) := by
  have := rightDerivedFunctorPlusBaseChange_homologyFunctor_shiftIso e Y m a a' h
  simp only [Functor.id_map] at this
  rw [homologyFunctor_map_normalizedDerivedBaseChange_app,
    homologyFunctor_map_normalizedDerivedBaseChange_app, Category.assoc]
  exact this

omit [IsGrothendieckAbelian.{vC} C] in
open DerivedCategory.Plus in
/-- The comparison on the interval `[q, q + 1)`: the normalized derived comparison followed
by `RG'` of the truncation comparison of `β`, read through the left-edge target
identifications, is `e` at `Hᵠ(K)` followed by `G'` of the homology comparison of `β`. -/
lemma normalizedDerivedBaseChange_hypercohomologyLeftEdgeTargetIso (e : G ⋙ 𝟭 C ⟶ β ⋙ G')
    (K : DerivedCategory.Plus B) (q : ℕ) :
    (homologyFunctor C q).map ((normalizedDerivedBaseChange G G' β e).app
        ((TStructure.t.eTruncGE.obj ((q : ℤ) : EInt)).obj
          ((TStructure.t.eTruncLT.obj ((q + 1 : ℤ) : EInt)).obj K))) ≫
      (homologyFunctor C q).map (G'.rightDerivedFunctorPlus.map
        (β.mapDerivedCategoryPlus.eTruncGELTIsoApp TStructure.t TStructure.t (q : ℤ)
          ((q + 1 : ℤ) : EInt) K).hom) ≫
      (G'.hypercohomologyLeftEdgeTargetIso q).hom.app (β.mapDerivedCategoryPlus.obj K) =
    (G.hypercohomologyLeftEdgeTargetIso q).hom.app K ≫
      e.app ((homologyFunctor B q).obj K) ≫
      G'.map ((β.mapDerivedCategoryPlusHomologyFunctorIso q).hom.app K) := by
  rw [hypercohomologyLeftEdgeTargetIso_hom_app_comp, hypercohomologyLeftEdgeTargetIso_hom_app]
  -- the truncation comparison of `β` in terms of the single-degree identification
  have hψ := β.mapDerivedCategoryPlus_eTruncGELTIsoApp_eTruncLTCompETruncGEIso (q : ℤ) K (𝟙 _)
  simp only [Functor.map_id, Category.id_comp] at hψ
  have hψ' := congrArg (fun f ↦ (homologyFunctor C q).map (G'.rightDerivedFunctorPlus.map f)) hψ
  simp only [Functor.map_comp] at hψ'
  rw [reassoc_of% hψ']
  -- naturality of the normalized comparison
  have hτ := congrArg (homologyFunctor C q).map ((normalizedDerivedBaseChange G G' β e).naturality
    ((eTruncLTCompETruncGEIso (q : ℤ)).hom.app K ≫
      ((singleFunctors B).shiftIso (-(q : ℤ)) q 0 (by simp)).inv.app ((homologyFunctor B q).obj K)))
  simp only [Functor.map_comp, Functor.comp_map, Category.assoc] at hτ
  rw [reassoc_of% hτ.symm]
  refine congrArg ((homologyFunctor C q).map _ ≫ ·) (congrArg ((homologyFunctor C q).map _ ≫ ·) ?_)
  erw [Functor.map_id, Functor.map_id, Functor.map_id, Functor.map_id, Category.id_comp]
  -- move the single-object comparisons past the shift comparison of `RG'`
  have n₁ := (homologyFunctorCommShiftIso G'.rightDerivedFunctorPlus (-(q : ℤ)) q 0
    (by simp)).hom.naturality ((β.mapDerivedCategoryPlusSingleFunctor 0).hom.app
      ((homologyFunctor B q).obj K))
  have n₂ := (homologyFunctorCommShiftIso G'.rightDerivedFunctorPlus (-(q : ℤ)) q 0
    (by simp)).hom.naturality
      ((singleFunctor B' 0).map ((β.mapDerivedCategoryPlusHomologyFunctorIso q).hom.app K))
  simp only [Functor.comp_map] at n₁ n₂
  rw [reassoc_of% n₂, reassoc_of% n₁]
  -- shift compatibility of the normalized comparison
  have hs := homologyFunctor_map_normalizedDerivedBaseChange_shift G G' β e
    ((singleFunctor B 0).obj ((homologyFunctor B q).obj K)) (-(q : ℤ)) q 0 (by simp)
  rw [← reassoc_of% hs]
  -- reduce to degree zero
  have n₃ := (G'.singleFunctorCompRightDerivedFunctorPlusCompHomologyFunctorIso 0).hom.naturality
    ((β.mapDerivedCategoryPlusHomologyFunctorIso q).hom.app K)
  have n₄ := G'.rightDerivedZeroIsoSelf.hom.naturality
    ((β.mapDerivedCategoryPlusHomologyFunctorIso q).hom.app K)
  simp only [Functor.comp_map] at n₃
  erw [reassoc_of% n₃, n₄]
  erw [reassoc_of% normalizedDerivedBaseChange_singleFunctor_zero]

open DerivedCategory.Plus in
/-- The natural transformation `Hⁿ(RG(τ_{≥ a} τ_{< b} K)) ⟶ Hⁿ(RG'(τ_{≥ a} τ_{< b} β(K)))`
induced by the normalized derived comparison and the truncation comparisons of `β`. -/
noncomputable def hypercohomologyExactComparisonH (e : G ⋙ 𝟭 C ⟶ β ⋙ G')
    (K : DerivedCategory.Plus B) (n : ℤ) :
    (G.hypercohomologySpectralObjectFunctor.obj K).H n ⟶
      (G'.hypercohomologySpectralObjectFunctor.obj (β.mapDerivedCategoryPlus.obj K)).H n :=
  Functor.whiskerLeft (TStructure.t.spectralObject K).ω₁
      (Functor.whiskerRight (normalizedDerivedBaseChange G G' β e)
        ((homologyFunctor C 0).shift n)) ≫
    Functor.whiskerRight (β.mapDerivedCategoryPlus.mapTriangulatedSpectralObjectObjIso
      TStructure.t TStructure.t K).hom.hom
        (G'.rightDerivedFunctorPlus ⋙ (homologyFunctor C 0).shift n)

omit [IsGrothendieckAbelian.{vC} C] [PreservesFiniteLimits G] [PreservesFiniteLimits G'] in
open DerivedCategory.Plus in
/-- The component of `Functor.hypercohomologyExactComparisonH` at an interval `D`. -/
lemma hypercohomologyExactComparisonH_app (e : G ⋙ 𝟭 C ⟶ β ⋙ G')
    (K : DerivedCategory.Plus B) (n : ℤ) (D : ComposableArrows EInt 1) :
    (hypercohomologyExactComparisonH G G' β e K n).app D =
      ((homologyFunctor C 0).shift n).map ((normalizedDerivedBaseChange G G' β e).app
        ((TStructure.t.eTruncGE.obj (D.obj 0)).obj ((TStructure.t.eTruncLT.obj (D.obj 1)).obj K))) ≫
      ((homologyFunctor C 0).shift n).map (G'.rightDerivedFunctorPlus.map
        (β.mapDerivedCategoryPlus.eTruncGELTIsoApp TStructure.t TStructure.t (D.obj 0) (D.obj 1)
          K).hom) :=
  rfl

-- Keep the original Grothendieck hypotheses in the public signature.
set_option linter.unusedSectionVars false in
/-- Exact comparison preserves the canonical normalized hypercohomology left edge.
Source: functoriality of the truncation spectral object and the derived base-change
unit equation (blueprint: lem-pur-hypercohomology-edge-exact-comparison).

Proof:
1. Write τ for the normalized derived comparison. It commutes with shifts: the
canonical derived-identity isomorphism does so after restriction to the bounded-below
homotopy category, and `rightDerivedFunctorPlusBaseChange` commutes with shifts by
its unit characterization. The comparison of truncation spectral objects is the
composite of `τ.mapTriangulatedSpectralObject`, the functor-composition comparison,
and the image under RG' of `β.mapTriangulatedSpectralObjectObjIso`.
2. Apply `Abelian.SpectralObject.leftEdge_naturality`. On the interval from bottom
to top its component is H^q(τ_K), because both extended truncations are identities.
3. On the interval [q,q+1), identify each truncation with H^q(K)[-q]. The identity
`mapDerivedCategoryPlus_eTruncGELTIsoApp_eTruncLTCompETruncGEIso`, with ψ the identity,
identifies the β-truncation comparison with β applied to the single-degree
identification, followed by β's shift comparison, its single-functor comparison,
and the single functor applied to its homology comparison.
4. Naturality of τ moves the single-degree identification past τ. Its shift
compatibility and homology-shift naturality reduce the remaining comparison to
an object in degree zero. Apply `rightDerivedBaseChange_zero_unit`: cancel the
invertible degree-zero unit of G, and use the canonical single/derived homology
isomorphisms. This gives e at H^q(K), followed by G' of β's homology comparison.
Substitute this target component in Step 2 and associate the composites. -/
theorem hypercohomologyLeftEdge_exactComparison (e : G ⋙ 𝟭 C ⟶ β ⋙ G')
    (K : DerivedCategory.Plus B) [K.IsGE 0]
    [(β.mapDerivedCategoryPlus.obj K).IsGE 0] (q : ℕ) :
    (DerivedCategory.Plus.homologyFunctor C q).map
        ((normalizedDerivedBaseChange G G' β e).app K) ≫
      (G'.hypercohomologySpectralObjectFunctor.obj (β.mapDerivedCategoryPlus.obj K)).leftEdge q ≫
      (G'.hypercohomologyLeftEdgeTargetIso q).hom.app (β.mapDerivedCategoryPlus.obj K) =
    (G.hypercohomologySpectralObjectFunctor.obj K).leftEdge q ≫
      (G.hypercohomologyLeftEdgeTargetIso q).hom.app K ≫
      e.app ((DerivedCategory.Plus.homologyFunctor B q).obj K) ≫
      G'.map ((β.mapDerivedCategoryPlusHomologyFunctorIso q).hom.app K) := by
  have h := Abelian.SpectralObject.leftEdge_naturality_of_natTrans (q : ℤ)
    (hypercohomologyExactComparisonH G G' β e K q)
  have hbot : (hypercohomologyExactComparisonH G G' β e K q).app
      (ComposableArrows.mk₁ (homOfLE (bot_le : (⊥ : EInt) ≤ ⊤))) =
      (DerivedCategory.Plus.homologyFunctor C q).map
        ((normalizedDerivedBaseChange G G' β e).app K) := by
    rw [hypercohomologyExactComparisonH_app]
    erw [eTruncGELTIsoApp_bot_top_hom, Functor.map_id, Functor.map_id, Category.comp_id]
    rfl
  rw [← hbot]
  erw [reassoc_of% h]
  exact congrArg (_ ≫ ·) ((Category.assoc _ _ _).trans
    (normalizedDerivedBaseChange_hypercohomologyLeftEdgeTargetIso G G' β e K q))

end CategoryTheory.Functor
