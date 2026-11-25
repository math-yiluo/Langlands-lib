/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.RationalP1.Second.RationalP1SecondPretraceData

import WeilConjectures.AlgebraicGeometry.RationalP1.Second.RationalP1SecondExchangeProjection
import WeilConjectures.AlgebraicGeometry.RationalP1.Second.RationalP1SecondProjectionInterchange

/-! # The second projective-line calculation before applying a trace
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.RationalP1
open DiagonalCoefficients CondensedRing

attribute [local irreducible] coefficient line twist projectionMap tensorShiftIso
attribute [local irreducible] secondLineComparison twistProjectionMap
attribute [local irreducible] moduleObjectDerivedPullback moduleObjectDerivedPushforward
attribute [local irreducible] firstProjection secondProjection square condensedAmbientExchange

private theorem transport_forward
    {C D : Type*} [Category* C] [Category* D] (H : C ⥤ D)
    {A B : C} {X Y Z : D} (s : X ⟶ H.obj A) (p : H.obj B ⟶ Z)
    (d : X ⟶ Y) (j : Y ⟶ Z) {x y : A ⟶ B} (he : x = y)
    (h : s ≫ H.map y ≫ p = d ≫ j) : s ≫ H.map x ≫ p = d ≫ j := by
  rw [he]
  exact h

private theorem inverse_square
    {C D : Type*} [Category* C] [Category* D]
    (H : C ⥤ D) {A B C' E : C} {X Y Z : D}
    (a : A ⟶ B) (t : B ≅ C') (b : C' ⟶ E) (p : H.obj E ⟶ Z)
    (s : Y ⟶ H.obj A) (d : Y ⟶ X) (j : X ⟶ Z)
    [ha : IsIso a] [hb : IsIso b] [hp : IsIso p] [hd : IsIso d]
    (h : s ≫ H.map (a ≫ t.hom ≫ b) ≫ p = d ≫ j) :
    j ≫ (inv p ≫ H.map (inv b)) ≫ H.map (t.inv ≫ inv a) = inv d ≫ s := by
  apply (cancel_epi d).1
  simp only [IsIso.hom_inv_id_assoc]
  rw [← reassoc_of% h]
  simp only [Functor.map_comp, Category.assoc, Functor.map_inv,
    IsIso.hom_inv_id_assoc, Iso.hom_inv_id_map_assoc, IsIso.hom_inv_id, Category.comp_id]

private theorem assemble_pretrace
    {C D E : Type*} [Category* C] [Category* D] [Category* E] [mE : MonoidalCategory E]
    (F : D ⥤ C) (R : C ⥤ D) (H : C ⥤ E)
    {A : D} {B C' Q : C} {M V W Z : E}
    (a : A ⟶ R.obj B) (t : B ≅ C') (b : F.obj (R.obj C') ⟶ Q)
    (p : H.obj Q ⟶ Z) (β : V ⟶ W)
    (s : M ⊗ V ⟶ H.obj (F.obj A)) (j : M ⊗ W ⟶ Z)
    (c : R.obj C' ⟶ A) (v : Z ⟶ H.obj (F.obj (R.obj C')))
    [ha : IsIso a] [hb : IsIso b] [hp : IsIso p] [hx : IsIso β]
    (h : s ≫ H.map (F.map a ≫ (F.mapIso (R.mapIso t)).hom ≫ b) ≫ p =
      (M ◁ β) ≫ j)
    (hc : c = R.map t.inv ≫ inv a) (hv : v = inv p ≫ H.map (inv b)) :
    j ≫ v ≫ H.map (F.map c) = (M ◁ inv β) ≫ s := by
  rw [hc, hv]
  have hi := inverse_square H (F.map a) (F.mapIso (R.mapIso t)) b p s (M ◁ β) j h
  simpa only [Functor.map_comp, Functor.mapIso_inv, Functor.map_inv,
    inv_whiskerLeft] using hi

-- Keep native exchange comparisons abstract in the coefficient and object variables.
private theorem generic_record_assembly
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (Y : Scheme.{u})
    (L : ∀ X : Scheme.{u}, Modules Λ X)
    (e : (moduleObjectDerivedPullback Λ (secondProjection Y)).obj
      (((DerivedCategory.singleFunctor (Modules Λ (ProjectiveLine Y)) 0).obj
        (L (ProjectiveLine Y))) ⟦(2 : ℤ)⟧) ≅
      ((DerivedCategory.singleFunctor (Modules Λ (diagonalSurface Y)) 0).obj
        (L (diagonalSurface Y))) ⟦(2 : ℤ)⟧)
    (A : DerivedCategory (Modules Λ Y))
    (B M : DerivedCategory (Modules Λ (ProjectiveLine Y)))
    (V : DerivedCategory (Modules Λ Y))
    (X : DerivedCategory (Modules Λ (ProjectiveLine Y))) :
    let F := moduleObjectDerivedPullback Λ (ProjectiveLine Y ↘ Y)
    let R := moduleObjectDerivedPushforward Λ (ProjectiveLine Y ↘ Y)
    let H := twist Λ (ProjectiveLine Y) (L (ProjectiveLine Y))
    let b := secondPretraceExchangeMap Λ Y M
    let τ := twistProjectionMap Λ (secondProjection Y)
      (L (ProjectiveLine Y)) (L (diagonalSurface Y)) e
      ((moduleObjectDerivedPullback Λ (firstProjection Y)).obj M)
    ∀ (a : A ⟶ R.obj B) (ha : IsIso a) (t : B ≅ M) (c : R.obj M ⟶ A)
      (β : F.obj V ⟶ X) (hx : IsIso β)
      (s : M ⊗ F.obj V ⟶ H.obj (F.obj A))
      (j : M ⊗ X ⟶ (moduleObjectDerivedPushforward Λ (secondProjection Y)).obj
        ((twist Λ (diagonalSurface Y) (L (diagonalSurface Y))).obj
          ((moduleObjectDerivedPullback Λ (firstProjection Y)).obj M))),
      c = R.map t.inv ≫ @inv _ _ _ _ a ha →
      s ≫ H.map (F.map a ≫ (F.mapIso (R.mapIso t)).hom ≫ b) ≫ τ = (M ◁ β) ≫ j →
      SecondPretraceEquation Λ Y L e M (H.obj (F.obj A)) X V
        (H.map (F.map c)) (@inv _ _ _ _ β hx) s j := by
  dsimp only
  intro a ha t c β hx s j hc h
  let F := moduleObjectDerivedPullback Λ (ProjectiveLine Y ↘ Y)
  let R := moduleObjectDerivedPushforward Λ (ProjectiveLine Y ↘ Y)
  let H := twist Λ (ProjectiveLine Y) (L (ProjectiveLine Y))
  let b := secondPretraceExchangeMap Λ Y M
  let τ := twistProjectionMap Λ (secondProjection Y)
    (L (ProjectiveLine Y)) (L (diagonalSurface Y)) e
    ((moduleObjectDerivedPullback Λ (firstProjection Y)).obj M)
  constructor
  intro hb hp
  have hbIso : IsIso b := secondPretraceExchangeMap_isIso Λ Y M hb
  have hpIso : IsIso τ := hp
  have hbInv : ambientExchangeInverse Λ (square Y) M hb = @inv _ _ _ _ b hbIso :=
    secondPretraceExchangeMap_inverse Λ Y M hb
  have hu : unitTail Λ Y L e M hb hp = inv τ ≫ H.map (@inv _ _ _ _ b hbIso) := by
    unfold unitTail
    rw [hbInv]
  exact assemble_pretrace F R H a t b τ β s j c (unitTail Λ Y L e M hb hp)
    (ha := ha) (hb := hbIso) (hp := hpIso) (hx := hx) h hc hu

-- Apply the abstract record assembly without unfolding the native derived choices.
/-- Exchange/projection reordering before applying any scalar trace.
The only inverses are the specified exchange and projection arrows. In particular,
this statement has no completed reference, diagonal class, counit, or trace map. -/
theorem second_pretrace
    (l : ℕ) [Fact l.Prime] (c : Option (PadicAlgCl.FiniteIntermediateField l))
    (k : Type u) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p] (hpl : p ≠ l)
    (Y : Scheme.{u}) [Y.Over (Spec (.of k))]
    (K : DerivedCategory (Modules (coefficient l c).X Y))
    (hq : IsIso (projectionMap (coefficient l c).X (ProjectiveLine Y ↘ Y) K
      (((DerivedCategory.singleFunctor (Modules (coefficient l c).X (ProjectiveLine Y))
        0).obj (line l c (ProjectiveLine Y))) ⟦(2 : ℤ)⟧)))
    (hx : IsIso (secondTraceExchange l c k p hpl Y)) :
    SecondPretraceEquation (coefficient l c).X Y (line l c)
      (secondLineComparison l c k p hpl Y)
      ((twist (coefficient l c).X (ProjectiveLine Y) (line l c (ProjectiveLine Y))).obj
        ((moduleObjectDerivedPullback (coefficient l c).X (ProjectiveLine Y ↘ Y)).obj K))
      ((twist (coefficient l c).X (ProjectiveLine Y) (line l c (ProjectiveLine Y))).obj
        ((moduleObjectDerivedPullback (coefficient l c).X (ProjectiveLine Y ↘ Y)).obj
          (K ⊗ (moduleObjectDerivedPushforward (coefficient l c).X
            (ProjectiveLine Y ↘ Y)).obj
              (((DerivedCategory.singleFunctor (Modules (coefficient l c).X
                (ProjectiveLine Y)) 0).obj (line l c (ProjectiveLine Y))) ⟦(2 : ℤ)⟧))))
      ((moduleObjectDerivedPushforward (coefficient l c).X (secondProjection Y)).obj
        (((DerivedCategory.singleFunctor (Modules (coefficient l c).X (diagonalSurface Y))
          0).obj (line l c (diagonalSurface Y))) ⟦(2 : ℤ)⟧))
      ((moduleObjectDerivedPushforward (coefficient l c).X (ProjectiveLine Y ↘ Y)).obj
        (((DerivedCategory.singleFunctor (Modules (coefficient l c).X (ProjectiveLine Y))
          0).obj (line l c (ProjectiveLine Y))) ⟦(2 : ℤ)⟧))
      ((twist (coefficient l c).X (ProjectiveLine Y) (line l c (ProjectiveLine Y))).map
        ((moduleObjectDerivedPullback (coefficient l c).X (ProjectiveLine Y ↘ Y)).map
          (counitProjectionPart (coefficient l c).X Y (line l c (ProjectiveLine Y)) K hq)))
      (@inv _ _ _ _ (secondTraceExchange l c k p hpl Y) hx)
      (secondTraceStrength (coefficient l c).X Y (line l c (ProjectiveLine Y)) K
        ((moduleObjectDerivedPushforward (coefficient l c).X (ProjectiveLine Y ↘ Y)).obj
          (((DerivedCategory.singleFunctor (Modules (coefficient l c).X (ProjectiveLine Y))
            0).obj (line l c (ProjectiveLine Y))) ⟦(2 : ℤ)⟧))).hom
      (secondForwardProjection l c k p hpl Y K) := by
  let Λ := (coefficient l c).X
  let F : DerivedCategory (Modules Λ Y) ⥤
      DerivedCategory (Modules Λ (ProjectiveLine Y)) :=
    moduleObjectDerivedPullback Λ (ProjectiveLine Y ↘ Y)
  let R : DerivedCategory (Modules Λ (ProjectiveLine Y)) ⥤
      DerivedCategory (Modules Λ Y) :=
    moduleObjectDerivedPushforward Λ (ProjectiveLine Y ↘ Y)
  let H := twist Λ (ProjectiveLine Y) (line l c (ProjectiveLine Y))
  let T := ((DerivedCategory.singleFunctor (Modules Λ (ProjectiveLine Y)) 0).obj
    (line l c (ProjectiveLine Y))) ⟦(2 : ℤ)⟧
  let M := (twist (coefficient l c).X (ProjectiveLine Y)
    (line l c (ProjectiveLine Y))).obj
      ((moduleObjectDerivedPullback (coefficient l c).X (ProjectiveLine Y ↘ Y)).obj K)
  let a := projectionMap Λ (ProjectiveLine Y ↘ Y) K T
  let t := tensorShiftIso Λ (ProjectiveLine Y) (line l c (ProjectiveLine Y)) (F.obj K)
  let b := secondPretraceExchangeMap Λ Y M
  let β := secondTraceExchange l c k p hpl Y
  let s := secondTraceStrength Λ Y (line l c (ProjectiveLine Y)) K (R.obj T)
  have haIso : IsIso a := hq
  have hxIso : IsIso β := hx
  have htwo := second_projection_interchange l c k p hpl Y K (R.obj T) β
  have he := second_exchange_projection l c k p hpl Y K
  let τ := twistProjectionMap Λ (secondProjection Y)
    (line l c (ProjectiveLine Y)) (line l c (diagonalSurface Y))
    (secondLineComparison l c k p hpl Y)
    ((moduleObjectDerivedPullback Λ (firstProjection Y)).obj M)
  have h : s.hom ≫ H.map (F.map a ≫ (F.mapIso (R.mapIso t)).hom ≫ b) ≫ τ =
      (M ◁ β) ≫ secondForwardProjection l c k p hpl Y K :=
    transport_forward H s.hom τ (M ◁ β)
      (secondForwardProjection l c k p hpl Y K) he htwo
  have hc : counitProjectionPart Λ Y (line l c (ProjectiveLine Y)) K hq =
      R.map t.inv ≫ inv a := by
    unfold counitProjectionPart
    rfl
  exact generic_record_assembly Λ Y (line l c) (secondLineComparison l c k p hpl Y)
    (K ⊗ R.obj T) (F.obj K ⊗ T) M (R.obj T)
    ((moduleObjectDerivedPushforward Λ (secondProjection Y)).obj
      (((DerivedCategory.singleFunctor (Modules Λ (diagonalSurface Y)) 0).obj
        (line l c (diagonalSurface Y))) ⟦(2 : ℤ)⟧))
    a haIso t (counitProjectionPart Λ Y (line l c (ProjectiveLine Y)) K hq)
    β hxIso s.hom (secondForwardProjection l c k p hpl Y K) hc h

end AlgebraicGeometry.ProEtale.RationalP1
