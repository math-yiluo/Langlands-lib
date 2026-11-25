/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.RationalP1.Scalar.RationalP1ScalarChernMaps
import WeilConjectures.AlgebraicGeometry.RationalP1.Scalar.RationalP1ScalarChernP2Splitting
import WeilConjectures.AlgebraicGeometry.RationalP1.Scalar.RationalP1ScalarChernBaseChange
import all WeilConjectures.AlgebraicGeometry.RationalP1.RationalP1UnitCounit
import WeilConjectures.AlgebraicGeometry.RationalP1.RationalP1LineFromPreservation
import WeilConjectures.AlgebraicGeometry.RationalP1.Second.RationalP1SecondPretraceData
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Line
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperStarCoherence
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import Mathlib.CategoryTheory.Preadditive.Biproducts

/-! # An inverse for the scalar projective-line splitting

We descend the second-projection splitting through proper base change. Pullback
by the projective-line projection reflects isomorphisms because of its section
at infinity.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.RationalP1
open DiagonalCoefficients CondensedRing

attribute [local irreducible] coefficient line diagram trace singleUnitIso
attribute [local irreducible] moduleObjectDerivedPullback moduleObjectDerivedPushforward
attribute [local irreducible] firstProjection secondProjection square condensedAmbientExchange
attribute [local irreducible] Functor.leftDerivedFunctor Functor.rightDerivedFunctor
attribute [local irreducible] CondensedRing.upperStar CondensedRing.lowerStar

private theorem isIso_desc_of_exchange
    {C D : Type*} [Category C] [Category D] [Preadditive C] [Preadditive D]
    [HasBinaryBiproducts C] [HasBinaryBiproducts D]
    (F : C ⥤ D) [F.Additive] {U V W : C} {U' V' W' : D}
    (a : U ⟶ W) (b : V ⟶ W) (a' : U' ⟶ W') (b' : V' ⟶ W')
    (e : F.obj U ≅ U') (e' : F.obj V ≅ V') (β : F.obj W ⟶ W')
    [IsIso β] [IsIso (biprod.desc a' b')]
    (ha : F.map a ≫ β = e.hom ≫ a')
    (hb : F.map b ≫ β = e'.hom ≫ b') :
    IsIso (F.map (biprod.desc a b)) := by
  let : PreservesBinaryBiproducts F := preservesBinaryBiproducts_of_preservesBiproducts F
  have h : (F.mapBiprod U V).inv ≫ F.map (biprod.desc a b) ≫ β =
      (biprod.mapIso e e').hom ≫ biprod.desc a' b' := by
    rw [← Category.assoc, biprod.mapBiprod_inv_map_desc]
    apply biprod.hom_ext'
    · simpa only [Category.assoc, biprod.inl_desc_assoc, biprod.mapIso_hom,
        biprod.inl_map_assoc, biprod.inl_desc] using ha
    · simpa only [Category.assoc, biprod.inr_desc_assoc, biprod.mapIso_hom,
        biprod.inr_map_assoc, biprod.inr_desc] using hb
  have : IsIso ((F.mapBiprod U V).inv ≫ F.map (biprod.desc a b) ≫ β) := by
    rw [h]
    infer_instance
  have : IsIso (F.map (biprod.desc a b) ≫ β) :=
    IsIso.of_isIso_comp_left (F.mapBiprod U V).inv _
  exact IsIso.of_isIso_comp_right _ β

private theorem left_inverse_of_exchange
    {C D : Type*} [Category C] [Category D] [Preadditive C] [Preadditive D]
    [HasBinaryBiproducts C] [HasBinaryBiproducts D]
    (F : C ⥤ D) [F.Additive] [F.ReflectsIsomorphisms]
    {U V W : C} {U' V' W' : D}
    (a : U ⟶ W) (b : V ⟶ W) (a' : U' ⟶ W') (b' : V' ⟶ W')
    (e : F.obj U ≅ U') (e' : F.obj V ≅ V') (β : F.obj W ⟶ W')
    [IsIso β] [IsIso (biprod.desc a' b')]
    (ha : F.map a ≫ β = e.hom ≫ a')
    (hb : F.map b ≫ β = e'.hom ≫ b') :
    ∃ v, v ≫ biprod.desc a b = 𝟙 _ := by
  have : IsIso (F.map (biprod.desc a b)) :=
    isIso_desc_of_exchange F a b a' b' e e' β ha hb
  have : IsIso (biprod.desc a b) := isIso_of_reflects_iso (biprod.desc a b) F
  exact ⟨inv (biprod.desc a b), IsIso.inv_hom_id _⟩

private theorem pullback_additive
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (moduleObjectDerivedPullback Λ f).Additive := by
  unfold moduleObjectDerivedPullback
  infer_instance

private theorem reflects_pullback_projectiveLine
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (Y : Scheme.{u}) :
    (moduleObjectDerivedPullback Λ (ProjectiveLine Y ↘ Y)).ReflectsIsomorphisms := by
  unfold moduleObjectDerivedPullback
  let F := (CondensedRing.upperStar Λ (ProjectiveLine Y ↘ Y)).leftDerivedFunctor
  let G := (CondensedRing.upperStar Λ (ProjectiveLine.infinity Y)).leftDerivedFunctor
  let e : F ⋙ G ≅ 𝟭 _ :=
    (CondensedRing.leftDerivedUpperStarComp Λ
      (ProjectiveLine.infinity Y) (ProjectiveLine Y ↘ Y)).symm ≪≫
      eqToIso (congrArg
        (fun f : Y ⟶ Y ↦ (CondensedRing.upperStar Λ f).leftDerivedFunctor)
        ProjectiveLine.infinity_over) ≪≫ CondensedRing.leftDerivedUpperStarId Λ Y
  have : (F ⋙ G).ReflectsIsomorphisms := reflectsIsomorphisms_of_iso e.symm
  exact reflectsIsomorphisms_of_comp F G

private theorem exchange_wrapper_isIso
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (Y : Scheme.{u})
    (M : DerivedCategory (Modules Λ (ProjectiveLine Y)))
    (h : unitExchangeInversion Λ Y M) :
    IsIso (secondPretraceExchangeMap Λ Y M) := by
  unfold unitExchangeInversion at h
  exact secondPretraceExchangeMap_isIso Λ Y M h

private theorem second_exchange_iso
    (l : ℕ) [Fact l.Prime] (c : Option (PadicAlgCl.FiniteIntermediateField l))
    (k : Type u) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p] (hpl : p ≠ l)
    (Y : Scheme.{u}) [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))] :
    IsIso (secondTraceExchange l c k p hpl Y) := by
  let Λ := (coefficient l c).X
  let T := (((DerivedCategory.singleFunctor (Modules Λ (ProjectiveLine Y)) 0).obj
    (line l c (ProjectiveLine Y))) ⟦(2 : ℤ)⟧)
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace (Y ↘ Spec (.of k))
  have : QuasiSeparatedSpace Y :=
    quasiSeparatedSpace_of_quasiSeparated (Y ↘ Spec (.of k))
  have hline := line_localizing_of_preservation Λ (ProjectiveLine Y ↘ Y)
    (line l c (ProjectiveLine Y)) (localizingPreservation l c k p hpl Y).2
  have hx := unit_exchange_isIso l c k p hpl Y ⟨T, hline⟩
  have : IsIso (secondPretraceExchangeMap Λ Y T) :=
    exchange_wrapper_isIso Λ Y T hx
  unfold secondTraceExchange
  infer_instance

set_option linter.unusedVariables false in
-- Preserve the common displayed P2 setup in the fixed statement.
/-- The explicit scalar Q biproduct map has a left inverse. -/
theorem scalar_q_chern_left_inverse
    (l : ℕ) [Fact l.Prime] (c : Option (PadicAlgCl.FiniteIntermediateField l))
    (k : Type u) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p] (hpl : p ≠ l)
    (Y : Scheme.{u}) [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))]
    [IsNoetherian Y] [IsNoetherian (ProjectiveLine Y)] [IsNoetherian (diagonalSurface Y)]
    [DiagonalTraceLocalizations l Y]
    [DiagonalTraceLocalizations l (ProjectiveLine Y)]
    [DiagonalTraceLocalizations l (diagonalSurface Y)]
    (δ : diagonalCompletedDomain l Y ⟶ diagonalCompletedCodomain l Y)
    (family : Family l Y) (r : Reference l Y δ family)
    (a : DiagonalTrace.completedUnit l Y ⟶
      r.tq.Rc.R.obj ((DiagonalTrace.completedLine l (ProjectiveLine Y)) ⟦(2 : ℤ)⟧))
    (ha : CompletedChernNormalized l r.tq.toPresentation a)
    (b : DiagonalTrace.completedUnit l (ProjectiveLine Y) ⟶
      r.t₂.Rc.R.obj ((DiagonalTrace.completedLine l (diagonalSurface Y)) ⟦(2 : ℤ)⟧))
    (hb : CompletedChernNormalized l r.t₂.toPresentation b) :
    let Λ := (coefficient l c).X
    let L := line l c
    let T := fun X : Scheme.{u} ↦
      ((DerivedCategory.singleFunctor (Modules Λ X) 0).obj (L X)) ⟦(2 : ℤ)⟧
    let uq := scalarTwistedUnit Λ (ProjectiveLine Y ↘ Y) (T Y) (T (ProjectiveLine Y))
      (scalarQLineIso l c k p hpl Y)
    let u₂ := scalarTwistedUnit Λ (secondProjection Y)
      (T (ProjectiveLine Y)) (T (diagonalSurface Y)) (secondLineComparison l c k p hpl Y)
    let cq := scalarQChern l c Y r a
    let c₂ := scalarP2Chern l c Y r b
    ∃ v, v ≫ biprod.desc uq cq = 𝟙 _ := by
  let Λ := (coefficient l c).X
  let T := fun X : Scheme.{u} ↦
    ((DerivedCategory.singleFunctor (Modules Λ X) 0).obj (line l c X)) ⟦(2 : ℤ)⟧
  let F := moduleObjectDerivedPullback Λ (ProjectiveLine Y ↘ Y)
  let uq := scalarTwistedUnit Λ (ProjectiveLine Y ↘ Y) (T Y) (T (ProjectiveLine Y))
    (scalarQLineIso l c k p hpl Y)
  let u₂ := scalarTwistedUnit Λ (secondProjection Y) (T (ProjectiveLine Y))
    (T (diagonalSurface Y)) (secondLineComparison l c k p hpl Y)
  let cq := scalarQChern l c Y r a
  let c₂ := scalarP2Chern l c Y r b
  have hβ : IsIso (secondTraceExchange l c k p hpl Y) :=
    second_exchange_iso l c k p hpl Y
  have h₂ : IsIso (biprod.desc u₂ c₂) :=
    scalar_p2_chern_splitting l c k p hpl Y δ family r a ha b hb
  have hchange := scalar_chern_base_change l c k p hpl Y δ family r a ha b hb
  have : F.Additive := pullback_additive Λ (ProjectiveLine Y ↘ Y)
  have : F.ReflectsIsomorphisms := reflects_pullback_projectiveLine Λ Y
  exact left_inverse_of_exchange F uq cq u₂ c₂ (scalarQLineIso l c k p hpl Y)
    (scalarUnitPullIso Λ Y) (secondTraceExchange l c k p hpl Y) hchange.1 hchange.2

end AlgebraicGeometry.ProEtale.RationalP1
