/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Coefficient.DiagonalCoefficientReference
public import WeilConjectures.AlgebraicGeometry.RationalP1.Scalar.RationalP1ScalarChernMaps
import all WeilConjectures.AlgebraicGeometry.RationalP1.DiagonalCompletedChernSplitting
import WeilConjectures.AlgebraicGeometry.RationalP1.RationalP1CompletedChernDegree

/-! # The realized trace as the second projection of its Chern splitting

Source: diagonal-tower coefficient changes, paragraph (3), the split trace projection.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.DiagonalCoefficients

private theorem conjugate_degree
    {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {U K : C} {V W Z : D} (b : U ⟶ K) (t : K ⟶ U)
    (u : F.obj U ⟶ V) [IsIso u] (k : F.obj K ≅ W)
    (q : W ⟶ Z) [IsIso q] (ht : b ≫ t = 𝟙 U) :
    (inv u ≫ F.map b ≫ k.hom ≫ q) ≫
      (inv q ≫ k.inv ≫ F.map t ≫ u) = 𝟙 V := by
  simp only [Category.assoc, IsIso.hom_inv_id_assoc, Iso.hom_inv_id_assoc]
  rw [← F.map_comp_assoc, ht, F.map_id, Category.id_comp, IsIso.inv_hom_id]

attribute [local irreducible] Functor.mapDerivedCategory
  CompletedRealization.singleUnit CompletedRealization.shiftedLine

-- The endpoint conversions compare the independently normalized realization functors.
/-- A realized completed trace kills the complementary shifted line and takes its
normalized Chern component to the identity.

Source: diagonal-tower trace proof (1) and coefficient changes (3).
(blueprint: lem-diagonal-realized-trace-splitting).

Proof: realize the completed unit/Chern splitting by the prescribed exact functor,
conjugating by its unit and shifted-line isomorphisms and the normalized push square.
The complementary component has source concentrated in degree minus two, so its
composite into the degree-zero unit vanishes by the standard t-structure. The Chern
component has degree one under the completed trace. Functoriality preserves that
identity, and cancellation of the realization and push-square isomorphisms gives
the asserted identity. This includes empty schemes and does not test derived maps
by finite evaluations. -/
theorem realizedTrace_splitting (l : ℕ) [Fact l.Prime]
    {X S : Scheme.{u}} [IsNoetherian X] [IsNoetherian S]
    [DiagonalTraceLocalizations l X] [DiagonalTraceLocalizations l S]
    (f : X ⟶ S) (hS : IsUnit (l : Γ(S, ⊤)))
    (eX : CompletedRealization l X) (eS : CompletedRealization l S)
    (t : DiagonalTrace.Result l (ULift.{u} (Padic l)) f)
    (D : DiagonalRightDerived
      (CondensedRing.lowerStar (Profinite.continuousMapRingObj.{u} ℤ_[l]) f))
    (push : CompletedPushSquare l f eX eS t.Rc D)
    (b : DiagonalTrace.completedUnit l S ⟶
      t.Rc.R.obj ((DiagonalTrace.completedLine l X)⟦(2 : ℤ)⟧))
    (hb : RationalP1.CompletedChernNormalized l t.toPresentation b) :
    have : IsIso (eX.shiftedLine l X) := by
      unfold CompletedRealization.shiftedLine
      infer_instance
    let Λ := Profinite.continuousMapRingObj.{u} ℤ_[l]
    let V := ((DerivedCategory.singleFunctor (Modules Λ S) 0).obj
      (zlLine l S))⟦(2 : ℤ)⟧
    let K := D.R.obj (((DerivedCategory.singleFunctor (Modules Λ X) 0).obj
      (zlLine l X))⟦(2 : ℤ)⟧)
    let τ := inv (D.R.map (eX.shiftedLine l X)) ≫
      push.derived.iso.inv.app _ ≫ eS.F.mapDerivedCategory.map t.trace ≫ eS.singleUnit l S
    let c := RationalP1.realizeScalarChern l f eX eS t.Rc D push b
    ∃ v : V ⟶ K, IsIso (biprod.desc v c) ∧ v ≫ τ = 0 ∧ c ≫ τ = 𝟙 _ := by
  dsimp only
  have : IsIso (eX.shiftedLine l X) := by
    unfold CompletedRealization.shiftedLine
    infer_instance
  obtain ⟨v, hv⟩ := RationalP1.realize_splitting l f eX eS t.Rc D push b
    (RationalP1.completed_chern_splitting l t hS b hb)
  refine ⟨v, hv, ?_, ?_⟩
  · have hle : (((DerivedCategory.singleFunctor
        (Modules (Profinite.continuousMapRingObj.{u} ℤ_[l]) S) 0).obj
          (zlLine l S))⟦(2 : ℤ)⟧).IsLE (-2) :=
      DerivedCategory.TStructure.t.isLE_shift _ 0 2 (-2) (by decide)
    exact DerivedCategory.TStructure.t.zero _ (-2) 0 (by decide)
  · have : IsIso (eS.singleUnit l S) := by
      unfold CompletedRealization.singleUnit
      infer_instance
    unfold RationalP1.realizeScalarChern
    exact conjugate_degree eS.F.mapDerivedCategory b t.trace (eS.singleUnit l S)
      (push.derived.iso.app _) (D.R.map (eX.shiftedLine l X))
      (RationalP1.completed_chern_degree l t hS b hb)

end AlgebraicGeometry.ProEtale.DiagonalCoefficients
