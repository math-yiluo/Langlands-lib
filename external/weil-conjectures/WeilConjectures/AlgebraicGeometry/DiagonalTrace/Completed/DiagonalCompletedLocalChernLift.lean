/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalTrace.Presentation.DiagonalTowerTracePresentations
import all WeilConjectures.AlgebraicGeometry.DiagonalTrace.Presentation.DiagonalCompletedChernLift

/-! # Lifting a local whole-system Chern arrow to completed coefficients -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.ProEtale.DiagonalTrace

attribute [local irreducible] Functor.mapDerivedCategory

/-- A local tower Chern arrow has a unique completed lift with its whole-system
normalization.

Source: diagonal trace proof (1), full faithfulness on complete objects.
(blueprint: lem-diagonal-completed-local-chern-lift).

Proof: the completed unit and the shifted completed Tate line are complete.
The line comparison into the derived tower limit is invertible. Compose the
unit comparison with the derived limit of the specified tower arrow and the
inverse line comparison. Fullness on complete objects lifts this map, and
faithfulness and invertibility of the line comparison give uniqueness. -/
theorem diagonalCompletedLocalChern_lift (l : ℕ) [Fact l.Prime]
    {X S : Scheme.{u}} [IsNoetherian X] [DiagonalTraceLocalizations l X]
    [DiagonalTraceLocalizations l S] {f : X ⟶ S}
    (p : Presentation l (ULift.{u} (Padic l)) f)
    (hX : IsUnit (l : Γ(X, ⊤)))
    (θ : SpTowerClasses.unit X (SpTowerClasses.Arings l (ULift.{u} (Padic l)) X) ⟶
      (SpTowerClasses.line l (ULift.{u} (Padic l)) p.chernX)⟦(2 : ℤ)⟧) :
    ∃! z : completedUnit l X ⟶ (completedLine l X)⟦(2 : ℤ)⟧,
      (diagonalCompletedUnderlying l X).map z ≫
        shiftedComparison (diagonalCompletedUnderlying l X)
          (p.restrictionX.F.mapDerivedCategory ⋙ p.LX.R)
          (p.coefficientsX.lineMap l (ULift.{u} (Padic l)) p.LX) 2 =
        p.coefficientsX.unitMap l (ULift.{u} (Padic l)) p.LX ≫
          p.LX.R.map (p.restrictionX.F.mapDerivedCategory.map θ) := by
  let F := diagonalCompletedUnderlying l X
  let P : ObjectProperty (DerivedCategory (DiagonalCompleted l X)) := fun M ↦
    ∀ V : DerivedCategory (DiagonalMod l X),
      IsIso (l • 𝟙 V) → Subsingleton (V ⟶ F.obj M)
  obtain ⟨ff⟩ := diagonalCompleteScalarRestrictionCore l X
  let U := SheafOfModules.unit (Scheme.purTwistRing X (Scheme.purTwistZlCompletion X l))
  have hunit := diagonalCompletedLine_complete l X U
    ((SheafOfModules.isInvertible_iff_isFiniteLocallyFreeOfRank_one U).mp inferInstance)
  let inst : ∀ x : X, Invertible (l : X.residueField x) := fun x ↦
    (show IsUnit (l : X.residueField x) from by
      let ψ := (X.residue x).hom.comp (X.presheaf.germ ⊤ x trivial).hom
      simpa only [map_natCast] using hX.map ψ).invertible
  have hfree : (Scheme.purTwistZlModule X l).IsFiniteLocallyFreeOfRank 1 :=
    (Scheme.pur_twist_sheaf_locally_free.{u, u} X l (ULift.{u} (Padic l))).2.1.2.1
  have hline₀ := diagonalCompletedLine_complete l X _ hfree
  let adj : shiftFunctor (DerivedCategory (DiagonalMod l X)) (-2 : ℤ) ⊣
      shiftFunctor (DerivedCategory (DiagonalMod l X)) (2 : ℤ) :=
    (shiftEquiv' _ (-2 : ℤ) (2 : ℤ) (by decide)).toAdjunction
  have hshift := complete_rightAdjoint adj l (F.obj (completedLine l X)) hline₀
  have hline : P ((completedLine l X)⟦(2 : ℤ)⟧) := by
    intro V hV
    let e := Iso.homCongr (Iso.refl V)
      ((F.commShiftIso (2 : ℤ)).app (completedLine l X))
    constructor
    intro a b
    apply e.injective
    exact @Subsingleton.elim _ (hshift V hV) (e a) (e b)
  let A : P.FullSubcategory := ⟨_, hline⟩
  let B : P.FullSubcategory := ⟨_, hunit⟩
  let k := shiftedComparison F (p.restrictionX.F.mapDerivedCategory ⋙ p.LX.R)
    (p.coefficientsX.lineMap l (ULift.{u} (Padic l)) p.LX) 2
  have := p.line_limit
  have : IsIso k := by unfold k shiftedComparison; infer_instance
  let c := p.coefficientsX.unitMap l (ULift.{u} (Padic l)) p.LX ≫
    p.LX.R.map (p.restrictionX.F.mapDerivedCategory.map θ)
  obtain ⟨z, hz⟩ := ff.map_surjective (X := B) (Y := A) (c ≫ inv k)
  change F.map z.hom = c ≫ inv k at hz
  refine ⟨z.hom, ?_, ?_⟩
  · change F.map z.hom ≫ k = c
    rw [hz, Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  · intro z' hz'
    change F.map z' ≫ k = c at hz'
    apply congrArg (fun a ↦ a.hom) (ff.map_injective (X := B) (Y := A) (f := ⟨z'⟩)
      (g := z) ?_)
    change F.map z' = F.map z.hom
    apply (cancel_mono k).mp
    rw [hz', hz, Category.assoc, IsIso.inv_hom_id, Category.comp_id]

end AlgebraicGeometry.ProEtale.DiagonalTrace
