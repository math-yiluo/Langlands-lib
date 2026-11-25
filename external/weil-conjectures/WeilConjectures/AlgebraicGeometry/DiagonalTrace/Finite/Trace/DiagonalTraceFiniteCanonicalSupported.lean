/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalTrace.Finite.Trace.DiagonalTraceFiniteEvaluation
public import WeilConjectures.AlgebraicGeometry.DiagonalTrace.Finite.Trace.DiagonalTraceFiniteCartierChern
import WeilConjectures.AlgebraicGeometry.DiagonalTrace.Finite.Trace.DiagonalTraceFiniteProjection
import WeilConjectures.AlgebraicGeometry.DiagonalTrace.Supported.DiagonalTraceSupportedUnitNormalization

/-! # The supported equation for the constructed finite operation -/

@[expose] public noncomputable section
set_option autoImplicit false
universe u a v w
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.ProEtale.DiagonalTrace

attribute [local irreducible] DerivedCategory Functor.mapDerivedCategory

private theorem rightSingle_naturality
    {A B : Type a} [Category.{v} A] [Category.{v} B] [Abelian A] [Abelian B]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w} B]
    (F : A ⥤ B) [F.Additive] (R : DiagonalRightDerived F)
    {M N : A} (v : M ⟶ N) :
    (DerivedCategory.singleFunctor B 0).map (F.map v) ≫
        diagonalTraceRightSingle F R N =
      diagonalTraceRightSingle F R M ≫ R.R.map
        ((DerivedCategory.singleFunctor A 0).map v) := by
  have he (M : A) : diagonalTraceRightSingle F R M =
      DerivedCategory.Q.map
        ((HomologicalComplex.singleMapHomologicalComplex F (.up ℤ) 0).inv.app M) ≫
        R.η.app ((HomologicalComplex.single A (.up ℤ) 0).obj M) := by
    simp only [diagonalTraceRightSingle, DerivedCategory.singleFunctorIsoCompQ,
      Iso.refl_hom, Iso.refl_inv, NatTrans.id_app, Category.id_comp]
    erw [R.R.map_id, Category.comp_id]
  rw [he, he]
  erw [← DerivedCategory.Q.map_comp_assoc]
  erw [(HomologicalComplex.singleMapHomologicalComplex F (.up ℤ) 0).inv.naturality v]
  erw [DerivedCategory.Q.map_comp, Category.assoc]
  have hn := R.η.naturality ((HomologicalComplex.single A (.up ℤ) 0).map v)
  dsimp only [Functor.comp_obj, Functor.comp_map] at hn
  erw [hn]
  rw [Category.assoc]
  rfl

private theorem supported_seed
    (l : ℕ) [Fact l.Prime] (Y : Scheme.{u})
    [DiagonalTraceLocalizations l (ProjectiveLine Y)]
    [DiagonalTraceLocalizations l (diagonalSurface Y)]
    (f : diagonalSurface Y ⟶ ProjectiveLine Y)
    (p : Presentation l (ULift.{u} (Padic l)) f)
    (a : SupportedSource l Y f p.Rc) :
    (diagonalCompletedUnderlying l (ProjectiveLine Y)).map a.hom ≫
        p.completed.iso.hom.app (diagonalCompletedDomain l Y) =
      p.finitePushUnit l ≫ p.Rf.R.map
        ((diagonalCompletedUnderlying l (diagonalSurface Y)).map
          ((DerivedCategory.singleFunctor (DiagonalCompleted l (diagonalSurface Y)) 0).map
            (completedSupportedUnit l Y))) := by
  let S := DerivedCategory.singleFunctor (DiagonalCompleted l (ProjectiveLine Y)) 0
  let T := DerivedCategory.singleFunctor (DiagonalCompleted l (diagonalSurface Y)) 0
  let b := S.map (completedPushUnit l f) ≫
    diagonalTraceRightSingle (diagonalTracePush l f) p.Rc _
  let t := T.map (completedSupportedUnit l Y)
  have ha : a.hom = b ≫ p.Rc.R.map t := by
    dsimp only [NormalizedSource.hom, b, t, S, T]
    rw [diagonalTrace_supportedUnit_normalization l Y f p a, CategoryTheory.Functor.map_comp,
      Category.assoc, rightSingle_naturality, ← Category.assoc]
  rw [ha, CategoryTheory.Functor.map_comp, Category.assoc]
  have hn := p.completed.iso.hom.naturality t
  dsimp only [Functor.comp_map] at hn
  rw [hn, ← Category.assoc]
  rfl

private theorem source_projection
    (l : ℕ) [Fact l.Prime] {X S : Scheme.{u}}
    [DiagonalTraceLocalizations l X] [DiagonalTraceLocalizations l S]
    {f : X ⟶ S} (p : Presentation l (ULift.{u} (Padic l)) f) (n : ℕ) :
    p.sourceMap l (ULift.{u} (Padic l)) ≫ (p.LS.projection n).app _ ≫
        ((evaluation ℕᵒᵖ (DiagonalMod l S)).obj (op n)).mapDerivedCategory.map
          (p.varying.inv.app _) =
      p.completed.iso.hom.app _ ≫ p.Rf.R.map
        (shiftedComparison (diagonalCompletedUnderlying l X)
          (p.restrictionX.F.mapDerivedCategory ⋙ p.LX.R)
          (p.coefficientsX.lineMap l (ULift.{u} (Padic l)) p.LX) 2 ≫
          (p.LX.projection n).app _) ≫
        (p.finitePushComparison l n).hom.app _ := by
  simp only [Presentation.sourceMap, Presentation.finitePushComparison,
    Iso.trans_hom, Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Iso.symm_hom,
    Category.id_comp, Category.comp_id, CategoryTheory.Functor.map_comp, Category.assoc]
  rw [← diagonalTrace_finiteEvaluation_projection l p _ n]
  erw [Category.id_comp]
  simp only [Category.assoc]
  erw [Iso.hom_inv_id_app_assoc]

/-- The explicit finite direct-image operation has the supported equation.
Source: diagonal tower trace proof (2), naturality of completed direct image and
of the unit-normalized limit projection.
(blueprint: lem-sfb-diagonal-trace-finite-canonical-supported).
Proof: use the ordinary supported-source unit identity, naturality of the
underived-to-derived unit, naturality of the completed square, and projection
coherence. Functoriality then combines the supported arrow with its source map. -/
theorem diagonalTrace_finiteCanonical_supported
    (l : ℕ) [Fact l.Prime] (Y : Scheme.{u})
    [DiagonalTraceLocalizations l (ProjectiveLine Y)]
    [DiagonalTraceLocalizations l (diagonalSurface Y)]
    (f : diagonalSurface Y ⟶ ProjectiveLine Y)
    (p : Presentation l (ULift.{u} (Padic l)) f)
    (a : SupportedSource l Y f p.Rc) (n : ℕ)
    (γ : diagonalCompletedDomain l Y ⟶ diagonalCompletedCodomain l Y) :
    let E := ULift.{u} (Padic l)
    let UX := diagonalCompletedUnderlying l (diagonalSurface Y)
    let US := diagonalCompletedUnderlying l (ProjectiveLine Y)
    let VX := p.restrictionX.F.mapDerivedCategory
    let evS := ((evaluation ℕᵒᵖ (DiagonalMod l (ProjectiveLine Y))).obj
      (op n)).mapDerivedCategory
    p.finitePushUnit l ≫ p.Rf.R.map
        (UX.map
            ((DerivedCategory.singleFunctor (DiagonalCompleted l (diagonalSurface Y)) 0).map
              (completedSupportedUnit l Y) ≫ γ) ≫
          shiftedComparison UX (VX ⋙ p.LX.R) (p.coefficientsX.lineMap l E p.LX) 2 ≫
            (p.LX.projection n).app _) ≫ (p.finitePushComparison l n).hom.app _ =
      US.map (a.hom ≫ p.Rc.R.map γ) ≫ p.sourceMap l E ≫
        (p.LS.projection n).app _ ≫ evS.map (p.varying.inv.app _) := by
  dsimp only
  rw [source_projection]
  simp only [CategoryTheory.Functor.map_comp, Category.assoc]
  have hn := p.completed.iso.hom.naturality γ
  dsimp only [Functor.comp_map] at hn
  rw [reassoc_of% hn]
  rw [reassoc_of% supported_seed l Y f p a]

end AlgebraicGeometry.ProEtale.DiagonalTrace
