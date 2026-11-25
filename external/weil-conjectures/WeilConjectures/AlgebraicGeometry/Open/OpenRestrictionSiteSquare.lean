/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Etale.Compact.EtaleCompactSupportCoefficientChange
import WeilConjectures.CategoryTheory.Adjunction.SquareCompatibleMate
import all WeilConjectures.AlgebraicGeometry.Comparison.ComparisonOpenTensorCoherence
import all WeilConjectures.AlgebraicGeometry.Etale.ProEtale.EtaleProEtaleScalarPullbackCube

/-! # Restriction and the exact open-extension site boundary

## References

* Stacks 03DI, 09AF and 099R
-/

-- After pruning, this module only keeps private declarations.
set_option linter.privateModule false

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

private theorem mate_whisker_top
    {C D E F : Type*} [Category C] [Category D] [Category E] [Category F]
    {G G' : C ⥤ E} {H : D ⥤ F}
    {L₁ : C ⥤ D} {R₁ : D ⥤ C} {L₂ : E ⥤ F} {R₂ : F ⥤ E}
    (a₁ : L₁ ⊣ R₁) (a₂ : L₂ ⊣ R₂) (w : TwoSquare G' L₁ L₂ H) (t : G ⟶ G') :
    mateEquiv a₁ a₂ (w.whiskerTop t) = (mateEquiv a₁ a₂ w).whiskerRight t := by
  simpa [TwoSquare.whiskerBottom, TwoSquare.whiskerLeft] using
    mateEquiv_whiskerTop_whiskerBottom a₁ a₂ w t (𝟙 H)

private theorem inverse_mate_cube
    {CA DA CB DB EA FA EB FB : Type*}
    [Category CA] [Category DA] [Category CB] [Category DB]
    [Category EA] [Category FA] [Category EB] [Category FB]
    {LA : CA ⥤ DA} {RA : DA ⥤ CA} {LB : CB ⥤ DB} {RB : DB ⥤ CB}
    {LA' : EA ⥤ FA} {RA' : FA ⥤ EA} {LB' : EB ⥤ FB} {RB' : FB ⥤ EB}
    (aA : LA ⊣ RA) (aB : LB ⊣ RB) (bA : LA' ⊣ RA') (bB : LB' ⊣ RB')
    {U : CB ⥤ CA} {V : DB ⥤ DA} {U' : EB ⥤ EA} {V' : FB ⥤ FA}
    {GA : CA ⥤ EA} {HA : DA ⥤ FA} {GB : CB ⥤ EB} {HB : DB ⥤ FB}
    (aa : TwoSquare GA LA LA' HA) (ab : TwoSquare GB LB LB' HB)
    (k : TwoSquare U LB LA V) (i : TwoSquare U' LB' LA' V')
    (t : U ⋙ GA ⟶ GB ⋙ U') (s : V ⋙ HA ⟶ HB ⋙ V')
    (h : ∀ M : DB,
      t.app (RB.obj M) ≫ U'.map ((mateEquiv aB bB ab).app M) ≫
          (mateEquiv bB bA i).app (HB.obj M) =
        GA.map ((mateEquiv aB aA k).app M) ≫
          (mateEquiv aA bA aa).app (V.obj M) ≫ RA'.map (s.app M))
    (N : CB) :
    LA'.map (t.app N) ≫ i.app (GB.obj N) ≫ V'.map (ab.app N) =
      aa.app (U.obj N) ≫ HA.map (k.app N) ≫ s.app (LB.obj N) := by
  have hc : (ab.hComp i).whiskerTop t = (k.hComp aa).whiskerBottom s := by
    apply (mateEquiv aB bA).injective
    rw [mate_whisker_top, mateEquiv_whiskerBottom,
      mateEquiv_vcomp aB bB bA, mateEquiv_vcomp aB aA bA]
    ext M
    simpa only [TwoSquare.vComp, TwoSquare.whiskerRight, TwoSquare.whiskerLeft,
      NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
      Functor.associator_hom_app, Functor.associator_inv_app,
      Category.id_comp, Category.comp_id, Category.assoc] using h M
  simpa only [TwoSquare.hComp, TwoSquare.whiskerTop, TwoSquare.whiskerBottom,
    NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app,
    Category.id_comp, Category.comp_id, Category.assoc] using
    congrArg (fun w ↦ w.app N) hc

private theorem square_symm
    {C D E V : Type*} [Category C] [Category D] [Category E] [Category V]
    [Abelian C] [Abelian D] [Abelian E] [Abelian V]
    [HasDerivedCategory C] [HasDerivedCategory D]
    [HasDerivedCategory E] [HasDerivedCategory V]
    {F : C ⥤ D} {G : D ⥤ V} {H : C ⥤ E} {J : E ⥤ V}
    [F.Additive] [G.Additive] [H.Additive] [J.Additive]
    [Limits.PreservesFiniteLimits F] [Limits.PreservesFiniteColimits F]
    [Limits.PreservesFiniteLimits G] [Limits.PreservesFiniteColimits G]
    [Limits.PreservesFiniteLimits H] [Limits.PreservesFiniteColimits H]
    [Limits.PreservesFiniteLimits J] [Limits.PreservesFiniteColimits J]
    (e : F ⋙ G ≅ H ⋙ J) :
    Functor.mapDerivedCategorySquareIso e.symm =
      (Functor.mapDerivedCategorySquareIso e).symm := by
  ext M
  simp only [Functor.mapDerivedCategorySquareIso, Iso.trans_hom, Iso.trans_inv,
    Iso.symm_hom, Iso.symm_inv, Functor.mapDerivedCategoryNatIso_symm,
    NatTrans.comp_app, Category.assoc]

end AlgebraicGeometry.ProEtale
