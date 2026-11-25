/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.AlgebraicGeometry.ExactUnboundedExchange
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar
public import WeilConjectures.SixFunctors.BaseChange.Square
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import WeilConjectures.AlgebraicGeometry.Unbounded.UnboundedProperOpenInterchangeSupplement
public import WeilConjectures.AlgebraicGeometry.Finite.Coefficient.FiniteCoefficientDirectImage
public import WeilConjectures.AlgebraicGeometry.Etale.Open.EtaleOpenTensor
public import WeilConjectures.AlgebraicGeometry.ProEtale.Extension.ProEtaleExtensionZeroComparison
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.AB
public import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Comp
public import Mathlib.CategoryTheory.Adjunction.CompositionIso
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.CoherenceLegacy
public import WeilConjectures.AlgebraicGeometry.ProEtale.Proper.ProEtaleProperOpenComparison
public import WeilConjectures.AlgebraicGeometry.FixedComparisonDirectImageMate
public import WeilConjectures.AlgebraicGeometry.ProEtale.Finite.ProEtaleFiniteModulesSupplement
public import WeilConjectures.Algebra.Homology.CanonicalTensorPullbackOfUniverses.RingedTopoiCanonicalTensorPullbackOfUniverses
import WeilConjectures.AlgebraicGeometry.Compact.CompactSupportSiteComparisonOpen

import WeilConjectures.CategoryTheory.Derived.DerivedExactCube
import WeilConjectures.AlgebraicGeometry.Etale.ProEtale.EtaleProEtaleScalarMate

/-! # Coefficient and site naturality of proper/open interchange

## References

* Stacks Project, Tags 0F7B and 0GL6
* Stacks Project, Tag 0F7B (exact extension and K-injective direct image)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale

set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
/- Transport and pasting calculations for the canonical scalar-adjunction mates. -/
private theorem inverse_mate_transport
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    {L : A ⥤ B} {U : B ⥤ A} {M : C ⥤ D} {V : D ⥤ C}
    (a : L ⊣ U) (b : M ⊣ V)
    {G G' : A ⥤ C} {H H' : B ⥤ D}
    (x : TwoSquare U H G V) (e : G ≅ G') (f : H ≅ H') :
    ((mateEquiv a b).symm
      (TwoSquare.mk U H' G' V
        (Functor.whiskerLeft U e.inv ≫ x ≫ Functor.whiskerRight f.hom V))) =
      Functor.whiskerRight e.inv M ≫ ((mateEquiv a b).symm x) ≫
        Functor.whiskerLeft L f.hom := by
  ext z
  simp only [mateEquiv_symm_apply, NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.whiskerLeft_app, Functor.associator_hom_app, Functor.associator_inv_app,
    Functor.leftUnitor_inv_app, Functor.rightUnitor_hom_app,
    CategoryTheory.Functor.map_id, Category.id_comp, Functor.map_comp,
    Category.assoc]
  dsimp only [Functor.comp_obj, Functor.comp_map]
  simp only [Category.id_comp]
  have he := e.inv.naturality (a.unit.app z)
  dsimp only [Functor.comp_obj, Functor.id_obj] at he
  rw [← M.map_comp_assoc, he, M.map_comp]
  simp only [Category.assoc]
  have hf := b.counit.naturality (f.hom.app (L.obj z))
  dsimp only [Functor.comp_map, Functor.id_map] at hf
  erw [Category.comp_id]
  erw [Category.id_comp]
  rw [hf]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem mateCube
    {C₀ C₁ C₂ C₃ D₀ D₁ D₂ D₃ : Type*}
    [Category C₀] [Category C₁] [Category C₂] [Category C₃]
    [Category D₀] [Category D₁] [Category D₂] [Category D₃]
    {S₀ : C₀ ⥤ D₀} {R₀ : D₀ ⥤ C₀} {S₁ : C₁ ⥤ D₁} {R₁ : D₁ ⥤ C₁}
    {S₂ : C₂ ⥤ D₂} {R₂ : D₂ ⥤ C₂} {S₃ : C₃ ⥤ D₃} {R₃ : D₃ ⥤ C₃}
    (a₀ : S₀ ⊣ R₀) (a₁ : S₁ ⊣ R₁) (a₂ : S₂ ⊣ R₂) (a₃ : S₃ ⊣ R₃)
    {J : C₀ ⥤ C₁} {H : C₁ ⥤ C₃} {G : C₀ ⥤ C₂} {I : C₂ ⥤ C₃}
    {J' : D₀ ⥤ D₁} {H' : D₁ ⥤ D₃} {G' : D₀ ⥤ D₂} {I' : D₂ ⥤ D₃}
    (qJ : R₀ ⋙ J ⟶ J' ⋙ R₁) (qH : R₁ ⋙ H ⟶ H' ⋙ R₃)
    (qG : R₀ ⋙ G ⟶ G' ⋙ R₂) (qI : R₂ ⋙ I ⟶ I' ⋙ R₃)
    (c : J ⋙ H ⟶ G ⋙ I) (d : J' ⋙ H' ⟶ G' ⋙ I')
    (hc : ∀ M, c.app (R₀.obj M) ≫ I.map (qG.app M) ≫ qI.app (G'.obj M) =
      H.map (qJ.app M) ≫ qH.app (J'.obj M) ≫ R₃.map (d.app M))
    (N : C₀) :
    S₃.map (c.app N) ≫
        ((mateEquiv a₂ a₃).symm (TwoSquare.mk _ _ _ _ qI)).app (G.obj N) ≫
        I'.map (((mateEquiv a₀ a₂).symm (TwoSquare.mk _ _ _ _ qG)).app N) =
      ((mateEquiv a₁ a₃).symm (TwoSquare.mk _ _ _ _ qH)).app (J.obj N) ≫
        H'.map (((mateEquiv a₀ a₁).symm (TwoSquare.mk _ _ _ _ qJ)).app N) ≫
        d.app (S₀.obj N) := by
  let lJ := ((mateEquiv a₀ a₁).symm (TwoSquare.mk _ _ _ _ qJ))
  let lH := ((mateEquiv a₁ a₃).symm (TwoSquare.mk _ _ _ _ qH))
  let lG := ((mateEquiv a₀ a₂).symm (TwoSquare.mk _ _ _ _ qG))
  let lI := ((mateEquiv a₂ a₃).symm (TwoSquare.mk _ _ _ _ qI))
  have hj (K : C₀) : J.map (a₀.unit.app K) ≫ qJ.app (S₀.obj K) =
      a₁.unit.app (J.obj K) ≫ R₁.map (lJ.app K) :=
    unit_mateEquiv_symm a₀ a₁ (TwoSquare.mk _ _ _ _ qJ) K
  have hh (K : C₁) : H.map (a₁.unit.app K) ≫ qH.app (S₁.obj K) =
      a₃.unit.app (H.obj K) ≫ R₃.map (lH.app K) :=
    unit_mateEquiv_symm a₁ a₃ (TwoSquare.mk _ _ _ _ qH) K
  have hg (K : C₀) : G.map (a₀.unit.app K) ≫ qG.app (S₀.obj K) =
      a₂.unit.app (G.obj K) ≫ R₂.map (lG.app K) :=
    unit_mateEquiv_symm a₀ a₂ (TwoSquare.mk _ _ _ _ qG) K
  have hi (K : C₂) : I.map (a₂.unit.app K) ≫ qI.app (S₂.obj K) =
      a₃.unit.app (I.obj K) ≫ R₃.map (lI.app K) :=
    unit_mateEquiv_symm a₂ a₃ (TwoSquare.mk _ _ _ _ qI) K
  change S₃.map (c.app N) ≫ lI.app (G.obj N) ≫ I'.map (lG.app N) =
    lH.app (J.obj N) ≫ H'.map (lJ.app N) ≫ d.app (S₀.obj N)
  apply (a₃.homEquiv _ _).injective
  simp only [Adjunction.homEquiv_unit, Functor.map_comp, Functor.comp_obj]
  have hn := a₃.unit.naturality (c.app N)
  dsimp only [Functor.id_map, Functor.comp_map, Functor.comp_obj] at hn
  rw [← reassoc_of% hn, ← reassoc_of% (hi (G.obj N))]
  have hq := qI.naturality (lG.app N)
  dsimp only [Functor.comp_map, Functor.comp_obj] at hq
  rw [← hq, ← I.map_comp_assoc, ← hg, I.map_comp]
  have hcn := c.naturality (a₀.unit.app N)
  dsimp only [Functor.comp_map, Functor.comp_obj] at hcn
  simp only [Category.assoc, Functor.id_obj] at hcn ⊢
  rw [← reassoc_of% hcn, hc]
  rw [← reassoc_of% (hh (J.obj N))]
  have hqn := qH.naturality (lJ.app N)
  dsimp only [Functor.comp_map, Functor.comp_obj] at hqn
  rw [← reassoc_of% hqn, ← H.map_comp_assoc, hj]
  simp only [Functor.map_comp, Category.assoc]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem scalar_exchange_of_cube
    {C D E F C' D' E' F' : Type*}
    [Category C] [Category D] [Category E] [Category F]
    [Category C'] [Category D'] [Category E'] [Category F']
    {a : C ⥤ D} {ar : D ⥤ C} {b : C' ⥤ D'} {br : D' ⥤ C'}
    {c : E ⥤ F} {cr : F ⥤ E} {d : E' ⥤ F'} {dr : F' ⥤ E'}
    (aa : a ⊣ ar) (ab : b ⊣ br) (ac : c ⊣ cr) (ad : d ⊣ dr)
    (s : C ⥤ C') (t : D ⥤ D') (v : E ⥤ E') (w : F ⥤ F')
    (g : C ⥤ E) (h : D ⥤ F) (g' : C' ⥤ E') (h' : D' ⥤ F')
    (la : s ⋙ b ⟶ a ⋙ t) (lc : v ⋙ d ⟶ c ⋙ w)
    (lg : s ⋙ g' ⟶ g ⋙ v) (lh : t ⋙ h' ⟶ h ⋙ w)
    (ta : g ⋙ c ⟶ a ⋙ h) (tb : g' ⋙ d ⟶ b ⋙ h')
    (cube : ∀ N : C,
      tb.app (s.obj N) ≫ h'.map (la.app N) ≫ lh.app (a.obj N) =
        d.map (lg.app N) ≫ lc.app (g.obj N) ≫ w.map (ta.app N))
    (M : D) :
    g'.map ((mateEquiv aa ab la).app M) ≫
        (mateEquiv ab ad tb).app (t.obj M) ≫ dr.map (lh.app M) =
      lg.app (ar.obj M) ≫ v.map ((mateEquiv aa ac ta).app M) ≫
        (mateEquiv ac ad lc).app (h.obj M) := by
  apply (ad.homEquiv _ _).symm.injective
  simp only [Adjunction.homEquiv_counit, Functor.map_comp, Category.assoc]
  rw [show d.map (dr.map (lh.app M)) ≫ ad.counit.app _ =
    ad.counit.app _ ≫ lh.app M from ad.counit.naturality _]
  slice_lhs 2 3 => rw [mateEquiv_counit]
  slice_lhs 1 2 =>
    exact tb.naturality ((mateEquiv aa ab la).app M)
  simp only [Functor.comp_map, Category.assoc]
  slice_lhs 2 3 =>
    rw [← h'.map_comp, mateEquiv_counit, h'.map_comp]
  slice_lhs 3 4 => exact lh.naturality (aa.counit.app M)
  slice_lhs 1 3 => exact cube (ar.obj M)
  slice_rhs 3 4 => exact mateEquiv_counit ac ad (TwoSquare.mk _ _ _ _ lc) (h.obj M)
  slice_rhs 2 3 => exact lc.naturality ((mateEquiv aa ac ta).app M)
  simp only [Functor.comp_map, Category.assoc]
  slice_rhs 3 4 => rw [← w.map_comp, mateEquiv_counit, w.map_comp]
  rfl

/- Recover the open-extension square from its restriction/exchange square. This
calculation is independent of sheaves and boundedness. -/
private theorem coefficient_interchange_of_restriction
    {CA DA EA FA CB DB EB FB : Type*}
    [Category CA] [Category DA] [Category EA] [Category FA]
    [Category CB] [Category DB] [Category EB] [Category FB]
    {JkA : CA ⥤ DA} {PkA : DA ⥤ CA} {JiA : EA ⥤ FA} {PiA : FA ⥤ EA}
    {JkB : CB ⥤ DB} {PkB : DB ⥤ CB} {JiB : EB ⥤ FB} {PiB : FB ⥤ EB}
    (akA : JkA ⊣ PkA) (aiA : JiA ⊣ PiA)
    (akB : JkB ⊣ PkB) (aiB : JiB ⊣ PiB)
    (RrA : CA ⥤ EA) (RpA : DA ⥤ FA) (RrB : CB ⥤ EB) (RpB : DB ⥤ FB)
    (SU : CA ⥤ CB) (SV : DA ⥤ DB) (SW : EA ⥤ EB) (SZ : FA ⥤ FB)
    (rk : PkA ⋙ SU ⟶ SV ⋙ PkB) (ri : PiA ⋙ SW ⟶ SZ ⋙ PiB)
    (cr : RrA ⋙ SW ⟶ SU ⋙ RrB) (cp : RpA ⋙ SZ ⟶ SV ⋙ RpB)
    (qk : JkA ⋙ SV ≅ SU ⋙ JkB) (qi : JiA ⋙ SZ ≅ SW ⋙ JiB)
    (exA : RpA ⋙ PiA ⟶ PkA ⋙ RrA) (exB : RpB ⋙ PiB ⟶ PkB ⋙ RrB)
    (hex : ∀ M, ri.app (RpA.obj M) ≫ PiB.map (cp.app M) ≫ exB.app (SV.obj M) =
      SW.map (exA.app M) ≫ cr.app (PkA.obj M) ≫ RrB.map (rk.app M))
    (hqi : ∀ M, aiB.unit.app (SW.obj M) ≫ PiB.map (qi.inv.app M) =
      SW.map (aiA.unit.app M) ≫ ri.app (JiA.obj M))
    (hqk : ∀ M, akB.unit.app (SU.obj M) ≫ PkB.map (qk.inv.app M) =
      SU.map (akA.unit.app M) ≫ rk.app (JkA.obj M))
    (E : CA) (aA : JiA.obj (RrA.obj E) ⟶ RpA.obj (JkA.obj E))
    (aB : JiB.obj (RrB.obj (SU.obj E)) ⟶ RpB.obj (JkB.obj (SU.obj E)))
    (hA : (aiA.homEquiv _ _ aA) ≫ exA.app (JkA.obj E) = RrA.map (akA.unit.app E))
    (hB : (aiB.homEquiv _ _ aB) ≫ exB.app (JkB.obj (SU.obj E)) =
      RrB.map (akB.unit.app (SU.obj E)))
    [Mono (exB.app (JkB.obj (SU.obj E)))] :
    SZ.map aA ≫ cp.app (JkA.obj E) ≫ RpB.map (qk.hom.app E) =
      qi.hom.app (RrA.obj E) ≫ JiB.map (cr.app E) ≫ aB := by
  apply (cancel_epi (qi.inv.app (RrA.obj E))).mp
  apply (aiB.homEquiv _ _).injective
  apply (cancel_mono (exB.app (JkB.obj (SU.obj E)))).mp
  simp only [← Category.assoc, Iso.inv_hom_id_app, Category.id_comp]
  rw [aiB.homEquiv_naturality_left]
  simp only [Category.assoc]
  slice_rhs 2 3 => exact hB
  simp only [Adjunction.homEquiv_unit, Functor.map_comp, Category.assoc]
  slice_lhs 1 2 => exact hqi (RrA.obj E)
  slice_lhs 2 3 => exact (ri.naturality aA).symm
  slice_lhs 5 6 => exact (exB.naturality (qk.hom.app E))
  slice_lhs 3 5 => exact hex (JkA.obj E)
  slice_lhs 1 3 => exact (by
    simpa only [Adjunction.homEquiv_unit, Functor.map_comp, Functor.comp_map,
      Category.assoc] using congrArg SW.map hA)
  slice_lhs 1 2 => exact cr.naturality (akA.unit.app E)
  slice_lhs 2 3 => exact (RrB.map_comp _ _).symm
  have hk : SU.map (akA.unit.app E) ≫ rk.app (JkA.obj E) ≫ PkB.map (qk.hom.app E) =
      akB.unit.app (SU.obj E) := by
    rw [← Category.assoc, ← hqk, Category.assoc, ← PkB.map_comp, Iso.inv_hom_id_app]
    erw [CategoryTheory.Functor.map_id, Category.comp_id]
  dsimp only [Functor.comp_map, Functor.id_obj]
  rw [← RrB.map_comp]
  simp only [Category.assoc, hk]

private theorem cachedEtaleGroth (A : Type (u + 1)) [CommRing A]
    (X : AlgebraicGeometry.Scheme.{u}) :
    IsGrothendieckAbelian.{u + 1} (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) :=
  inferInstance
private theorem cachedEtaleSheafify (A : Type (u + 1)) [CommRing A]
    (X : AlgebraicGeometry.Scheme.{u}) : HasSheafify X.smallEtaleTopology (ModuleCat.{u + 1} A) :=
  inferInstance

attribute [local instance] cachedEtaleGroth cachedEtaleSheafify
attribute [local irreducible] upperStar
attribute [local instance 2000] Abelian.toPreadditive
private lemma conjugate_unique {C D : Type*} [Category* C] [Category* D]
    {F F' : C ⥤ D} {G : D ⥤ C} (a : F ⊣ G) (b : F' ⊣ G) :
    conjugateEquiv b a (a.leftAdjointUniq b).hom = 𝟙 G := by
  simp [Adjunction.leftAdjointUniq]

private lemma conjugate_assoc_inv {A B C D : Type*}
    [Category* A] [Category* B] [Category* C] [Category* D]
    {L₁ : A ⥤ B} {R₁ : B ⥤ A} {L₂ : B ⥤ C} {R₂ : C ⥤ B}
    {L₃ : C ⥤ D} {R₃ : D ⥤ C}
    (a : L₁ ⊣ R₁) (b : L₂ ⊣ R₂) (c : L₃ ⊣ R₃) :
    conjugateEquiv ((a.comp b).comp c) (a.comp (b.comp c))
      (Functor.associator L₁ L₂ L₃).inv = (Functor.associator R₃ R₂ R₁).inv := by
  apply (cancel_epi (Functor.associator R₃ R₂ R₁).hom).mp
  rw [← conjugateEquiv_associator_hom a b c, conjugateEquiv_comp]
  simp only [Iso.inv_hom_id]
  rw [conjugateEquiv_associator_hom]
  simp

private lemma coefficient_comp
    {Λ Λ' : Type (u + 1)} [CommRing Λ] [CommRing Λ'] (φ : Λ →+* Λ')
    {X S Y : Scheme.{u}} (h : Y ⟶ X) (p : X ⟶ S) (d : Y ⟶ S)
    (hd : d = h ≫ p) :
    Functor.isoWhiskerLeft (Sheaf.restrictScalars S.smallEtaleTopology φ)
        (upperStarComp (ModuleCat.{u + 1} Λ) h p d hd) ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (upperStarRestrictScalarsIsoSheaf φ p) (h)^*[ModuleCat.{u + 1} Λ] ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft (p)^*[ModuleCat.{u + 1} Λ'] (upperStarRestrictScalarsIsoSheaf φ h) ≪≫
      (Functor.associator _ _ _).symm =
    upperStarRestrictScalarsIsoSheaf φ d ≪≫
      Functor.isoWhiskerRight (upperStarComp (ModuleCat.{u + 1} Λ') h p d hd)
        (Sheaf.restrictScalars Y.smallEtaleTopology φ) := by
  have := (ModuleCat.restrictCoextendScalarsAdj.{u + 1, u + 1, u + 1} φ).isRightAdjoint
  let aS := Sheaf.restrictCoextendScalarsAdj S.smallEtaleTopology φ
  let aX := Sheaf.restrictCoextendScalarsAdj X.smallEtaleTopology φ
  let aY := Sheaf.restrictCoextendScalarsAdj Y.smallEtaleTopology φ
  let b := upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) p
  let c := upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) h
  let f := upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) d
  let b' := upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ') p
  let c' := upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ') h
  let f' := upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ') d
  apply Iso.ext
  apply (conjugateEquiv ((b'.comp c').comp aY) (aS.comp f)).injective
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom]
  rw [← conjugateEquiv_comp _ (aS.comp (b.comp c)),
    ← conjugateEquiv_comp _ ((aS.comp b).comp c),
    ← conjugateEquiv_comp _ ((b'.comp aX).comp c),
    ← conjugateEquiv_comp _ (b'.comp (aX.comp c)),
    ← conjugateEquiv_comp _ (b'.comp (c'.comp aY)),
    ← conjugateEquiv_comp _ (f'.comp aY)]
  rw [conjugate_assoc_inv, conjugateEquiv_whiskerLeft, conjugateEquiv_associator_hom,
    conjugateEquiv_whiskerRight, conjugate_assoc_inv, conjugateEquiv_whiskerLeft,
    conjugateEquiv_whiskerRight]
  have hp := conjugate_unique (aS.comp b) (b'.comp aX)
  have hh := conjugate_unique (aX.comp c) (c'.comp aY)
  have hd' := conjugate_unique (aS.comp f) (f'.comp aY)
  simp only [aS, aX, aY, b, c, f, b', c', f', upperStarRestrictScalarsIsoSheaf] at hp hh hd' ⊢
  erw [hp, hh, hd']
  simp only [upperStarComp, Iso.symm_hom, conjugateIsoEquiv_symm_apply_inv,
    Iso.symm_inv, Equiv.apply_symm_apply]
  apply NatTrans.ext
  funext F
  dsimp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.associator_inv_app, Functor.associator_hom_app, NatTrans.id_app]
  erw [CategoryTheory.Functor.map_id]
  rfl

private lemma coefficient_comp_app
    {Λ Λ' : Type (u + 1)} [CommRing Λ] [CommRing Λ'] (φ : Λ →+* Λ')
    {X S Y : Scheme.{u}} (h : Y ⟶ X) (p : X ⟶ S) (d : Y ⟶ S)
    (hd : d = h ≫ p) (L : Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} Λ')) :
    (upperStarComp (ModuleCat.{u + 1} Λ) h p d hd).hom.app
        ((Sheaf.restrictScalars S.smallEtaleTopology φ).obj L) ≫
      (h)^*[ModuleCat.{u + 1} Λ].map ((upperStarRestrictScalarsIsoSheaf φ p).hom.app L) ≫
      (upperStarRestrictScalarsIsoSheaf φ h).hom.app ((p)^*[ModuleCat.{u + 1} Λ'].obj L) =
    (upperStarRestrictScalarsIsoSheaf φ d).hom.app L ≫
      (Sheaf.restrictScalars Y.smallEtaleTopology φ).map
        ((upperStarComp (ModuleCat.{u + 1} Λ') h p d hd).hom.app L) := by
  have key := congr_app (congrArg Iso.hom (coefficient_comp φ h p d hd)) L
  simpa using key

private lemma coefficient_square
    {Λ Λ' : Type (u + 1)} [CommRing Λ] [CommRing Λ'] (φ : Λ →+* Λ')
    {X S T Y : Scheme.{u}} {p : X ⟶ S} {g : T ⟶ S} {e : Y ⟶ T} {h : Y ⟶ X}
    (sq : CommSq e h g p) (L : Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} Λ')) :
    (h)^*[ModuleCat.{u + 1} Λ].map ((upperStarRestrictScalarsIsoSheaf φ p).hom.app L) ≫
      (upperStarRestrictScalarsIsoSheaf φ h).hom.app ((p)^*[ModuleCat.{u + 1} Λ'].obj L) ≫
      (Sheaf.restrictScalars Y.smallEtaleTopology φ).map
        ((squareUpperStarIso (ModuleCat.{u + 1} Λ') sq).hom.app L) =
    (squareUpperStarIso (ModuleCat.{u + 1} Λ) sq).hom.app
        ((Sheaf.restrictScalars S.smallEtaleTopology φ).obj L) ≫
      (e)^*[ModuleCat.{u + 1} Λ].map ((upperStarRestrictScalarsIsoSheaf φ g).hom.app L) ≫
      (upperStarRestrictScalarsIsoSheaf φ e).hom.app ((g)^*[ModuleCat.{u + 1} Λ'].obj L) := by
  rw [← cancel_epi ((upperStarComp (ModuleCat.{u + 1} Λ) h p (e ≫ g) sq.w).hom.app
    ((Sheaf.restrictScalars S.smallEtaleTopology φ).obj L))]
  simp only [squareUpperStarIso, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    CategoryTheory.Functor.map_comp, Category.assoc, Iso.hom_inv_id_app_assoc]
  rw [reassoc_of% (coefficient_comp_app φ h p (e ≫ g) sq.w L),
    ← CategoryTheory.Functor.map_comp_assoc, Iso.hom_inv_id_app]
  erw [CategoryTheory.Functor.map_id, Category.id_comp]
  exact (coefficient_comp_app φ e g (e ≫ g) rfl L).symm

variable {R S : Type (u + 1)} [CommRing R] [CommRing S]
private theorem exact_scalar_mate_etale (q : R →+* S) {X Y : Scheme.{u}} (f : X ⟶ Y) :
    IsIso ((mateEquiv
      (Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars Y.smallEtaleTopology q))
      (Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars X.smallEtaleTopology q))).symm
      (TwoSquare.mk _ _ _ _
        (Functor.mapDerivedCategorySquareIso
          (upperStarRestrictScalarsIsoSheaf q f)).hom)) := by
  let a := Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars Y.smallEtaleTopology q)
  let b := Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars X.smallEtaleTopology q)
  let x := TwoSquare.mk _ _ _ _ (scalarRestrictionPullbackIso q f).hom
  let e := leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} R) f
  let e' := leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} S) f
  have hx : IsIso ((mateEquiv a b).symm x) := (ProEtale.scalarPullbackReverse_isIso q f).2
  have h := inverse_mate_transport a b x e e'
  have ht : IsIso (Functor.whiskerRight e.inv _ ≫
      ((mateEquiv a b).symm x) ≫ Functor.whiskerLeft _ e'.hom) := inferInstance
  rw [← h] at ht
  have heq : TwoSquare.mk _ _ _ _
      (Functor.mapDerivedCategorySquareIso (upperStarRestrictScalarsIsoSheaf q f)).hom =
      TwoSquare.mk _ _ _ _
        (Functor.whiskerLeft (Sheaf.derivedRestrictScalars Y.smallEtaleTopology q)
          e.inv ≫ x ≫
          Functor.whiskerRight e'.hom
            (Sheaf.derivedRestrictScalars X.smallEtaleTopology q)) := by
    ext M
    dsimp only [x, e, e', scalarRestrictionPullbackIso, NatTrans.comp_app,
      Functor.whiskerLeft_app, Functor.whiskerRight_app, Iso.trans_hom,
      Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom, Iso.symm_hom]
    simp only [Category.assoc, Iso.inv_hom_id_app_assoc,
      ← CategoryTheory.Functor.map_comp, Iso.inv_hom_id_app,
      CategoryTheory.Functor.map_id]
    erw [Category.comp_id]
  rw [← heq] at ht
  exact ht

private theorem exact_geometric_adjunction
    (A : Type (u + 1)) [CommRing A] {X Y : Scheme.{u}} (f : X ⟶ Y) :
    mapDerivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f =
      (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f).ofNatIsoLeft
        (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) f) := by
  apply Adjunction.ext
  apply Localization.natTrans_ext DerivedCategory.Qh
    (HomotopyCategory.quasiIso _ (.up ℤ))
  intro K
  apply (cancel_mono
    (R((f)_*[ModuleCat.{u + 1} A]).map
      (((f)^*[ModuleCat.{u + 1} A]).mapDerivedCategoryFactorsh.hom.app K))).mp
  have h₁ := (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f).mapHomotopyCategory
    (.up ℤ) |>.derivedη_fac_app (HomotopyCategory.quasiIso _ (.up ℤ))
      ((f)^*[ModuleCat.{u + 1} A]).mapDerivedCategoryFactorsh.hom
      ((f)_*[ModuleCat.{u + 1} A]).rightDerivedFunctorUnit K
  have h₂ := (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f).mapHomotopyCategory
    (.up ℤ) |>.derivedη_fac_app (HomotopyCategory.quasiIso _ (.up ℤ))
      ((f)^*[ModuleCat.{u + 1} A]).leftDerivedFunctorCounit
      ((f)_*[ModuleCat.{u + 1} A]).rightDerivedFunctorUnit K
  have h₃ := NatTrans.congr_app
    ((f)^*[ModuleCat.{u + 1} A]).leftDerivedFunctorIsoMapDerivedCategory_hom_fac K
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app] at h₃
  simp only [Adjunction.ofNatIsoLeft_unit, NatTrans.comp_app, Functor.whiskerRight_app,
    Category.assoc, ← CategoryTheory.Functor.map_comp]
  dsimp only [leftDerivedUpperStarIsoMapDerivedCategory]
  rw [h₃]
  exact h₁.trans h₂.symm

/- Localization preserves the entire coefficient cube, rather than just its edges. -/
private theorem exact_coefficient_square
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B)
    {U V W Z : Scheme.{u}} {k : U ⟶ V} {r : U ⟶ W} {p : V ⟶ Z} {i : W ⟶ Z}
    (sq : CommSq k r p i) (M : DerivedCategoryModule B Z) :
    (exactDerivedSquareUpperStarIso (ModuleCat.{u + 1} A) sq).hom.app
        ((Sheaf.derivedRestrictScalars Z.smallEtaleTopology φ).obj M) ≫
      D((k)^*[ModuleCat.{u + 1} A]).map
        ((Functor.mapDerivedCategorySquareIso (upperStarRestrictScalarsIsoSheaf φ p)).hom.app M) ≫
      (Functor.mapDerivedCategorySquareIso (upperStarRestrictScalarsIsoSheaf φ k)).hom.app
        (D((p)^*[ModuleCat.{u + 1} B]).obj M) =
    D((r)^*[ModuleCat.{u + 1} A]).map
        ((Functor.mapDerivedCategorySquareIso (upperStarRestrictScalarsIsoSheaf φ i)).hom.app M) ≫
      (Functor.mapDerivedCategorySquareIso (upperStarRestrictScalarsIsoSheaf φ r)).hom.app
        (D((i)^*[ModuleCat.{u + 1} B]).obj M) ≫
      (Sheaf.derivedRestrictScalars U.smallEtaleTopology φ).map
        ((exactDerivedSquareUpperStarIso (ModuleCat.{u + 1} B) sq).hom.app M) := by
  have h := Functor.mapDerivedCategory_exactCube
    (Sheaf.restrictScalars Z.smallEtaleTopology φ) (i)^*[ModuleCat.{u + 1} A]
    (r)^*[ModuleCat.{u + 1} A] (i)^*[ModuleCat.{u + 1} B]
    (Sheaf.restrictScalars W.smallEtaleTopology φ) (r)^*[ModuleCat.{u + 1} B]
    (Sheaf.restrictScalars U.smallEtaleTopology φ) (p)^*[ModuleCat.{u + 1} B]
    (k)^*[ModuleCat.{u + 1} B] (p)^*[ModuleCat.{u + 1} A]
    (k)^*[ModuleCat.{u + 1} A] (Sheaf.restrictScalars V.smallEtaleTopology φ)
    (upperStarRestrictScalarsIsoSheaf φ i) (upperStarRestrictScalarsIsoSheaf φ r)
    (squareUpperStarIso (ModuleCat.{u + 1} B) sq)
    (squareUpperStarIso (ModuleCat.{u + 1} A) sq)
    (upperStarRestrictScalarsIsoSheaf φ p) (upperStarRestrictScalarsIsoSheaf φ k)
    (coefficient_square φ sq)
  exact (congr_app h M).symm

private theorem coefficient_of_mate
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    {P : A ⥤ B} {Q : B ⥤ A} (adjA : Q ⊣ P)
    {P' : C ⥤ D} {Q' : D ⥤ C} (adjB : Q' ⊣ P')
    {S : B ⥤ D} {R : D ⥤ B} (adjX : S ⊣ R)
    {S' : A ⥤ C} {R' : C ⥤ A} (adjT : S' ⊣ R')
    (e : R ⋙ Q ≅ Q' ⋙ R')
    [IsIso (((mateEquiv adjX adjT).symm (TwoSquare.mk _ _ _ _ e.hom)))]
    (M : A) :
    let k := ((mateEquiv adjX adjT).symm (TwoSquare.mk _ _ _ _ e.hom))
    let γ := (mateEquiv adjA adjB (TwoSquare.mk _ _ _ _ (asIso k).inv))
    Q.map (adjX.unit.app (P.obj M)) ≫ e.hom.app (S.obj (P.obj M)) ≫
      R'.map (Q'.map (γ.app M) ≫ adjB.counit.app (S'.obj M)) =
        adjA.counit.app M ≫ adjT.unit.app M := by
  dsimp only
  let k := ((mateEquiv adjX adjT).symm (TwoSquare.mk _ _ _ _ e.hom))
  let γ := (mateEquiv adjA adjB (TwoSquare.mk _ _ _ _ (asIso k).inv))
  have hunit := unit_mateEquiv_symm adjX adjT (TwoSquare.mk _ _ _ _ e.hom) (P.obj M)
  change Q.map (adjX.unit.app (P.obj M)) ≫ e.hom.app (S.obj (P.obj M)) =
    adjT.unit.app (Q.obj (P.obj M)) ≫ R'.map (k.app (P.obj M)) at hunit
  have hc := mateEquiv_counit adjA adjB (TwoSquare.mk _ _ _ _ (asIso k).inv) M
  change Q'.map (γ.app M) ≫ adjB.counit.app (S'.obj M) =
    (asIso k).inv.app (P.obj M) ≫ S'.map (adjA.counit.app M) at hc
  rw [show Q'.map (γ.app M) ≫ adjB.counit.app (S'.obj M) = _ from hc,
    ← Category.assoc, hunit, Category.assoc, ← R'.map_comp]
  change adjT.unit.app _ ≫ R'.map ((asIso k).hom.app _ ≫ (asIso k).inv.app _ ≫ _) = _
  rw [Iso.hom_inv_id_app_assoc]
  exact (adjT.unit.naturality (adjA.counit.app M)).symm

private theorem mate_transport_left
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    {L L' : A ⥤ B} {R : B ⥤ A} {M M' : C ⥤ D} {V : D ⥤ C}
    (a : L ⊣ R) (b : M ⊣ V) (e : L ≅ L') (f : M ≅ M')
    {S : A ⥤ C} {T : B ⥤ D} (x : S ⋙ M ⟶ L ⋙ T) :
    (mateEquiv (a.ofNatIsoLeft e) (b.ofNatIsoLeft f)
      (TwoSquare.mk _ _ _ _
        (Functor.whiskerLeft S f.inv ≫ x ≫ Functor.whiskerRight e.hom T))) =
      (mateEquiv a b (TwoSquare.mk _ _ _ _ x)) := by
  ext K
  simp only [mateEquiv_apply, Adjunction.ofNatIsoLeft_unit,
    Adjunction.ofNatIsoLeft_counit, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Functor.associator_hom_app, Functor.associator_inv_app,
    CategoryTheory.Functor.map_comp, Category.id_comp,
    Category.assoc]
  dsimp only [Functor.comp_obj, Functor.comp_map]
  simp only [← CategoryTheory.Functor.map_comp_assoc,
    Iso.hom_inv_id_app_assoc, Iso.hom_inv_id_app,
    CategoryTheory.Functor.map_id, Category.id_comp]

private abbrev exactScalarReverse
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B)
    {T X : Scheme.{u}} (f : T ⟶ X) :=
  ((mateEquiv
    (Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars X.smallEtaleTopology φ))
    (Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars T.smallEtaleTopology φ))).symm
      (TwoSquare.mk _ _ _ _
        (Functor.mapDerivedCategorySquareIso (upperStarRestrictScalarsIsoSheaf φ f)).hom))

private instance exactScalarReverse_isIso
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B)
    {T X : Scheme.{u}} (f : T ⟶ X) : IsIso (exactScalarReverse φ f) :=
  exact_scalar_mate_etale φ f

private def exactCoefficientMap
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B)
    {T X : Scheme.{u}} (f : T ⟶ X) :=
  (mateEquiv (mapDerivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f)
    (mapDerivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} B) f)
    (TwoSquare.mk _ _ _ _ (asIso (exactScalarReverse φ f)).inv))

/- Identify the universal scalar-unit definition with the geometric mate; transport
along the canonical exact/left-derived pullback comparison. -/
private theorem exactCoefficientMap_app
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B)
    {T X : Scheme.{u}} (f : T ⟶ X) (K : DerivedCategoryModule A T) :
    (exactCoefficientMap φ f).app K = finiteCoefficientDirectImageMap φ f K := by
  let a := Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars X.smallEtaleTopology φ)
  let b := Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars T.smallEtaleTopology φ)
  let x := TwoSquare.mk _ _ _ _ (scalarRestrictionPullbackIso φ f).hom
  let e := leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) f
  let e' := leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} B) f
  let l := ((mateEquiv a b).symm x)
  have : IsIso l := (ProEtale.scalarPullbackReverse_isIso φ f).2
  let γ := (mateEquiv (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f)
    (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} B) f)
    (TwoSquare.mk _ _ _ _ (asIso l).inv))
  have hγ : γ.app K = finiteCoefficientDirectImageMap φ f K := by
    apply (finiteCoefficientDirectImageMap_existsUnique φ f K).choose_spec.2
    exact coefficient_of_mate
      (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f)
      (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} B) f)
      a b (scalarRestrictionPullbackIso φ f) K
  have ht := inverse_mate_transport a b x e e'
  have heq : TwoSquare.mk _ _ _ _
      (Functor.mapDerivedCategorySquareIso (upperStarRestrictScalarsIsoSheaf φ f)).hom =
      TwoSquare.mk _ _ _ _
        (Functor.whiskerLeft (Sheaf.derivedRestrictScalars X.smallEtaleTopology φ)
          e.inv ≫ x ≫
          Functor.whiskerRight e'.hom
            (Sheaf.derivedRestrictScalars T.smallEtaleTopology φ)) := by
    ext M
    dsimp only [x, e, e', scalarRestrictionPullbackIso, NatTrans.comp_app,
      Functor.whiskerLeft_app, Functor.whiskerRight_app, Iso.trans_hom,
      Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom, Iso.symm_hom]
    simp only [Category.assoc, Iso.inv_hom_id_app_assoc,
      ← CategoryTheory.Functor.map_comp, Iso.inv_hom_id_app,
      CategoryTheory.Functor.map_id]
    erw [Category.comp_id]
  rw [← heq] at ht
  have hi : asIso (exactScalarReverse φ f) =
      Functor.isoWhiskerRight e.symm _ ≪≫ asIso l ≪≫ Functor.isoWhiskerLeft _ e' :=
    Iso.ext ht
  have hm := mate_transport_left
    (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f)
    (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} B) f) e e'
    (S := scalarExtension φ X) (T := scalarExtension φ T) (asIso l).inv
  dsimp only [exactCoefficientMap]
  rw [exact_geometric_adjunction, exact_geometric_adjunction, hi]
  simpa only [Iso.trans_inv, Functor.isoWhiskerLeft_inv, Functor.isoWhiskerRight_inv,
    Iso.symm_inv, Category.assoc, scalarExtension,
    ProEtale.pbcFixedScalarExtension, e, e'] using (congr_app hm K).trans hγ

private theorem exactScalarReverse_cube
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B)
    {U V W Z : Scheme.{u}} {k : U ⟶ V} {r : U ⟶ W} {p : V ⟶ Z} {i : W ⟶ Z}
    (sq : CommSq k r p i) (M : DerivedCategoryModule A Z) :
    (scalarExtension φ U).map
        ((exactDerivedSquareUpperStarIso (ModuleCat.{u + 1} A) sq).hom.app M) ≫
      (exactScalarReverse φ k).app (D((p)^*[ModuleCat.{u + 1} A]).obj M) ≫
      D((k)^*[ModuleCat.{u + 1} B]).map ((exactScalarReverse φ p).app M) =
    (exactScalarReverse φ r).app (D((i)^*[ModuleCat.{u + 1} A]).obj M) ≫
      D((r)^*[ModuleCat.{u + 1} B]).map ((exactScalarReverse φ i).app M) ≫
      (exactDerivedSquareUpperStarIso (ModuleCat.{u + 1} B) sq).hom.app
        ((scalarExtension φ Z).obj M) := by
  exact mateCube
    (Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars Z.smallEtaleTopology φ))
    (Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars W.smallEtaleTopology φ))
    (Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars V.smallEtaleTopology φ))
    (Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars U.smallEtaleTopology φ))
    (Functor.mapDerivedCategorySquareIso (upperStarRestrictScalarsIsoSheaf φ i)).hom
    (Functor.mapDerivedCategorySquareIso (upperStarRestrictScalarsIsoSheaf φ r)).hom
    (Functor.mapDerivedCategorySquareIso (upperStarRestrictScalarsIsoSheaf φ p)).hom
    (Functor.mapDerivedCategorySquareIso (upperStarRestrictScalarsIsoSheaf φ k)).hom
    (exactDerivedSquareUpperStarIso (ModuleCat.{u + 1} A) sq).hom
    (exactDerivedSquareUpperStarIso (ModuleCat.{u + 1} B) sq).hom
    (exact_coefficient_square φ sq) M

private theorem exactCoefficient_exchange
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B)
    {U V W Z : Scheme.{u}} {k : U ⟶ V} {r : U ⟶ W} {p : V ⟶ Z} {i : W ⟶ Z}
    (sq : CommSq k r p i) (M : DerivedCategoryModule A V) :
    (exactScalarReverse φ i).app (R((p)_*[ModuleCat.{u + 1} A]).obj M) ≫
        D((i)^*[ModuleCat.{u + 1} B]).map ((exactCoefficientMap φ p).app M) ≫
        (exactDerivedBaseChangeMap (ModuleCat.{u + 1} B) sq).app
          ((scalarExtension φ V).obj M) =
      (scalarExtension φ W).map
          ((exactDerivedBaseChangeMap (ModuleCat.{u + 1} A) sq).app M) ≫
        (exactCoefficientMap φ r).app (D((k)^*[ModuleCat.{u + 1} A]).obj M) ≫
        R((r)_*[ModuleCat.{u + 1} B]).map ((exactScalarReverse φ k).app M) := by
  have hc (N : DerivedCategoryModule A Z) :
      (exactDerivedSquareUpperStarIso (ModuleCat.{u + 1} B) sq).hom.app
          ((scalarExtension φ Z).obj N) ≫
        D((k)^*[ModuleCat.{u + 1} B]).map ((asIso (exactScalarReverse φ p)).inv.app N) ≫
        (asIso (exactScalarReverse φ k)).inv.app (D((p)^*[ModuleCat.{u + 1} A]).obj N) =
      D((r)^*[ModuleCat.{u + 1} B]).map ((asIso (exactScalarReverse φ i)).inv.app N) ≫
        (asIso (exactScalarReverse φ r)).inv.app (D((i)^*[ModuleCat.{u + 1} A]).obj N) ≫
        (scalarExtension φ U).map
          ((exactDerivedSquareUpperStarIso (ModuleCat.{u + 1} A) sq).hom.app N) := by
    have h := congrArg (fun f ↦
      D((r)^*[ModuleCat.{u + 1} B]).map ((asIso (exactScalarReverse φ i)).inv.app N) ≫
      (asIso (exactScalarReverse φ r)).inv.app (D((i)^*[ModuleCat.{u + 1} A]).obj N) ≫
      f ≫
      D((k)^*[ModuleCat.{u + 1} B]).map ((asIso (exactScalarReverse φ p)).inv.app N) ≫
      (asIso (exactScalarReverse φ k)).inv.app (D((p)^*[ModuleCat.{u + 1} A]).obj N))
      (exactScalarReverse_cube φ sq N)
    simpa only [Category.assoc, ← CategoryTheory.Functor.map_comp_assoc,
      ← CategoryTheory.Functor.map_comp, Iso.hom_inv_id_app_assoc, Iso.inv_hom_id_app_assoc,
      Iso.hom_inv_id_app, Iso.inv_hom_id_app, CategoryTheory.Functor.map_id,
      IsIso.hom_inv_id_assoc, IsIso.inv_hom_id_assoc, IsIso.hom_inv_id, IsIso.inv_hom_id,
      asIso_inv, NatIso.isIso_inv_app,
      Category.id_comp, Category.comp_id, asIso_hom] using h.symm
  have h := scalar_exchange_of_cube
    (mapDerivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) p)
    (mapDerivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} B) p)
    (mapDerivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) r)
    (mapDerivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} B) r)
    (scalarExtension φ Z) (scalarExtension φ V) (scalarExtension φ W) (scalarExtension φ U)
    D((i)^*[ModuleCat.{u + 1} A]) D((k)^*[ModuleCat.{u + 1} A])
    D((i)^*[ModuleCat.{u + 1} B]) D((k)^*[ModuleCat.{u + 1} B])
    (asIso (exactScalarReverse φ p)).inv (asIso (exactScalarReverse φ r)).inv
    (asIso (exactScalarReverse φ i)).inv (asIso (exactScalarReverse φ k)).inv
    (exactDerivedSquareUpperStarIso (ModuleCat.{u + 1} A) sq).hom
    (exactDerivedSquareUpperStarIso (ModuleCat.{u + 1} B) sq).hom hc M
  have h' := congrArg (fun f ↦
    (exactScalarReverse φ i).app (R((p)_*[ModuleCat.{u + 1} A]).obj M) ≫ f ≫
      R((r)_*[ModuleCat.{u + 1} B]).map ((exactScalarReverse φ k).app M)) h
  dsimp only [exactCoefficientMap, exactDerivedBaseChangeMap]
  simp only [Category.assoc, ← CategoryTheory.Functor.map_comp,
    IsIso.inv_hom_id, IsIso.hom_inv_id_assoc, asIso_inv,
    NatIso.isIso_inv_app, CategoryTheory.Functor.map_id]
    at h'
  erw [Category.comp_id] at h'
  exact h'

private theorem coextend_unit_hom
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B)
    (X : Scheme.{u}) (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B)) :
    ((Sheaf.restrictCoextendScalarsAdj X.smallEtaleTopology φ).unit.app F).hom =
      ((ModuleCat.restrictCoextendScalarsAdj.{u + 1, u + 1,
    u + 1} φ).whiskerRight X.Etaleᵒᵖ).unit.app F.obj := by
  change (sheafToPresheaf X.smallEtaleTopology (ModuleCat.{u + 1} B)).map
    ((Sheaf.restrictCoextendScalarsAdj X.smallEtaleTopology φ).unit.app F) = _
  rw [Sheaf.restrictCoextendScalarsAdj, Adjunction.map_restrictFullyFaithful_unit_app]
  simp only [Iso.refl_hom, NatTrans.id_app]
  erw [CategoryTheory.Functor.map_id, Category.comp_id]
  rfl

private theorem localization_unit_hom_app
    (A : Type (u + 1)) [CommRing A] {U X : Scheme.{u}}
    (j : U ⟶ X) [IsOpenImmersion j]
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) (T : X.Etaleᵒᵖ) :
    ((localizationRestrictionLowerStarAdjunction (ModuleCat.{u + 1} A) j
      inferInstance).unit.app F).hom.app T =
      F.obj.map ((MorphismProperty.Over.mapPullbackAdj @Etale ⊤ j
        (inferInstance : Etale j) _root_.trivial).op.unit.app T) := by
  rfl

private theorem open_adj_coefficient
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B)
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    (Sheaf.restrictCoextendScalarsAdj X.smallEtaleTopology φ).comp
      (localizationRestrictionLowerStarAdjunction (ModuleCat.{u + 1} A) j inferInstance) =
    (localizationRestrictionLowerStarAdjunction (ModuleCat.{u + 1} B) j inferInstance).comp
      (Sheaf.restrictCoextendScalarsAdj U.smallEtaleTopology φ) := by
  apply Adjunction.ext
  apply NatTrans.ext
  funext F
  apply (fullyFaithfulSheafToPresheaf X.smallEtaleTopology (ModuleCat.{u + 1} B)).map_injective
  simp only [Adjunction.comp_unit_app]
  apply NatTrans.ext
  funext T
  obtain ⟨T⟩ := T
  change ((Sheaf.restrictCoextendScalarsAdj X.smallEtaleTopology φ).unit.app F).hom.app
      (Opposite.op T) ≫
      (ModuleCat.coextendScalars φ).map
        (((localizationRestrictionLowerStarAdjunction (ModuleCat.{u + 1} A) j
          inferInstance).unit.app
            ((Sheaf.restrictScalars X.smallEtaleTopology φ).obj F)).hom.app (Opposite.op T)) =
    ((localizationRestrictionLowerStarAdjunction (ModuleCat.{u + 1} B) j
      inferInstance).unit.app F).hom.app (Opposite.op T) ≫
      ((Sheaf.restrictCoextendScalarsAdj U.smallEtaleTopology φ).unit.app
        ((localizationRestriction (ModuleCat.{u + 1} B) j inferInstance).obj F)).hom.app _
  rw [coextend_unit_hom, coextend_unit_hom,
    Adjunction.whiskerRight_unit_app_app, Adjunction.whiskerRight_unit_app_app,
    localization_unit_hom_app, localization_unit_hom_app]
  exact ((ModuleCat.restrictCoextendScalarsAdj.{u + 1, u + 1, u + 1} φ).unit.naturality
    (F.obj.map ((MorphismProperty.Over.mapPullbackAdj @Etale ⊤ j
      (inferInstance : Etale j) _root_.trivial).op.unit.app (Opposite.op T)))).symm
private theorem unique_whisker_left
    {C D E : Type*} [Category C] [Category D] [Category E]
    {F : C ⥤ D} {G : D ⥤ C} (a : F ⊣ G)
    {L L' : D ⥤ E} {R : E ⥤ D} (b : L ⊣ R) (c : L' ⊣ R) :
    (a.comp b).leftAdjointUniq (a.comp c) =
      Functor.isoWhiskerLeft F (b.leftAdjointUniq c) := by
  apply Iso.ext
  apply (conjugateEquiv (a.comp c) (a.comp b)).injective
  simp only [Functor.isoWhiskerLeft_hom, conjugateEquiv_whiskerLeft]
  simp [Adjunction.leftAdjointUniq]

private theorem unique_whisker_right
    {C D E : Type*} [Category C] [Category D] [Category E]
    {F F' : C ⥤ D} {G : D ⥤ C} (a : F ⊣ G) (b : F' ⊣ G)
    {L : D ⥤ E} {R : E ⥤ D} (c : L ⊣ R) :
    (a.comp c).leftAdjointUniq (b.comp c) =
      Functor.isoWhiskerRight (a.leftAdjointUniq b) L := by
  apply Iso.ext
  apply (conjugateEquiv (b.comp c) (a.comp c)).injective
  simp only [Functor.isoWhiskerRight_hom, conjugateEquiv_whiskerRight]
  simp [Adjunction.leftAdjointUniq]

/- The open-specific restriction comparison is the general canonical comparison:
sectionwise naturality identifies the composite coextension adjunctions. -/
private theorem openRestrictScalarsIso_eq
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B)
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    openRestrictScalarsIso φ j = (upperStarRestrictScalarsIsoSheaf φ j).symm := by
  let a := Sheaf.restrictCoextendScalarsAdj X.smallEtaleTopology φ
  let b := Sheaf.restrictCoextendScalarsAdj U.smallEtaleTopology φ
  let c := upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) j
  let d := upperStarLowerStarAdjunction (ModuleCat.{u + 1} B) j
  let e := localizationRestrictionLowerStarAdjunction (ModuleCat.{u + 1} A) j inferInstance
  let f := localizationRestrictionLowerStarAdjunction (ModuleCat.{u + 1} B) j inferInstance
  have hf : a.comp e = f.comp b := open_adj_coefficient φ j
  have hl := unique_whisker_left a e c
  have hr := unique_whisker_right d f b
  apply Iso.ext
  change Functor.whiskerRight (d.leftAdjointUniq f).hom
      (Sheaf.restrictScalars U.smallEtaleTopology φ) ≫ 𝟙 _ ≫
      Functor.whiskerLeft (Sheaf.restrictScalars X.smallEtaleTopology φ)
        (e.leftAdjointUniq c).hom =
    ((d.comp b).leftAdjointUniq (a.comp c)).hom
  rw [Category.id_comp, ← Functor.isoWhiskerRight_hom, ← hr,
    ← Functor.isoWhiskerLeft_hom, ← hl, hf]
  exact Adjunction.leftAdjointUniq_trans _ _ _

private theorem openScalarRestrictionMap_eq
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B)
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    openScalarRestrictionMap φ j = exactScalarReverse φ j := by
  dsimp only [openScalarRestrictionMap, openDerivedRestrictScalarsIso, exactScalarReverse]
  rw [openRestrictScalarsIso_eq]
  congr 3
  simp only [Functor.mapDerivedCategorySquareIso, Iso.trans_hom, Iso.trans_inv,
    Iso.symm_hom, Iso.symm_inv, Category.assoc]
  rw [← Functor.mapDerivedCategoryNatIso_symm]
  rfl
set_option backward.defeqAttrib.useBackward true in
private theorem scalarOpenTranspose
    {C D E F : Type*} [Category C] [Category D] [Category E] [Category F]
    {LA : C ⥤ D} {JA : D ⥤ C} {LB : E ⥤ F} {JB : F ⥤ E}
    {SX : D ⥤ F} {RX : F ⥤ D} {SU : C ⥤ E} {RU : E ⥤ C}
    (a : LA ⊣ JA) (b : LB ⊣ JB) (x : SX ⊣ RX) (u : SU ⊣ RU)
    (q : JB ⋙ RU ≅ RX ⋙ JA) (K : C) :
    b.unit.app (SU.obj K) ≫ JB.map
        (((a.comp x).leftAdjointUniq ((u.comp b).ofNatIsoRight q)).inv.app K) =
      SU.map (a.unit.app K) ≫
        ((mateEquiv x u).symm (TwoSquare.mk _ _ _ _ q.inv)).app (LA.obj K) := by
  apply (u.homEquiv _ _).injective
  simp only [Adjunction.homEquiv_unit, Functor.map_comp]
  have h := Adjunction.unit_leftAdjointUniq_hom_app
    ((u.comp b).ofNatIsoRight q) (a.comp x) K
  change ((u.comp b).ofNatIsoRight q).unit.app K ≫
      (RX ⋙ JA).map
        (((a.comp x).leftAdjointUniq ((u.comp b).ofNatIsoRight q)).inv.app K) =
      (a.comp x).unit.app K at h
  simp only [Adjunction.ofNatIsoRight_unit, NatTrans.comp_app,
    Functor.whiskerLeft_app, Adjunction.comp_unit_app, Functor.comp_map,
    Category.assoc] at h
  have hn := q.hom.naturality
    (((a.comp x).leftAdjointUniq ((u.comp b).ofNatIsoRight q)).inv.app K)
  dsimp only [Functor.comp_map, Functor.comp_obj] at hn
  dsimp only [Functor.comp_obj] at h
  rw [← hn] at h
  have hm := unit_mateEquiv_symm x u (TwoSquare.mk _ _ _ _ q.inv) (LA.obj K)
  change JA.map (x.unit.app (LA.obj K)) ≫ q.inv.app (SX.obj (LA.obj K)) =
    u.unit.app (JA.obj (LA.obj K)) ≫ RU.map
      (((mateEquiv x u).symm (TwoSquare.mk _ _ _ _ q.inv)).app (LA.obj K)) at hm
  have hu := u.unit.naturality (a.unit.app K)
  dsimp only [Functor.id_map, Functor.comp_map, Functor.comp_obj] at hu
  rw [← reassoc_of% hu, ← hm]
  apply (cancel_mono (q.hom.app (SX.obj (LA.obj K)))).1
  simpa only [Category.assoc, Iso.inv_hom_id_app, Category.comp_id, Functor.comp_obj,
    Adjunction.comp_unit_app] using h

private theorem openScalarExtension_unit
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B)
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (K : DerivedCategoryModule A U) :
    (derivedOpenImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} B) j).unit.app
        ((scalarExtension φ U).obj K) ≫
      D((j)^*[ModuleCat.{u + 1} B]).map ((openScalarExtension φ j).inv.app K) =
    (scalarExtension φ U).map
      ((derivedOpenImmersionLowerShriekUpperStarAdjunction
        (ModuleCat.{u + 1} A) j).unit.app K) ≫
        (exactScalarReverse φ j).app (D((j)_!open[ModuleCat.{u + 1} A]).obj K) := by
  rw [← openScalarRestrictionMap_eq]
  exact scalarOpenTranspose
    (derivedOpenImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) j)
    (derivedOpenImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} B) j)
    (Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars X.smallEtaleTopology φ))
    (Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars U.smallEtaleTopology φ))
    (openDerivedRestrictScalarsIso φ j) K
variable {U V W Z : Scheme.{u}}
  [IsNoetherian U] [IsNoetherian V] [IsNoetherian W] [IsNoetherian Z]
  {k : U ⟶ V} {r : U ⟶ W} {p : V ⟶ Z} {i : W ⟶ Z}
  [IsOpenImmersion k] [IsOpenImmersion i] [IsProper r] [IsProper p]

/-- Existence with the exchange normalization that determines the proper/open isomorphism. -/
theorem properOpenCoefficientInterchange_normalized_exists
    (A : Type (u + 1)) [CommRing A] [Finite A] (sq : IsPullback k r p i) :
    ∃ γ :
    R((r)_*[ModuleCat.{u + 1} A]) ⋙ D((i)_!open[ModuleCat.{u + 1} A]) ≅
      D((k)_!open[ModuleCat.{u + 1} A]) ⋙ R((p)_*[ModuleCat.{u + 1} A]),
        ∃ lam : D((k)_!open[ModuleCat.{u + 1} A]) ⋙ R((p)_*[ModuleCat.{u + 1} A]) ⋙
            D((i)^*[ModuleCat.{u + 1} A]) ≅ R((r)_*[ModuleCat.{u + 1} A]),
          (∀ K : DerivedCategoryModule A U,
            lam.hom.app K =
              (exactDerivedBaseChangeMap (ModuleCat.{u + 1} A) sq.toCommSq).app
                  (D((k)_!open[ModuleCat.{u + 1} A]).obj K) ≫
                R((r)_*[ModuleCat.{u + 1} A]).map
                  (inv ((derivedOpenImmersionLowerShriekUpperStarAdjunction
                    (ModuleCat.{u + 1} A) k).unit.app K))) ∧
          ∀ K : DerivedCategoryModule A U,
            γ.hom.app K =
              D((i)_!open[ModuleCat.{u + 1} A]).map (lam.inv.app K) ≫
                (derivedOpenImmersionLowerShriekUpperStarAdjunction
                  (ModuleCat.{u + 1} A) i).counit.app
                    (R((p)_*[ModuleCat.{u + 1} A]).obj
                      (D((k)_!open[ModuleCat.{u + 1} A]).obj K)) := by
  exact ⟨(unboundedProperOpenInterchange A).choose_spec.choose k r p i sq.toCommSq,
    (unboundedProperOpenInterchange A).choose_spec.choose_spec.2.2.1 k r p i sq⟩

/-- The proper/open isomorphism from the recorded theorem, whose representative and
open adjunct determine it uniquely. -/
def properOpenCoefficientInterchange (A : Type (u + 1)) [CommRing A] [Finite A]
    (sq : IsPullback k r p i) :
    R((r)_*[ModuleCat.{u + 1} A]) ⋙ D((i)_!open[ModuleCat.{u + 1} A]) ≅
      D((k)_!open[ModuleCat.{u + 1} A]) ⋙ R((p)_*[ModuleCat.{u + 1} A]) :=
  (properOpenCoefficientInterchange_normalized_exists A sq).choose

private theorem properOpenCoefficientInterchange_normalization
    (A : Type (u + 1)) [CommRing A] [Finite A] (sq : IsPullback k r p i)
    (E : DerivedCategoryModule A U) :
    let a := derivedOpenImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) i
    let b := derivedOpenImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) k
    let ex := (exactDerivedBaseChangeMap (ModuleCat.{u + 1} A) sq.toCommSq).app
      (D((k)_!open[ModuleCat.{u + 1} A]).obj E)
    (a.homEquiv _ _ ((properOpenCoefficientInterchange A sq).hom.app E)) ≫ ex =
      R((r)_*[ModuleCat.{u + 1} A]).map (b.unit.app E) ∧ IsIso ex := by
  dsimp only
  obtain ⟨lam, hl, hg⟩ :=
    (properOpenCoefficientInterchange_normalized_exists A sq).choose_spec
  let η := (derivedOpenImmersionLowerShriekUpperStarAdjunction
    (ModuleCat.{u + 1} A) k).unit.app E
  have hx : (exactDerivedBaseChangeMap (ModuleCat.{u + 1} A) sq.toCommSq).app
      (D((k)_!open[ModuleCat.{u + 1} A]).obj E) =
      lam.hom.app E ≫ R((r)_*[ModuleCat.{u + 1} A]).map η := by
    rw [hl]
    dsimp only [η]
    simp only [Category.assoc, ← CategoryTheory.Functor.map_comp, IsIso.inv_hom_id,
      CategoryTheory.Functor.map_id]
    erw [Category.comp_id]
  have ha : (derivedOpenImmersionLowerShriekUpperStarAdjunction
      (ModuleCat.{u + 1} A) i).homEquiv _ _
        ((properOpenCoefficientInterchange A sq).hom.app E) = lam.inv.app E := by
    rw [show (properOpenCoefficientInterchange A sq).hom.app E = _ from hg E]
    exact (derivedOpenImmersionLowerShriekUpperStarAdjunction
      (ModuleCat.{u + 1} A) i).homEquiv _ _ |>.apply_symm_apply (lam.inv.app E)
  constructor
  · rw [ha, hx, Iso.inv_hom_id_app_assoc]
  · rw [hx]
    infer_instance

/-- The restriction isomorphism selected by its specified exchange and open-unit formula.
The hom component, rather than just its endpoints, is fixed by the recorded theorem. -/
def properOpenCoefficientRestriction (A : Type (u + 1)) [CommRing A] [Finite A]
    (sq : IsPullback k r p i) :
    D((k)_!open[ModuleCat.{u + 1} A]) ⋙ R((p)_*[ModuleCat.{u + 1} A]) ⋙
        D((i)^*[ModuleCat.{u + 1} A]) ≅ R((r)_*[ModuleCat.{u + 1} A]) :=
  (Functor.isoWhiskerLeft R((r)_*[ModuleCat.{u + 1} A])
      (asIso (derivedOpenImmersionLowerShriekUpperStarAdjunction
        (ModuleCat.{u + 1} A) i).unit) ≪≫
    Functor.isoWhiskerRight (properOpenCoefficientInterchange A sq)
      D((i)^*[ModuleCat.{u + 1} A])).symm

/-- Canonical inclusion comparison for the target of proper/open interchange. -/
def properOpenCoefficientTargetPlus (A : Type (u + 1)) [CommRing A]
    (E : DerivedCategory.Plus (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    ((p)_*[ModuleCat.{u + 1} A].rightDerivedFunctorPlus.obj
      ((k)_!open[ModuleCat.{u + 1} A].mapDerivedCategoryPlus.obj E)).obj ≅
      R((p)_*[ModuleCat.{u + 1} A]).obj (D((k)_!open[ModuleCat.{u + 1} A]).obj E.obj) :=
  ((p)_*[ModuleCat.{u + 1} A]).rightDerivedFunctorPlusCompatibility.app
      ((k)_!open[ModuleCat.{u + 1} A].mapDerivedCategoryPlus.obj E) ≪≫
    R((p)_*[ModuleCat.{u + 1} A]).mapIso
      (((k)_!open[ModuleCat.{u + 1} A]).mapDerivedCategoryPlusCompatibility.app E)

/-- The specified etale interchange, expressed in the full bounded-below subcategories.
Full faithfulness of the inclusion transports the actual morphism, not just its objects. -/
def properOpenCoefficientInterchangePlus (A : Type (u + 1)) [CommRing A] [Finite A]
    (sq : IsPullback k r p i)
    (E : DerivedCategory.Plus (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    (i)_!open[ModuleCat.{u + 1} A].mapDerivedCategoryPlus.obj
        ((r)_*[ModuleCat.{u + 1} A].rightDerivedFunctorPlus.obj E) ≅
      (p)_*[ModuleCat.{u + 1} A].rightDerivedFunctorPlus.obj
        ((k)_!open[ModuleCat.{u + 1} A].mapDerivedCategoryPlus.obj E) :=
  (DerivedCategory.Plus.ι (C := Sheaf Z.smallEtaleTopology
    (ModuleCat.{u + 1} A))).preimageIso
    (((i)_!open[ModuleCat.{u + 1} A]).mapDerivedCategoryPlusCompatibility.app
        ((r)_*[ModuleCat.{u + 1} A].rightDerivedFunctorPlus.obj E) ≪≫
      D((i)_!open[ModuleCat.{u + 1} A]).mapIso
        (((r)_*[ModuleCat.{u + 1} A]).rightDerivedFunctorPlusCompatibility.app E) ≪≫
      (properOpenCoefficientInterchange A sq).app E.obj ≪≫
      (properOpenCoefficientTargetPlus (p := p) (k := k) A E).symm)

private def properOpenCoefficientInterchangePlusIso
    (A : Type (u + 1)) [CommRing A] [Finite A] (sq : IsPullback k r p i) :
    (r)_*[ModuleCat.{u + 1} A].rightDerivedFunctorPlus ⋙
        (i)_!open[ModuleCat.{u + 1} A].mapDerivedCategoryPlus ≅
      (k)_!open[ModuleCat.{u + 1} A].mapDerivedCategoryPlus ⋙
        (p)_*[ModuleCat.{u + 1} A].rightDerivedFunctorPlus :=
  Functor.fullyFaithfulCancelRight DerivedCategory.Plus.ι
    (Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft (r)_*[ModuleCat.{u + 1} A].rightDerivedFunctorPlus
        ((i)_!open[ModuleCat.{u + 1} A]).mapDerivedCategoryPlusCompatibility ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight
        ((r)_*[ModuleCat.{u + 1} A]).rightDerivedFunctorPlusCompatibility
        D((i)_!open[ModuleCat.{u + 1} A]) ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft DerivedCategory.Plus.ι
        (properOpenCoefficientInterchange A sq) ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight
        ((k)_!open[ModuleCat.{u + 1} A]).mapDerivedCategoryPlusCompatibility.symm
        R((p)_*[ModuleCat.{u + 1} A]) ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft (k)_!open[ModuleCat.{u + 1} A].mapDerivedCategoryPlus
        ((p)_*[ModuleCat.{u + 1} A]).rightDerivedFunctorPlusCompatibility.symm ≪≫
      (Functor.associator _ _ _).symm)

private lemma properOpenCoefficientInterchangePlusIso_app
    (A : Type (u + 1)) [CommRing A] [Finite A] (sq : IsPullback k r p i)
    (E : DerivedCategory.Plus (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    (properOpenCoefficientInterchangePlusIso A sq).hom.app E =
      (properOpenCoefficientInterchangePlus A sq E).hom := by
  apply DerivedCategory.Plus.ι.map_injective
  simp [properOpenCoefficientInterchangePlusIso, properOpenCoefficientInterchangePlus,
    properOpenCoefficientTargetPlus, Functor.preimageIso, Category.assoc]

/-- The exact same restriction exchange in bounded-below coordinates. -/
def properOpenCoefficientRestrictionPlus (A : Type (u + 1)) [CommRing A] [Finite A]
    (sq : IsPullback k r p i)
    (E : DerivedCategory.Plus (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    (i)^*[ModuleCat.{u + 1} A].mapDerivedCategoryPlus.obj
        ((p)_*[ModuleCat.{u + 1} A].rightDerivedFunctorPlus.obj
          ((k)_!open[ModuleCat.{u + 1} A].mapDerivedCategoryPlus.obj E)) ≅
      (r)_*[ModuleCat.{u + 1} A].rightDerivedFunctorPlus.obj E :=
  (DerivedCategory.Plus.ι (C := Sheaf W.smallEtaleTopology
    (ModuleCat.{u + 1} A))).preimageIso
    (((i)^*[ModuleCat.{u + 1} A]).mapDerivedCategoryPlusCompatibility.app _ ≪≫
      D((i)^*[ModuleCat.{u + 1} A]).mapIso
        (properOpenCoefficientTargetPlus (p := p) (k := k) A E) ≪≫
      (properOpenCoefficientRestriction A sq).app E.obj ≪≫
      (((r)_*[ModuleCat.{u + 1} A]).rightDerivedFunctorPlusCompatibility.app E).symm)

private lemma properOpenCoefficientRestrictionPlus_inv
    (A : Type (u + 1)) [CommRing A] [Finite A] (sq : IsPullback k r p i)
    (E : DerivedCategory.Plus (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    (properOpenCoefficientRestrictionPlus A sq E).inv =
      (derivedOpenImmersionLowerShriekUpperStarAdjunctionPlus
        (ModuleCat.{u + 1} A) i).unit.app
          ((r)_*[ModuleCat.{u + 1} A].rightDerivedFunctorPlus.obj E) ≫
        (i)^*[ModuleCat.{u + 1} A].mapDerivedCategoryPlus.map
          (properOpenCoefficientInterchangePlus A sq E).hom := by
  apply DerivedCategory.Plus.ι.map_injective
  simp only [Functor.map_comp]
  rw [properOpenCoefficientRestrictionPlus, Functor.preimageIso_inv, Functor.map_preimage]
  rw [derivedOpenImmersionLowerShriekUpperStarAdjunctionPlus,
    Adjunction.mapDerivedCategoryPlusAdjunction,
    Adjunction.map_restrictFullyFaithful_unit_app]
  have hmap : DerivedCategory.Plus.ι.map
      ((i)^*[ModuleCat.{u + 1} A].mapDerivedCategoryPlus.map
        (properOpenCoefficientInterchangePlus A sq E).hom) =
      D((i)^*[ModuleCat.{u + 1} A]).map
        (DerivedCategory.Plus.ι.map (properOpenCoefficientInterchangePlus A sq E).hom) := rfl
  rw [hmap]
  rw [properOpenCoefficientInterchangePlus, Functor.preimageIso_hom, Functor.map_preimage]
  simp only [properOpenCoefficientRestriction, Iso.trans_hom, Iso.trans_inv,
    Iso.symm_inv, Iso.symm_hom, Iso.app_hom, Iso.app_inv, Functor.mapIso_hom,
    Functor.mapIso_inv, Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.map_comp]
  dsimp only [Functor.mapDerivedCategoryPlusCompatibility, Iso.symm_hom,
    Iso.refl_inv, Iso.refl_hom, NatTrans.id_app, Functor.comp_obj]
  erw [CategoryTheory.Functor.map_id, Category.comp_id, Category.comp_id]
  simp only [Category.comp_id, Category.assoc]
  erw [Category.id_comp]
  erw [← reassoc_of% (derivedOpenImmersionLowerShriekUpperStarAdjunction
    (ModuleCat.{u + 1} A) i).unit.naturality
      (((r)_*[ModuleCat.{u + 1} A]).rightDerivedFunctorPlusCompatibility.hom.app E)]
  rfl

/-- The coefficient-square composite through the B proper/open map.
The two scalar comparisons are the recorded summandwise maps, and the proper
coefficient arrow is the uniquely specified B-linear counit transpose. -/
def properOpenCoefficientComposite
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) (sq : IsPullback k r p i) (E : DerivedCategoryModule A U) :
    (scalarExtension φ Z).obj
        (D((i)_!open[ModuleCat.{u + 1} A]).obj (R((r)_*[ModuleCat.{u + 1} A]).obj E)) ⟶
      R((p)_*[ModuleCat.{u + 1} B]).obj
        (D((k)_!open[ModuleCat.{u + 1} B]).obj ((scalarExtension φ U).obj E)) :=
  (openScalarExtension φ i).hom.app (R((r)_*[ModuleCat.{u + 1} A]).obj E) ≫
    D((i)_!open[ModuleCat.{u + 1} B]).map (finiteCoefficientDirectImageMap φ r E) ≫
    (properOpenCoefficientInterchange B sq).hom.app ((scalarExtension φ U).obj E)

/-- The transpose identity for the coefficient square: the two composites agree after
transposing along the derived pullback/direct-image adjunction for `p`. -/
theorem properOpen_coefficient_mate_transposed
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) (sq : IsPullback k r p i) (E : DerivedCategoryModule A U)
    (_hE : ∃ n : ℤ, E.IsGE n)
    (_hEB : ∃ n : ℤ, ((scalarExtension φ U).obj E).IsGE n) :
    let adj := derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} B) p
    ((adj.homEquiv _ _).symm)
      ((scalarExtension φ Z).map ((properOpenCoefficientInterchange A sq).hom.app E) ≫
        finiteCoefficientDirectImageMap φ p
          (D((k)_!open[ModuleCat.{u + 1} A]).obj E) ≫
        R((p)_*[ModuleCat.{u + 1} B]).map
          ((openScalarExtension φ k).hom.app E)) =
    ((adj.homEquiv _ _).symm)
      (properOpenCoefficientComposite φ sq E) := by
  dsimp only
  apply congrArg ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} B) p).homEquiv
    _ _).symm
  let := (properOpenCoefficientInterchange_normalization B sq
    ((scalarExtension φ U).obj E)).2
  have h := coefficient_interchange_of_restriction
    (derivedOpenImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) k)
    (derivedOpenImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) i)
    (derivedOpenImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} B) k)
    (derivedOpenImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} B) i)
    R((r)_*[ModuleCat.{u + 1} A]) R((p)_*[ModuleCat.{u + 1} A])
    R((r)_*[ModuleCat.{u + 1} B]) R((p)_*[ModuleCat.{u + 1} B])
    (scalarExtension φ U) (scalarExtension φ V) (scalarExtension φ W) (scalarExtension φ Z)
    (exactScalarReverse φ k) (exactScalarReverse φ i)
    (exactCoefficientMap φ r) (exactCoefficientMap φ p)
    (openScalarExtension φ k) (openScalarExtension φ i)
    (exactDerivedBaseChangeMap (ModuleCat.{u + 1} A) sq.toCommSq)
    (exactDerivedBaseChangeMap (ModuleCat.{u + 1} B) sq.toCommSq)
    (exactCoefficient_exchange φ sq.toCommSq)
    (openScalarExtension_unit φ i) (openScalarExtension_unit φ k) E
    ((properOpenCoefficientInterchange A sq).hom.app E)
    ((properOpenCoefficientInterchange B sq).hom.app ((scalarExtension φ U).obj E))
    (properOpenCoefficientInterchange_normalization A sq E).1
    (properOpenCoefficientInterchange_normalization B sq ((scalarExtension φ U).obj E)).1
  simpa only [exactCoefficientMap_app, properOpenCoefficientComposite] using h

/-- The coefficient square, as equality of actual B-linear arrows in the unbounded
category. -/
theorem properOpen_coefficient_mate
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) (sq : IsPullback k r p i) (E : DerivedCategoryModule A U)
    (_hE : ∃ n : ℤ, E.IsGE n)
    (_hEB : ∃ n : ℤ, ((scalarExtension φ U).obj E).IsGE n) :
    (scalarExtension φ Z).map ((properOpenCoefficientInterchange A sq).hom.app E) ≫
        finiteCoefficientDirectImageMap φ p (D((k)_!open[ModuleCat.{u + 1} A]).obj E) ≫
        R((p)_*[ModuleCat.{u + 1} B]).map ((openScalarExtension φ k).hom.app E) =
      properOpenCoefficientComposite φ sq E := by
  let adj := derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} B) p
  have h := properOpen_coefficient_mate_transposed φ sq E _hE _hEB
  dsimp only at h
  exact (adj.homEquiv _ _).symm.injective h

end AlgebraicGeometry.Etale

namespace AlgebraicGeometry.ProEtale

private lemma transportOpenAdjunct
    {C D C' D' : Type*} [Category C] [Category D] [Category C'] [Category D']
    {L : C ⥤ D} {R : D ⥤ C} {L' : C' ⥤ D'} {R' : D' ⥤ C'}
    (a : L ⊣ R) (b : L' ⊣ R') (N : D ⥤ D') (M : C ⥤ C')
    (e : L ⋙ N ≅ M ⋙ L') (t : R ⋙ M ≅ N ⋙ R')
    (hc : ∀ Y : D, N.map (a.counit.app Y) =
      e.hom.app (R.obj Y) ≫ L'.map (t.hom.app Y) ≫ b.counit.app (N.obj Y))
    (X : C) (Y : D) (l : X ⟶ R.obj Y)
    (P : C') (d : M.obj X ≅ P) (Z : D') (c : N.obj Y ⟶ Z) :
    N.map ((a.homEquiv X Y).symm l) ≫ c = e.hom.app X ≫ L'.map d.hom ≫
      (b.homEquiv P Z).symm
        (d.inv ≫ M.map l ≫ t.hom.app Y ≫ R'.map c) := by
  dsimp only [Functor.comp_obj] at *
  simp only [Adjunction.homEquiv_counit, Functor.map_comp, Category.assoc]
  rw [← L'.map_comp_assoc, d.hom_inv_id]
  rw [hc Y]
  have hn := e.hom.naturality l
  dsimp only [Functor.comp_map] at hn
  rw [← Category.assoc, ← Category.assoc, hn]
  simp only [Category.assoc]
  rw [b.counit_naturality]
  simp only [L'.map_id, Category.id_comp]

variable {U V W Z : Scheme.{u}}
  [IsNoetherian U] [IsNoetherian V] [IsNoetherian W] [IsNoetherian Z]
  {k : U ⟶ V} {r : U ⟶ W} {p : V ⟶ Z} {i : W ⟶ Z}
  [IsOpenImmersion k] [IsOpenImmersion i] [IsProper r] [IsProper p]

/-- Inverse of the transported open-restriction exchange followed by the inverse
open unit. The factors are the named counit mates, exact pullback comparison and
open-extension comparison. It does not use the site square to define Gamma. -/
def properOpenSiteRestrictionInverse (A : Type (u + 1)) [CommRing A] [Finite A]
    (sq : IsPullback k r p i)
    (E : DerivedCategory.Plus (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    (lowerStar (ModuleCat.{u + 1} A) r).rightDerivedFunctorPlus.obj
        ((comparisonUpperStar (ModuleCat.{u + 1} A) U).mapDerivedCategoryPlus.obj E) ≅
      (upperStar (ModuleCat.{u + 1} A) i).mapDerivedCategoryPlus.obj
        ((lowerStar (ModuleCat.{u + 1} A) p).rightDerivedFunctorPlus.obj
          ((openImmersionLowerShriek (ModuleCat.{u + 1} A) k).mapDerivedCategoryPlus.obj
            ((comparisonUpperStar (ModuleCat.{u + 1} A) U).mapDerivedCategoryPlus.obj E))) :=
  ((@asIso _ _ _ _ (fixedComparisonDirectImageMatePlus A r)
      (isIso_fixedComparisonDirectImageMatePlus A r)).app E).symm ≪≫
    (comparisonUpperStar (ModuleCat.{u + 1} A) W).mapDerivedCategoryPlus.mapIso
      (Etale.properOpenCoefficientRestrictionPlus A sq E).symm ≪≫
    (fixedComparisonPullbackPlus A i).app
      ((Etale.lowerStar (ModuleCat.{u + 1} A) p).rightDerivedFunctorPlus.obj
        ((Etale.openImmersionLowerShriek
          (ModuleCat.{u + 1} A) k).mapDerivedCategoryPlus.obj E)) ≪≫
    (upperStar (ModuleCat.{u + 1} A) i).mapDerivedCategoryPlus.mapIso
      ((@asIso _ _ _ _ (fixedComparisonDirectImageMatePlus A p)
          (isIso_fixedComparisonDirectImageMatePlus A p)).app
          ((Etale.openImmersionLowerShriek
            (ModuleCat.{u + 1} A) k).mapDerivedCategoryPlus.obj E) ≪≫
        (lowerStar (ModuleCat.{u + 1} A) p).rightDerivedFunctorPlus.mapIso
          ((properOpenSiteExtensionIso A k).app E))

private lemma openComparisonPlus_counit
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    (j : X ⟶ Y) [IsOpenImmersion j]
    (B : DerivedCategory.Plus (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    (comparisonUpperStar (ModuleCat.{u + 1} A) Y).mapDerivedCategoryPlus.map
        ((Etale.derivedOpenImmersionLowerShriekUpperStarAdjunctionPlus
          (ModuleCat.{u + 1} A) j).counit.app B) =
      (properOpenSiteExtensionIso A j).hom.app
          ((Etale.upperStar (ModuleCat.{u + 1} A) j).mapDerivedCategoryPlus.obj B) ≫
        (openImmersionLowerShriek (ModuleCat.{u + 1} A) j).mapDerivedCategoryPlus.map
          ((fixedComparisonPullbackPlus A j).hom.app B) ≫
        (derivedOpenImmersionLowerShriekUpperStarAdjunctionPlus
          (ModuleCat.{u + 1} A) j).counit.app
          ((comparisonUpperStar (ModuleCat.{u + 1} A) Y).mapDerivedCategoryPlus.obj B) := by
  let c := Compactification.ofIsOpenImmersion j
  have : IsNoetherian c.Z := by
    change IsNoetherian Y
    infer_instance
  exact (compactSupportSiteComparison_open_counits A c).2 B

/-- Gamma on bounded-below etale-origin complexes, defined by the open adjunct of
inverse transported restriction and open unit, with the retained origin E. -/
def properOpenSiteInterchange (A : Type (u + 1)) [CommRing A] [Finite A]
    (sq : IsPullback k r p i)
    (E : DerivedCategory.Plus (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    (openImmersionLowerShriek (ModuleCat.{u + 1} A) i).mapDerivedCategoryPlus.obj
        ((lowerStar (ModuleCat.{u + 1} A) r).rightDerivedFunctorPlus.obj
          ((comparisonUpperStar (ModuleCat.{u + 1} A) U).mapDerivedCategoryPlus.obj E)) ⟶
      (lowerStar (ModuleCat.{u + 1} A) p).rightDerivedFunctorPlus.obj
        ((openImmersionLowerShriek (ModuleCat.{u + 1} A) k).mapDerivedCategoryPlus.obj
          ((comparisonUpperStar (ModuleCat.{u + 1} A) U).mapDerivedCategoryPlus.obj E)) :=
  (derivedOpenImmersionLowerShriekUpperStarAdjunctionPlus
    (ModuleCat.{u + 1} A) i).homEquiv _ _ |>.symm
      (properOpenSiteRestrictionInverse A sq E).hom

/-- The path through the etale proper/open comparison, the specified proper counit
mate and the open comparison. -/
def properOpenSiteComposite (A : Type (u + 1)) [CommRing A] [Finite A]
    (sq : IsPullback k r p i)
    (E : DerivedCategory.Plus (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A))) :=
  (comparisonUpperStar (ModuleCat.{u + 1} A) Z).mapDerivedCategoryPlus.map
      (Etale.properOpenCoefficientInterchangePlus A sq E).hom ≫
    (fixedComparisonDirectImageMatePlus A p).app
      ((Etale.openImmersionLowerShriek (ModuleCat.{u + 1} A) k).mapDerivedCategoryPlus.obj E) ≫
    (lowerStar (ModuleCat.{u + 1} A) p).rightDerivedFunctorPlus.map
      ((properOpenSiteExtensionIso A k).hom.app E)

/-- Site naturality square for the specified open adjunct, as an equation in the
unbounded category via the fully faithful bounded-below inclusion. -/
theorem properOpen_site_mate (A : Type (u + 1)) [CommRing A] [Finite A]
    (sq : IsPullback k r p i)
    (E : DerivedCategory.Plus (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    DerivedCategory.Plus.ι.map (properOpenSiteComposite A sq E) =
      DerivedCategory.Plus.ι.map
        ((properOpenSiteExtensionIso A i).hom.app
            ((Etale.lowerStar (ModuleCat.{u + 1} A) r).rightDerivedFunctorPlus.obj E) ≫
          (openImmersionLowerShriek (ModuleCat.{u + 1} A) i).mapDerivedCategoryPlus.map
            ((fixedComparisonDirectImageMatePlus A r).app E) ≫
          properOpenSiteInterchange A sq E) := by
  apply congrArg DerivedCategory.Plus.ι.map
  let a := Etale.derivedOpenImmersionLowerShriekUpperStarAdjunctionPlus
    (ModuleCat.{u + 1} A) i
  let b := derivedOpenImmersionLowerShriekUpperStarAdjunctionPlus
    (ModuleCat.{u + 1} A) i
  have hγ : (a.homEquiv _ _).symm
      (Etale.properOpenCoefficientRestrictionPlus A sq E).inv =
        (Etale.properOpenCoefficientInterchangePlus A sq E).hom := by
    rw [Etale.properOpenCoefficientRestrictionPlus_inv]
    change (a.homEquiv _ _).symm
      ((a.homEquiv _ _) (Etale.properOpenCoefficientInterchangePlus A sq E).hom) = _
    exact (a.homEquiv _ _).symm_apply_apply _
  have h := transportOpenAdjunct a b
    (comparisonUpperStar (ModuleCat.{u + 1} A) Z).mapDerivedCategoryPlus
    (comparisonUpperStar (ModuleCat.{u + 1} A) W).mapDerivedCategoryPlus
    (properOpenSiteExtensionIso A i) (fixedComparisonPullbackPlus A i)
    (openComparisonPlus_counit A i) _ _
    (Etale.properOpenCoefficientRestrictionPlus A sq E).inv _
    ((@asIso _ _ _ _ (fixedComparisonDirectImageMatePlus A r)
      (isIso_fixedComparisonDirectImageMatePlus A r)).app E) _
    ((fixedComparisonDirectImageMatePlus A p).app
        ((Etale.openImmersionLowerShriek
          (ModuleCat.{u + 1} A) k).mapDerivedCategoryPlus.obj E) ≫
      (lowerStar (ModuleCat.{u + 1} A) p).rightDerivedFunctorPlus.map
        ((properOpenSiteExtensionIso A k).hom.app E))
  rw [hγ] at h
  dsimp only [Functor.comp_obj] at h
  simpa only [properOpenSiteComposite, properOpenSiteInterchange,
    properOpenSiteRestrictionInverse, Iso.trans_hom, Iso.symm_hom, Iso.app_hom,
    Iso.app_inv, Functor.mapIso_hom, Functor.map_comp, asIso_hom, Category.assoc, b] using h

end AlgebraicGeometry.ProEtale
