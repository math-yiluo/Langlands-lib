/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Derived.DerivedFiberOpenFactorization
public import WeilConjectures.AlgebraicGeometry.PerfectComplex
public import Mathlib.CategoryTheory.Adjunction.Additive
import WeilConjectures.AlgebraicGeometry.TensorPullbackTilde
import all WeilConjectures.AlgebraicGeometry.AffineDerivedPullbackTensorTilde
import WeilConjectures.AlgebraicGeometry.Residue.ResidueTildeHomologyComparison
import WeilConjectures.AlgebraicGeometry.Affine.AffinePerfectSectionsCounit
import WeilConjectures.AlgebraicGeometry.AffineResidueScalarTransport
import all WeilConjectures.AlgebraicGeometry.Localized.LocalizedStrictPerfectResidueHomology

/-! # Natural derived pullback calculation on strictly perfect affine complexes

Source: Stacks Project, Tags 01IB, 08DW and 06YJ.
(blueprint: new-affine-perfect-residue-model-naturality)
-/

public section
set_option autoImplicit false
universe v
open CategoryTheory
namespace AlgebraicGeometry.Scheme
noncomputable section

set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The composition comparison for zero-preserving functors, with its composite source explicit. -/
private def zeroMapComplexCompIso {C D E : Type*} [Category C] [Category D] [Category E]
    [Limits.HasZeroMorphisms C] [Limits.HasZeroMorphisms D] [Limits.HasZeroMorphisms E]
    {F : C ⥤ D} {G : D ⥤ E} {H : C ⥤ E}
    [F.PreservesZeroMorphisms] [G.PreservesZeroMorphisms] [H.PreservesZeroMorphisms]
    (e : F ⋙ G ≅ H) :
    F.mapHomologicalComplex (.up ℤ) ⋙ G.mapHomologicalComplex (.up ℤ) ≅
      H.mapHomologicalComplex (.up ℤ) :=
  NatIso.mapHomologicalComplex e (.up ℤ)

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- A reconstruction counit and a termwise comparison give the comparison on a subcategory. -/
private def reconstructionComparison {Z C D E B : Type*}
    [Category Z] [Category C] [Category D] [Category E] [Category B]
    [Limits.HasZeroMorphisms C] [Limits.HasZeroMorphisms D]
    [Limits.HasZeroMorphisms E] [Limits.HasZeroMorphisms B]
    (ι : Z ⥤ CochainComplex C ℤ) (F : C ⥤ D) (T : D ⥤ E)
    (Sh : D ⥤ C) (J : C ⥤ B) (L : E ⥤ B)
    [F.PreservesZeroMorphisms] [T.PreservesZeroMorphisms]
    [Sh.PreservesZeroMorphisms] [J.PreservesZeroMorphisms] [L.PreservesZeroMorphisms]
    (ρ : F.mapHomologicalComplex (.up ℤ) ⋙ Sh.mapHomologicalComplex (.up ℤ) ⟶ 𝟭 _)
    (hρ : IsIso (Functor.whiskerLeft ι ρ)) (α : Sh ⋙ J ≅ T ⋙ L) :
    ι ⋙ J.mapHomologicalComplex (.up ℤ) ≅
      ι ⋙ (F ⋙ T).mapHomologicalComplex (.up ℤ) ⋙ L.mapHomologicalComplex (.up ℤ) :=
  let Fc := F.mapHomologicalComplex (.up ℤ)
  let Tc := T.mapHomologicalComplex (.up ℤ)
  let Shc := Sh.mapHomologicalComplex (.up ℤ)
  let Jc := J.mapHomologicalComplex (.up ℤ)
  let Lc := L.mapHomologicalComplex (.up ℤ)
  let r : ι ⋙ Fc ⋙ Shc ≅ ι :=
    @asIso _ _ _ _ (Functor.whiskerLeft ι ρ) hρ ≪≫ Functor.rightUnitor ι
  let s : Shc ⋙ Jc ≅ Tc ⋙ Lc :=
    zeroMapComplexCompIso α ≪≫ (zeroMapComplexCompIso (Iso.refl (T ⋙ L))).symm
  let t : Fc ⋙ Tc ≅ (F ⋙ T).mapHomologicalComplex (.up ℤ) :=
    zeroMapComplexCompIso (Iso.refl (F ⋙ T))
  Functor.isoWhiskerRight r.symm Jc ≪≫
    Functor.isoWhiskerLeft (ι ⋙ Fc) s ≪≫
    Functor.isoWhiskerRight (Functor.isoWhiskerLeft ι t) Lc

/-- Paste comparison isomorphisms before and after a common functor. -/
private def whiskeredComparison {Z C D E S : Type*}
    [Category Z] [Category C] [Category D] [Category E] [Category S]
    (X : Z ⥤ C) (F : C ⥤ D) (Y : Z ⥤ E) (J : E ⥤ D) (H : D ⥤ S)
    (R : C ⥤ S) (M : E ⥤ S) (θ : R ≅ F ⋙ H) (d : X ⋙ F ≅ Y ⋙ J)
    (η : J ⋙ H ≅ M) : X ⋙ R ≅ Y ⋙ M :=
  Functor.isoWhiskerLeft X θ ≪≫ Functor.isoWhiskerRight d H ≪≫
    Functor.isoWhiskerLeft Y η

/-- Transport a derived counit comparison along an exact functor and an ordinary-pullback iso. -/
private def transportedCounitComparison {C D E I : Type*}
    [Category C] [Category D] [Category E] [Category I]
    [Abelian C] [Abelian D] [Abelian E]
    [HasDerivedCategory.{v} C] [HasDerivedCategory.{v} D] [HasDerivedCategory.{v} E]
    (ι : I ⥤ CochainComplex C ℤ) (V : C ⥤ D) [V.Additive]
    [Limits.PreservesFiniteLimits V] [Limits.PreservesFiniteColimits V]
    (E₀ PG : D ⥤ E) [E₀.Additive] [PG.Additive]
    (L : DerivedCategory.{v} D ⥤ DerivedCategory.{v} E)
    (ε : DerivedCategory.Qh.{v} ⋙ L ⟶
      E₀.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh.{v})
    (hε : IsIso (Functor.whiskerLeft
      ((ι ⋙ V.mapHomologicalComplex (.up ℤ)) ⋙ HomotopyCategory.quotient D (.up ℤ)) ε))
    (τ : E₀ ≅ PG) :
    ι ⋙ DerivedCategory.Q.{v} ⋙ V.mapDerivedCategory ⋙ L ≅
      ι ⋙ (V ⋙ PG).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q.{v} :=
  let F := ι ⋙ V.mapHomologicalComplex (.up ℤ)
  let c : F ⋙ DerivedCategory.Q.{v} ⋙ L ≅
      F ⋙ E₀.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q.{v} :=
    Functor.isoWhiskerRight
      (Functor.isoWhiskerLeft F (DerivedCategory.quotientCompQhIso _).symm) L ≪≫
    @asIso _ _ _ _ (Functor.whiskerLeft (F ⋙ HomotopyCategory.quotient _ (.up ℤ)) ε) hε ≪≫
    Functor.isoWhiskerRight
      (Functor.isoWhiskerLeft F (E₀.mapHomotopyCategoryFactors (.up ℤ)))
      DerivedCategory.Qh ≪≫
    Functor.isoWhiskerLeft (F ⋙ E₀.mapHomologicalComplex (.up ℤ))
      (DerivedCategory.quotientCompQhIso _)
  Functor.isoWhiskerLeft ι (Functor.isoWhiskerRight V.mapDerivedCategoryFactors L) ≪≫
    c ≪≫ Functor.isoWhiskerRight
      (Functor.isoWhiskerLeft F (NatIso.mapHomologicalComplex τ (.up ℤ))) DerivedCategory.Q ≪≫
    Functor.isoWhiskerRight (Functor.isoWhiskerLeft ι
      (Functor.mapHomologicalComplexCompIso (Iso.refl (V ⋙ PG)) (.up ℤ))) DerivedCategory.Q

/-- The termwise comparison between the ordinary residue pullback of the affine associated
sheaf and the associated sheaf of the residue extension of sections. -/
private def residueTermComparison (W : Scheme.{v}) (w : W) (U : W.Opens)
    (hwU : w ∈ U) (hU : IsAffineOpen U) :
    let V : SheafOfModules.{v} ((moduleRings W.toRingedSpace).over U) ⥤
        SheafOfModules.{v} (moduleRings U.toScheme.toRingedSpace) :=
      (Modules.overEquiv U).functor
    affinePerfectSheafification W U hU ⋙
      (V ⋙ Modules.pullback (openResiduePoint W w U hwU)) ≅
        ModuleCat.extendScalars.{v, v, v} (W.evaluation U w hwU).hom ⋙
          tilde.functor (W.residueField w) := by
  classical
  dsimp only
  let A := W.presheaf.obj (.op U)
  let z : U := ⟨w, hwU⟩
  let p := hU.isoSpec.hom z
  let e := asIso (U.ι.residueFieldMap z) ≪≫
    (asIso (hU.isoSpec.hom.residueFieldMap z)).symm ≪≫ Spec.residueFieldIso A p
  let ψ := algebraMap A p.asIdeal.ResidueField
  let φ := (CommRingCat.ofHom ψ ≫ e.inv).hom
  let g := openResiduePoint W w U hwU
  have hchart : g ≫ hU.isoSpec.hom = Spec.map (CommRingCat.ofHom φ) := by
    dsimp [g, openResiduePoint, φ, e, ψ, p, z]
    rw [Category.assoc, ← Hom.SpecMap_residueFieldMap_fromSpecResidueField]
    rw [← Spec.map_residueFieldIso_inv_eq_fromSpecResidueField]
    simp only [← Spec.map_comp, Category.assoc]
    rfl
  let TA := tilde.functor A
  let RC := Modules.restrictFunctor hU.isoSpec.hom
  let V := (Modules.overEquiv U).functor
  let B := (Modules.overEquiv U).inverse
  let Sh := affinePerfectSheafification W U hU
  let δ : Sh ⋙ V ≅ TA ⋙ RC :=
    Functor.associator TA (RC ⋙ B) V ≪≫
      Functor.isoWhiskerLeft TA (Functor.associator RC B V) ≪≫
      Functor.isoWhiskerLeft TA
        (Functor.isoWhiskerLeft RC (Modules.overEquiv U).counitIso) ≪≫
      Functor.isoWhiskerLeft TA (Functor.rightUnitor RC)
  let η : ModuleCat.extendScalars e.inv.hom ≅ ModuleCat.restrictScalars e.hom.hom :=
    (ModuleCat.extendRestrictScalarsAdj e.inv.hom).leftAdjointUniq
      (ModuleCat.restrictScalarsEquivalenceOfRingEquiv e.commRingCatIsoToRingEquiv).toAdjunction
  let S := ModuleCat.extendScalars.{v, v, v} ψ
  let R := ModuleCat.restrictScalars.{v, v, v} e.hom.hom
  let σ : ModuleCat.extendScalars φ ≅ S ⋙ R :=
    ModuleCat.extendScalarsComp ψ e.inv.hom ≪≫ Functor.isoWhiskerLeft S η
  let L := tilde.functor (W.residueField w)
  let f := Spec.map (CommRingCat.ofHom φ)
  let τ : Modules.tensorPullback f ≅ Modules.pullback f :=
    (Modules.nonempty_tensorPullbackAdjunction f).some.leftAdjointUniq
      (Modules.pullbackPushforwardAdjunction f)
  let β := Classical.choose (Modules.exists_tensorPullback_tilde_iso (CommRingCat.ofHom φ))
  let δs := Classical.choice (affine_residue_scalar_transport W U hU z)
  exact (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight δ (Modules.pullback g) ≪≫
    Functor.isoWhiskerRight
      (Functor.isoWhiskerLeft TA (Modules.restrictFunctorIsoPullback hU.isoSpec.hom)) _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft TA (Modules.pullbackComp g hU.isoSpec.hom) ≪≫
    Functor.isoWhiskerLeft TA (Modules.pullbackCongr hchart) ≪≫
    Functor.isoWhiskerLeft TA τ.symm ≪≫ β ≪≫
    Functor.isoWhiskerRight σ L ≪≫ Functor.isoWhiskerRight δs L

attribute [local irreducible] Modules.overEquiv affinePerfectSheafification openResiduePoint

variable
  [∀ Y : Scheme.{v},
    HasDerivedCategory.{v + 1} (SheafOfModules.{v} (moduleRings Y.toRingedSpace))]
  [∀ (Y : Scheme.{v}) (U : Y.Opens), HasDerivedCategory.{v + 1}
    (SheafOfModules.{v} ((moduleRings Y.toRingedSpace).over U))]

-- The natural comparison traverses complex, homotopy and derived localization functors.
set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- The natural isomorphism by which termwise residue extension of sections computes local
derived fibre cohomology in degree one on strictly perfect complexes.
Source: Stacks Project, Tags 01IB, 08DW and 06YJ.
(blueprint: new-affine-perfect-residue-model-naturality)

Construction: Work in the full subcategory of strictly perfect complexes. Transport each
complex by the canonical over-site equivalence. Boundedness and finite-free
retractions imply K-flatness, so the chosen derived-pullback counit is invertible
on this whole subcategory. Compute its ordinary pullback by the natural affine
associated-sheaf/base-change formula, using the natural terminal-section
reconstruction counit. The canonical field transport makes the coefficient map
exactly section evaluation. Take homology and global sections on the residue
spectrum; these sections are exact and undo associated sheaves. All factors
are natural isomorphisms on the full subcategory. -/
def affinePerfectResidueModelIso
    (W : Scheme.{v}) (w : W) (U : W.Opens) (hwU : w ∈ U) (hU : IsAffineOpen U) :
    let F : SheafOfModules.{v} ((moduleRings W.toRingedSpace).over U) ⥤
        ModuleCat.{v} Γ(W, U) := SheafOfModules.evaluation _ (.op (Over.mk (𝟙 U)))
    letI : F.Additive := inferInstanceAs
      ((SheafOfModules.forget _ ⋙ PresheafOfModules.evaluation _ _).Additive)
    let T := ModuleCat.extendScalars.{v, v, v} (W.evaluation U w hwU).hom
    letI : T.Additive := (ModuleCat.extendRestrictScalarsAdj _).left_adjoint_additive
    let G := (F ⋙ T).mapHomologicalComplex (.up ℤ)
    let P : ObjectProperty (CochainComplex
      (SheafOfModules.{v} ((moduleRings W.toRingedSpace).over U)) ℤ) :=
      IsStrictlyPerfect W U
    P.ι ⋙ G ⋙
        HomologicalComplex.homologyFunctor (ModuleCat.{v} (W.residueField w)) (.up ℤ) 1 ≅
      P.ι ⋙ DerivedCategory.Q ⋙ localDerivedFiberCohomologyFunctor W w U hwU 1 := by
  dsimp only
  classical
  let D := SheafOfModules.{v} ((moduleRings W.toRingedSpace).over U)
  let A := SheafOfModules.{v} (moduleRings U.toScheme.toRingedSpace)
  let B := SheafOfModules.{v} (moduleRings (Spec (W.residueField w)).toRingedSpace)
  let QD : CochainComplex D ℤ ⥤ DerivedCategory.{v + 1} D := DerivedCategory.Q
  let QB : CochainComplex B ℤ ⥤ DerivedCategory.{v + 1} B := DerivedCategory.Q
  let P : ObjectProperty (CochainComplex D ℤ) := IsStrictlyPerfect W U
  let ι := P.ι
  let V : D ⥤ A := (Modules.overEquiv U).functor
  have : V.IsEquivalence := (Modules.overEquiv U).isEquivalence_functor
  have : Limits.PreservesFiniteLimits V := inferInstance
  have : Limits.PreservesFiniteColimits V := inferInstance
  have : V.Additive := Functor.additive_of_preserves_binary_products V
  let VD : DerivedCategory.{v + 1} D ⥤ DerivedCategory.{v + 1} A := V.mapDerivedCategory
  let Vc := V.mapHomologicalComplex (.up ℤ)
  let g := openResiduePoint W w U hwU
  let Lg : DerivedCategory.{v + 1} A ⥤ DerivedCategory.{v + 1} B := derivedPullback g
  have hcounit := tensorDerivedCounit g
  have hEadd := hcounit.fst
  let ε := Classical.choose hcounit.snd
  have hflat := (Classical.choose_spec hcounit.snd).2
  let E : A ⥤ B := Modules.tensorPullback g
  have : E.Additive := hEadd
  have hε : IsIso (Functor.whiskerLeft
      ((ι ⋙ Vc) ⋙ HomotopyCategory.quotient A (.up ℤ)) ε) := by
    apply (NatTrans.isIso_iff_isIso_app _).2
    intro K
    exact hflat (Vc.obj K.obj) (strictlyPerfect_overEquiv_isKFlat W U K.obj K.property)
  let PG : A ⥤ B := Modules.pullback g
  have : PG.Additive := Modules.instAdditivePullback g
  let J : D ⥤ B := V ⋙ PG
  have : J.Additive := inferInstanceAs (V ⋙ PG).Additive
  let τ : E ≅ PG :=
    (Modules.nonempty_tensorPullbackAdjunction g).some.leftAdjointUniq
      (Modules.pullbackPushforwardAdjunction g)
  let c' : ι ⋙ QD ⋙ VD ⋙ Lg ≅ ι ⋙ J.mapHomologicalComplex (.up ℤ) ⋙ QB :=
    transportedCounitComparison ι V E PG Lg ε hε τ
  let F : D ⥤ ModuleCat.{v} Γ(W, U) :=
    SheafOfModules.evaluation _ (.op (Over.mk (𝟙 U)))
  have : F.Additive := inferInstanceAs
    ((SheafOfModules.forget _ ⋙ PresheafOfModules.evaluation _ _).Additive)
  let T := ModuleCat.extendScalars.{v, v, v} (W.evaluation U w hwU).hom
  have : T.Additive :=
    (ModuleCat.extendRestrictScalarsAdj (W.evaluation U w hwU).hom).left_adjoint_additive
  let G := (F ⋙ T).mapHomologicalComplex (.up ℤ)
  let Sh := affinePerfectSheafification W U hU
  have : Sh.PreservesZeroMorphisms :=
    affinePerfectSheafification_preservesZeroMorphisms W U hU
  let L : ModuleCat.{v} (W.residueField w) ⥤ B := tilde.functor (W.residueField w)
  have : L.Additive := ⟨by intros; exact tilde.map_add _ _⟩
  have hsections := affine_perfect_sections_counit W U hU
  let ρ := Classical.choose hsections
  have hρ := Classical.choose_spec hsections
  let α : Sh ⋙ J ≅ T ⋙ L := residueTermComparison W w U hwU hU
  let a : ι ⋙ J.mapHomologicalComplex (.up ℤ) ≅
      ι ⋙ G ⋙ L.mapHomologicalComplex (.up ℤ) :=
    reconstructionComparison ι F T Sh J L ρ
      ((NatTrans.isIso_iff_isIso_app _).2 (fun K ↦ hρ K.obj K.property)) α
  let d : ι ⋙ QD ⋙ VD ⋙ Lg ≅ ι ⋙ G ⋙ L.mapHomologicalComplex (.up ℤ) ⋙ QB :=
    c' ≪≫ Functor.isoWhiskerRight a QB
  let Γ : B ⥤ ModuleCat.{v} (W.residueField w) :=
    moduleSpecΓFunctor (R := W.residueField w)
  let H := DerivedCategory.homologyFunctor B 1
  let HM := HomologicalComplex.homologyFunctor (ModuleCat.{v} (W.residueField w)) (.up ℤ) 1
  let θ : localDerivedFiberCohomologyFunctor W w U hwU 1 ≅ VD ⋙ Lg ⋙ H ⋙ Γ :=
    eqToIso (localDerivedFiberCohomologyFunctor_eq W w U hwU 1)
  let η : L.mapHomologicalComplex (.up ℤ) ⋙ QB ⋙ H ⋙ Γ ≅ HM :=
    residueTildeHomologyComparison (W.residueField w) (Field.toIsField (W.residueField w)) 1
  let β : ι ⋙ QD ⋙ localDerivedFiberCohomologyFunctor W w U hwU 1 ≅ ι ⋙ G ⋙ HM :=
    whiskeredComparison (ι ⋙ QD) (VD ⋙ Lg) (ι ⋙ G)
      (L.mapHomologicalComplex (.up ℤ) ⋙ QB) (H ⋙ Γ)
      (localDerivedFiberCohomologyFunctor W w U hwU 1) HM θ d η
  exact β.symm

end
end AlgebraicGeometry.Scheme
