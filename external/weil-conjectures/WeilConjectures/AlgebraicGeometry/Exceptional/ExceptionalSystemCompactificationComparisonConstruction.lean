/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Exceptional.ExceptionalSystemInterfaces
import WeilConjectures.AlgebraicGeometry.Exceptional.ExceptionalSystemPullbackSquareConstruction
import WeilConjectures.AlgebraicGeometry.Exceptional.ExceptionalSystemOpenMateInvertibility
import all WeilConjectures.Algebra.Homology.Coefficient.CoefficientSystemOrdinaryImages
import all WeilConjectures.Algebra.Homology.Coefficient.CoefficientSystemUnboundedComparison
import WeilConjectures.CategoryTheory.Derived.DerivedMateComparison

/-! # Construction of proper/open comparison data -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option genSizeOf false
set_option genInjectivity false
set_option genSizeOfSpec false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite SheafOfModules
namespace AlgebraicGeometry

attribute [local instance 20000] strictEtaleSystemDerived strictEtaleLevelDerived
  exceptionalProSystemDerived exceptionalProLevelDerived

section
universe a av b bv c cv d dv q
variable {A : Type a} [Category.{av} A] [Abelian A] [HasDerivedCategory.{q} A]
  {B : Type b} [Category.{bv} B] [Abelian B] [HasDerivedCategory.{q} B]
  {C : Type c} [Category.{cv} C] [Abelian C] [HasDerivedCategory.{q} C]
  {D : Type d} [Category.{dv} D] [Abelian D] [HasDerivedCategory.{q} D]
  {L : A ⥤ B} {R : B ⥤ A} {L' : C ⥤ D} {R' : D ⥤ C}
  [L.Additive] [R.Additive] [L'.Additive] [R'.Additive]
  {G : A ⥤ C} {H : B ⥤ D} [G.Additive] [H.Additive]
  {LD : DerivedCategory A ⥤ DerivedCategory B}
  {RD : DerivedCategory B ⥤ DerivedCategory A}
  {LD' : DerivedCategory C ⥤ DerivedCategory D}
  {RD' : DerivedCategory D ⥤ DerivedCategory C}
  {GD : DerivedCategory A ⥤ DerivedCategory C}
  {HD : DerivedCategory B ⥤ DerivedCategory D}

-- The representative mate calculation crosses several functor categories.
private theorem localizeMate
    (adj : L ⊣ R) (adj' : L' ⊣ R') (ad : LD ⊣ RD) (ad' : LD' ⊣ RD')
    (φL : DerivedCategory.Q ⋙ LD ≅ L.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (φR : DerivedCategory.Q ⋙ RD ≅ R.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (φL' : DerivedCategory.Q ⋙ LD' ≅ L'.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (φR' : DerivedCategory.Q ⋙ RD' ≅ R'.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (φG : DerivedCategory.Q ⋙ GD ≅ G.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (φH : DerivedCategory.Q ⋙ HD ≅ H.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (hL : ∀ P K (f : (L.mapHomologicalComplex (.up ℤ)).obj P ⟶ K),
      ad.homEquiv _ _ (φL.hom.app P ≫ DerivedCategory.Q.map f) =
        DerivedCategory.Q.map ((adj.mapHomologicalComplex (.up ℤ)).homEquiv P K f) ≫
          φR.inv.app K)
    (hL' : ∀ P K (f : (L'.mapHomologicalComplex (.up ℤ)).obj P ⟶ K),
      ad'.homEquiv _ _ (φL'.hom.app P ≫ DerivedCategory.Q.map f) =
        DerivedCategory.Q.map ((adj'.mapHomologicalComplex (.up ℤ)).homEquiv P K f) ≫
          φR'.inv.app K)
    (α : TwoSquare G L L' H) (β : TwoSquare R H G R')
    (hm : mateEquiv adj adj' α = β)
    (αD : TwoSquare GD LD LD' HD) (βD : TwoSquare RD HD GD RD')
    (hα : ∀ P, αD.app (DerivedCategory.Q.obj P) ≫
      HD.map (φL.hom.app P) ≫ φH.hom.app ((L.mapHomologicalComplex (.up ℤ)).obj P) =
        LD'.map (φG.hom.app P) ≫
          φL'.hom.app ((G.mapHomologicalComplex (.up ℤ)).obj P) ≫
          DerivedCategory.Q.map ((α.mapHomologicalComplex (.up ℤ)).app P))
    (hβ : ∀ K, βD.app (DerivedCategory.Q.obj K) ≫
      RD'.map (φH.hom.app K) ≫ φR'.hom.app ((H.mapHomologicalComplex (.up ℤ)).obj K) =
        GD.map (φR.hom.app K) ≫
          φG.hom.app ((R.mapHomologicalComplex (.up ℤ)).obj K) ≫
          DerivedCategory.Q.map ((β.mapHomologicalComplex (.up ℤ)).app K)) :
    mateEquiv ad ad' αD = βD := by
  have hrep (P : CochainComplex A ℤ) := derivedMate_comparison
    (adj.mapHomologicalComplex (.up ℤ)) (adj'.mapHomologicalComplex (.up ℤ)) ad ad'
    φL.hom φL'.hom φR φR' φG φH hL hL'
    (.mk _ _ _ _ (β.mapHomologicalComplex (.up ℤ))) βD hβ
    (α.mapHomologicalComplex (.up ℤ))
    (fun P ↦ by
      rw [Adjunction.homEquiv_unit]
      apply HomologicalComplex.hom_ext
      intro i
      have hu := unit_mateEquiv adj adj' α (P.X i)
      change G.map (adj.unit.app (P.X i)) ≫
        ((mateEquiv adj adj' α)).app (L.obj (P.X i)) =
          adj'.unit.app (G.obj (P.X i)) ≫ R'.map (α.app (P.X i)) at hu
      rw [hm] at hu
      exact hu.symm) P
  have heq : ((mateEquiv ad ad').symm βD) = αD := by
    apply (Localization.fullyFaithfulWhiskeringLeft DerivedCategory.Q
      (HomologicalComplex.quasiIso A (.up ℤ)) (DerivedCategory D)).map_injective
    apply NatTrans.ext
    funext P
    apply (cancel_mono (HD.map (φL.hom.app P) ≫
      φH.hom.app ((L.mapHomologicalComplex (.up ℤ)).obj P))).1
    exact (hrep P).trans (hα P).symm
  exact (congrArg (mateEquiv ad ad') heq).symm.trans
    ((mateEquiv ad ad').apply_symm_apply βD)
end

variable {O : Type (u + 1)} [CommRing O] {ell : O}
  {X Y : Scheme.{u}} {f : X ⟶ Y} {c : Compactification f}

private theorem etaleOpenEvaluationMate (S : StrictEtaleCompactSupport O ell c) (n : ℕ) :
    (mateEquiv S.derivedOpenAdjunction (S.levelDerivedOpenAdjunction n)
      (.mk _ _ _ _ (S.openDerivedEvaluation n).inv)) =
      (S.openDerived.inverseEvaluation n).hom := by
  apply localizeMate S.val.openAdjunction (S.val.levelOpenAdjunction n)
    S.derivedOpenAdjunction (S.levelDerivedOpenAdjunction n)
    S.val.openFactors S.openDerived.system.inverseFactors
    (S.val.levelOpenFactors n) (S.openDerived.level n).inverseFactors
    (S.PX.evaluationFactors n) (S.PZ.evaluationFactors n)
    S.property.2.2.1 (S.property.2.2.2.1 n)
    (.mk _ _ _ _ (S.val.openEvaluation n).inv)
    (.mk _ _ _ _ (S.openImage.inverseEvaluation n).hom)
    (S.property.2.1 n).symm
  · exact derivedSquare_symm_rep S.val.openExtension
      (coefficientEvaluation.{u + 1, u, u + 1} (J := X.smallEtaleTopology) n)
      (coefficientEvaluation.{u + 1, u, u + 1} (J := c.Z.smallEtaleTopology) n) (S.val.levelOpen n)
      S.derivedOpen (S.PX.evaluation n) (S.PZ.evaluation n) (S.levelDerivedOpen n)
      S.val.openFactors (S.PX.evaluationFactors n) (S.PZ.evaluationFactors n)
      (S.val.levelOpenFactors n) (S.val.openEvaluation n) (S.openDerivedEvaluation n)
      (S.property.2.2.2.2 n)
  · exact S.openDerived.inverseEvaluation_rep n

private theorem proOpenEvaluationMate
    {PX : ExceptionalProEvaluation X O ell} {PY : ExceptionalProEvaluation Y O ell}
    {PZ : ExceptionalProEvaluation c.Z O ell}
    (P : ExceptionalProCompactSupport O ell c PX PY PZ) (n : ℕ) :
    (mateEquiv P.val.derivedOpenAdjunction (P.val.levelDerivedOpenAdjunction n)
      (.mk _ _ _ _ (P.val.openDerivedEvaluation n).inv)) =
      (P.val.openDerived.inverseEvaluation n).hom := by
  apply localizeMate P.val.openAdjunction (P.val.levelOpenAdjunction n)
    P.val.derivedOpenAdjunction (P.val.levelDerivedOpenAdjunction n)
    P.val.openFactors P.val.openDerived.system.inverseFactors
    (P.val.levelOpenFactors n) (P.val.openDerived.level n).inverseFactors
    (PX.evaluationFactors n) (PZ.evaluationFactors n)
    P.property.2.2.1 (P.property.2.2.2.1 n)
    (.mk _ _ _ _ (P.val.openEvaluation n).inv)
    (.mk _ _ _ _ (P.val.openImage.inverseEvaluation n).hom)
    (P.property.2.1 n).symm
  · exact derivedSquare_symm_rep P.val.openExtension
      (coefficientEvaluation.{u + 1, u, u + 1} (J := Scheme.ProEt.topology X) n)
      (coefficientEvaluation.{u + 1, u, u + 1}
        (J := Scheme.ProEt.topology c.Z) n) (P.val.levelOpen n)
      P.val.derivedOpen (PX.evaluation n) (PZ.evaluation n) (P.val.levelDerivedOpen n)
      P.val.openFactors (PX.evaluationFactors n) (PZ.evaluationFactors n)
      (P.val.levelOpenFactors n) (P.val.openEvaluation n) (P.val.openDerivedEvaluation n)
      (P.property.2.2.2.2 n)
  · exact P.val.openDerived.inverseEvaluation_rep n

private theorem inverseMate_cube
    {A B C D A' B' C' D' : Type*}
    [Category A] [Category B] [Category C] [Category D]
    [Category A'] [Category B'] [Category C'] [Category D']
    {L : A ⥤ B} {R : B ⥤ A} {M : C ⥤ D} {N : D ⥤ C}
    {l : A' ⥤ B'} {r : B' ⥤ A'} {m : C' ⥤ D'} {n : D' ⥤ C'}
    (a : L ⊣ R) (b : M ⊣ N) (a' : l ⊣ r) (b' : m ⊣ n)
    {G : A ⥤ C} {H : B ⥤ D} {g : A' ⥤ C'} {h : B' ⥤ D'}
    {EA : A ⥤ A'} {EB : B ⥤ B'} {EC : C ⥤ C'} {ED : D ⥤ D'}
    (γ : G ⋙ EC ≅ EA ⋙ g) (η : H ⋙ ED ≅ EB ⋙ h)
    (e : L ⋙ EB ≅ EA ⋙ l) (e' : M ⋙ ED ≅ EC ⋙ m)
    (α : TwoSquare G L M H) (α' : TwoSquare g l m h)
    (compatible : ∀ K : B,
      EC.map ((mateEquiv a b α).app K) ≫
        (mateEquiv b b' (.mk _ _ _ _ e'.inv)).app (H.obj K) ≫
        n.map (η.hom.app K) =
      γ.hom.app (R.obj K) ≫
        g.map ((mateEquiv a a' (.mk _ _ _ _ e.inv)).app K) ≫
        (mateEquiv a' b' α').app (EB.obj K)) (K : A) :
    e'.inv.app (G.obj K) ≫ ED.map (α.app K) ≫ η.hom.app (L.obj K) =
      m.map (γ.hom.app K) ≫ α'.app (EA.obj K) ≫ h.map (e.inv.app K) := by
  let s := (α.hComp (.mk _ _ _ _ e'.inv)).whiskerBottom η.hom
  let t := ((TwoSquare.mk _ _ _ _ e.inv).hComp α').whiskerTop γ.hom
  have heq : s = t := by
    apply (mateEquiv a b').injective
    dsimp only [s, t]
    rw [mate_whiskerBottom, mate_whiskerTop, mateEquiv_vcomp, mateEquiv_vcomp]
    · ext K
      simpa only [TwoSquare.whiskerLeft, TwoSquare.whiskerRight,
        TwoSquare.vComp_app, NatTrans.comp_app, whiskerLeft_app, whiskerRight_app,
        Category.assoc] using compatible K
  have hc := congr_app heq K
  simpa only [s, t, TwoSquare.whiskerBottom, TwoSquare.whiskerTop,
    TwoSquare.hComp_app, NatTrans.comp_app, whiskerLeft_app, whiskerRight_app,
    Category.assoc] using hc
variable {O : Type (u + 1)} [CommRing O] {ell : O}
  {X Y : Scheme.{u}} {f : X ⟶ Y} {c : Compactification f}
  {S : StrictEtaleCompactSupport O ell c}
  (CX : ExceptionalSystemSiteComparison O ell X S.PX)
  (CY : ExceptionalSystemSiteComparison O ell Y S.PY)
  (CZ : ExceptionalSystemSiteComparison O ell c.Z S.PZ)

-- Invert the two vertical sides of a square using only the category laws.
private theorem inverseSquare_eq
    {C : Type*} [Category C] {A B D E F G : C}
    (a : A ⟶ B) (b : D ⟶ E) [IsIso a] [IsIso b]
    (e : F ≅ A) (f : E ≅ G) (s : F ⟶ D) (t : B ⟶ G)
    (h : e.hom ≫ a ≫ t = s ≫ b ≫ f.hom) :
    inv a ≫ e.inv ≫ s = t ≫ f.inv ≫ inv b := by
  have hh := congrArg (fun k ↦ inv a ≫ e.inv ≫ k ≫ f.inv ≫ inv b) h
  simpa only [Category.assoc, Iso.inv_hom_id_assoc, Iso.hom_inv_id_assoc,
    IsIso.inv_hom_id_assoc, IsIso.hom_inv_id, Category.comp_id] using hh.symm

-- The system and level mate identities require simultaneous localization comparisons.
/-- Construct the normalized proper and open compactification comparisons.
Source: Zheng Construction 5.15 and Lemmas 4.10, 5.16 and 5.22
(blueprint: lem-sf-exceptional-system-comparison-exists).

Proof: Construct the ordinary proper and open inverse-image squares and localize them
with their evaluation equations. The finite open inverse mate is invertible by the
extension-by-zero comparison; joint reflection by the level evaluations gives the
system mate. Localize this mate using the representative adjunction equations.
The mate cube gives the ordinary and derived open-evaluation equations, completing
all fields and coherence equations of the comparison record. -/
theorem exceptionalSystemCompactificationComparison_exists
    [∀ n : ℕ, Finite (O ⧸ (Ideal.span ({ell} : Set O)) ^ (n + 1))]
    (hX : ExceptionalSystemSiteEquivalence CX)
    (hY : ExceptionalSystemSiteEquivalence CY)
    (hZ : ExceptionalSystemSiteEquivalence CZ)
    (P : ExceptionalProCompactSupport O ell c
      CX.proEvaluation CY.proEvaluation CZ.proEvaluation) :
    Nonempty (ExceptionalSystemCompactificationComparison S CX CY CZ P) := by
  obtain ⟨RP⟩ := exceptionalSystemPullbackSquare_exists c.g CZ CY
    S.properImage P.val.properImage S.properDerived P.val.properDerived
  obtain ⟨RO⟩ := exceptionalSystemPullbackSquare_exists c.i CX CZ
    S.openImage P.val.openImage S.openDerived P.val.openDerived
  have hi := exceptionalSystemLevelOpenMate_isIso CX CY CZ hX hY hZ P RO
  let τ := (mateEquiv S.val.openAdjunction P.val.openAdjunction).symm
    (.mk _ _ _ _ RO.ordinary.inv)
  let τn (n : ℕ) := (mateEquiv (S.val.levelOpenAdjunction n)
    (P.val.levelOpenAdjunction n)).symm (.mk _ _ _ _ (RO.level n).inv)
  have (n : ℕ) : IsIso (τn n) := hi n
  have hτ (M) : IsIso (τ.app M) := by
    refine @JointlyReflectIsomorphisms.isIso _ _ _ _ _ _
      (evaluations_jointlyReflect (K := Scheme.ProEt.topology c.Z) O ell) _ _
      (τ.app M) (fun n ↦ ?_)
    have hc := inverseMate_cube S.val.openAdjunction P.val.openAdjunction
      (S.val.levelOpenAdjunction n) (P.val.levelOpenAdjunction n)
      (CX.ordinary.inverseEvaluation n) (CZ.ordinary.inverseEvaluation n)
      (S.val.openEvaluation n) (P.val.openEvaluation n) τ (τn n) (by
        intro K
        simp only [τ, τn, Equiv.apply_symm_apply]
        have hs := congrArg (fun t ↦ t.app K) (S.property.2.1 n)
        have hp := congrArg (fun t ↦ t.app (CZ.ordinary.inverse.obj K))
          (P.property.2.1 n)
        erw [← hs, ← hp]
        apply (cancel_epi ((coefficientEvaluation.{u + 1, u, u + 1}
          (J := Scheme.ProEt.topology X) n).map (RO.ordinary.hom.app K))).1
        simp only [← Functor.map_comp_assoc, Iso.hom_inv_id_app]
        erw [(coefficientEvaluation.{u + 1, u, u + 1}
          (J := Scheme.ProEt.topology X) n).map_id, Category.id_comp]
        apply (cancel_mono ((RO.level n).hom.app
          ((coefficientEvaluation.{u + 1, u, u + 1}
            (J := c.Z.smallEtaleTopology) n).obj K))).1
        simp only [Category.assoc, Iso.inv_hom_id_app]
        exact (RO.property.2.1 n K).symm) M
    have hh : IsIso ((P.val.openEvaluation n).inv.app (CX.ordinary.inverse.obj M) ≫
        (coefficientEvaluation.{u + 1, u, u + 1}
          (J := Scheme.ProEt.topology c.Z) n).map (τ.app M) ≫
        (CZ.ordinary.inverseEvaluation n).hom.app (S.val.openExtension.obj M)) := by
      rw [hc]
      infer_instance
    have : IsIso ((coefficientEvaluation.{u + 1, u, u + 1}
        (J := Scheme.ProEt.topology c.Z) n).map (τ.app M) ≫
        (CZ.ordinary.inverseEvaluation n).hom.app (S.val.openExtension.obj M)) :=
      (isIso_comp_left_iff _ _).mp hh
    exact (isIso_comp_right_iff _ _).mp this
  have : IsIso τ := NatIso.isIso_of_isIso_app τ
  obtain ⟨eD, heD⟩ := derivedSquare_exists S.val.openExtension CX.ordinary.inverse
    CZ.ordinary.inverse P.val.openExtension S.derivedOpen CX.image.system.inverse
    CZ.image.system.inverse P.val.derivedOpen S.val.openFactors
    CX.image.system.inverseFactors CZ.image.system.inverseFactors P.val.openFactors
    (asIso τ).symm
  have hlev (n : ℕ) := derivedSquare_exists (S.val.levelOpen n) (CX.ordinary.lift n).modules
    (CZ.ordinary.lift n).modules (P.val.levelOpen n) (S.levelDerivedOpen n)
    (CX.image.level n).inverse (CZ.image.level n).inverse (P.val.levelDerivedOpen n)
    (S.val.levelOpenFactors n) (CX.image.level n).inverseFactors
    (CZ.image.level n).inverseFactors (P.val.levelOpenFactors n) (asIso (τn n)).symm
  choose eDn heDn using hlev
  have hmD : (mateEquiv S.derivedOpenAdjunction P.val.derivedOpenAdjunction
      (.mk _ _ _ _ eD.inv)) = RO.square.inv := by
    apply localizeMate S.val.openAdjunction P.val.openAdjunction
      S.derivedOpenAdjunction P.val.derivedOpenAdjunction
      S.val.openFactors S.openDerived.system.inverseFactors
      P.val.openFactors P.val.openDerived.system.inverseFactors
      CX.image.system.inverseFactors CZ.image.system.inverseFactors
      S.property.2.2.1 P.property.2.2.1 τ (.mk _ _ _ _ RO.ordinary.inv)
      ((mateEquiv S.val.openAdjunction P.val.openAdjunction).apply_symm_apply _)
    · exact derivedSquare_symm_rep S.val.openExtension CX.ordinary.inverse CZ.ordinary.inverse
        P.val.openExtension S.derivedOpen CX.image.system.inverse CZ.image.system.inverse
        P.val.derivedOpen S.val.openFactors CX.image.system.inverseFactors
        CZ.image.system.inverseFactors P.val.openFactors (asIso τ).symm eD heD
    · exact derivedSquare_symm_rep CZ.ordinary.inverse S.openImage.inverse
        P.val.openImage.inverse CX.ordinary.inverse CZ.image.system.inverse
        S.openDerived.system.inverse P.val.openDerived.system.inverse CX.image.system.inverse
        CZ.image.system.inverseFactors S.openDerived.system.inverseFactors
        P.val.openDerived.system.inverseFactors CX.image.system.inverseFactors
        RO.ordinary RO.square RO.property.2.2.2.2
  have hmDn (n : ℕ) :
      (mateEquiv (S.levelDerivedOpenAdjunction n) (P.val.levelDerivedOpenAdjunction n)
        (.mk _ _ _ _ (eDn n).inv)) = (RO.derivedLevel n).inv := by
    apply localizeMate (S.val.levelOpenAdjunction n) (P.val.levelOpenAdjunction n)
      (S.levelDerivedOpenAdjunction n) (P.val.levelDerivedOpenAdjunction n)
      (S.val.levelOpenFactors n) (S.openDerived.level n).inverseFactors
      (P.val.levelOpenFactors n) (P.val.openDerived.level n).inverseFactors
      (CX.image.level n).inverseFactors (CZ.image.level n).inverseFactors
      (S.property.2.2.2.1 n) (P.property.2.2.2.1 n) (τn n)
      (.mk _ _ _ _ (RO.level n).inv)
      ((mateEquiv (S.val.levelOpenAdjunction n) (P.val.levelOpenAdjunction n)).apply_symm_apply _)
    · exact derivedSquare_symm_rep (S.val.levelOpen n) (CX.ordinary.lift n).modules
        (CZ.ordinary.lift n).modules (P.val.levelOpen n) (S.levelDerivedOpen n)
        (CX.image.level n).inverse (CZ.image.level n).inverse (P.val.levelDerivedOpen n)
        (S.val.levelOpenFactors n) (CX.image.level n).inverseFactors
        (CZ.image.level n).inverseFactors (P.val.levelOpenFactors n)
        (asIso (τn n)).symm (eDn n) (heDn n)
    · exact derivedSquare_symm_rep (CZ.ordinary.lift n).modules (S.openImage.lift n).modules
        (P.val.openImage.lift n).modules (CX.ordinary.lift n).modules
        (CZ.image.level n).inverse (S.openDerived.level n).inverse
        (P.val.openDerived.level n).inverse (CX.image.level n).inverse
        (CZ.image.level n).inverseFactors (S.openDerived.level n).inverseFactors
        (P.val.openDerived.level n).inverseFactors (CX.image.level n).inverseFactors
        (RO.level n) (RO.derivedLevel n) (RO.property.2.2.1 n)
  let α := (mateEquiv S.derivedOpenAdjunction P.val.derivedOpenAdjunction).symm
    (.mk _ _ _ _ RO.square.inv)
  let αn (n : ℕ) := (mateEquiv (S.levelDerivedOpenAdjunction n)
    (P.val.levelDerivedOpenAdjunction n)).symm (.mk _ _ _ _ (RO.derivedLevel n).inv)
  have hα : α = eD.inv := by
    exact (mateEquiv S.derivedOpenAdjunction P.val.derivedOpenAdjunction).symm_apply_eq.mpr
      hmD.symm
  have hαn (n : ℕ) : (αn n) = (eDn n).inv := by
    exact (mateEquiv (S.levelDerivedOpenAdjunction n)
      (P.val.levelDerivedOpenAdjunction n)).symm_apply_eq.mpr (hmDn n).symm
  have : IsIso α := by rw [hα]; infer_instance
  have (n : ℕ) : IsIso (αn n) := by rw [hαn]; infer_instance
  let e := (asIso α).symm
  let en (n : ℕ) := (asIso (αn n)).symm
  let record : ExceptionalSystemCompactificationComparisonData S CX CY CZ P :=
    { properSquare := RP
      openSquare := RO
      openComparison := e
      levelOpenComparison := en }
  refine ⟨⟨record, ?_, ?_, ?_⟩⟩
  · exact 
      ((mateEquiv S.derivedOpenAdjunction P.val.derivedOpenAdjunction).apply_symm_apply _)
  · intro n
    exact
      ((mateEquiv (S.levelDerivedOpenAdjunction n)
        (P.val.levelDerivedOpenAdjunction n)).apply_symm_apply _)
  · intro n M
    have hc := inverseMate_cube S.derivedOpenAdjunction P.val.derivedOpenAdjunction
      (S.levelDerivedOpenAdjunction n) (P.val.levelDerivedOpenAdjunction n)
      (CX.image.inverseEvaluation n) (CZ.image.inverseEvaluation n)
      (S.openDerivedEvaluation n) (P.val.openDerivedEvaluation n) α (αn n) (by
        intro K
        simp only [α, αn, Equiv.apply_symm_apply, etaleOpenEvaluationMate,
          proOpenEvaluationMate]
        apply (cancel_epi ((CX.proEvaluation.evaluation n).map
          (RO.square.hom.app K))).1
        simp only [← Functor.map_comp_assoc, Iso.hom_inv_id_app]
        apply (cancel_mono ((RO.derivedLevel n).hom.app ((S.PZ.evaluation n).obj K))).1
        simp only [Category.assoc, Iso.inv_hom_id_app]
        erw [(CX.proEvaluation.evaluation n).map_id, Category.id_comp, Category.comp_id]
        exact (RO.property.2.2.2.1 n K).symm) M
    have hh := inverseSquare_eq
      ((CZ.proEvaluation.evaluation n).map (α.app M))
      ((αn n).app ((S.PX.evaluation n).obj M))
      ((P.val.openDerivedEvaluation n).app (CX.image.system.inverse.obj M)).symm
      ((CZ.image.level n).inverse.mapIso ((S.openDerivedEvaluation n).app M)).symm
      ((P.val.levelDerivedOpen n).map ((CX.image.inverseEvaluation n).hom.app M))
      ((CZ.image.inverseEvaluation n).hom.app (S.derivedOpen.obj M)) hc
    simpa only [record, e, en, Iso.symm_hom, Iso.symm_inv, asIso_inv,
      NatIso.isIso_inv_app, Functor.mapIso_hom, Iso.app_hom, Functor.map_inv,
      Category.assoc] using hh

end AlgebraicGeometry
