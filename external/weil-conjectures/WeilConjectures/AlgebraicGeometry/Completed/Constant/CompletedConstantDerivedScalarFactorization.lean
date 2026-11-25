/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Constant.ConstantAdicFiniteDiagramData
public import WeilConjectures.AlgebraicGeometry.Completed.Constant.CompletedConstantRealizationDataSupplement
import all WeilConjectures.AlgebraicGeometry.Completed.Constant.CompletedConstantModuleModel
import all WeilConjectures.AlgebraicGeometry.Relative.RelativeCompletedModuleRealizationExact
import all WeilConjectures.AlgebraicGeometry.WeilSheaf.ProfiniteCoefficientInverseImageSupplement
import all WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleOperationsSupplement
import all WeilConjectures.AlgebraicGeometry.Adic.AdicLisseRelativeRestriction
import all WeilConjectures.AlgebraicGeometry.Pbc.PbcFinitePullbackConstructibility
import WeilConjectures.AlgebraicGeometry.Relative.RelativeFiniteCoefficientTransport

/-! # Scalar factorization of the relative completed constant realization

Source: Stacks Tags 06YY, 06YU and 0D6D; flat completion (Tag 093M).
(blueprint: lem-weil-pbc-completed-constant-derived-scalar-factorization).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option linter.style.haveILetI false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme

private theorem scalarExtensionExact (X : Scheme.{u})
    {A : Type (u + 1)} [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    (φ : adicLisseConstantRing X (AdicCompletion I A) ⟶ adicLisseCompletedRing X I)
    (hφ : ∀ n : ℕ, φ ≫ limit.π (adicLisseRingSystem X I) (op n) =
      (constantSheaf (ProEt.topology X) CommRingCat.{u + 1}).map
        (CommRingCat.ofHom (AdicCompletion.evalₐ I (n + 1)).toRingHom)) :
    PreservesFiniteLimits (pbcExtend φ) ∧
      PreservesFiniteColimits (pbcExtend φ) := by
  let := AdicCompletion.isNoetherianRing I
  let J := I.map (algebraMap A (AdicCompletion I A))
  let e : adicLisseCompletedRing X J ≅ adicLisseCompletedRing X I :=
    lim.mapIso (completion_tower_iso X I)
  have hc (n : ℕ) : φ ≫ e.inv ≫ limit.π (adicLisseRingSystem X J) (op n) =
      (constantSheaf (ProEt.topology X) CommRingCat.{u + 1}).map
        (CommRingCat.ofHom (Ideal.Quotient.mk (J ^ (n + 1)))) := by
    let q : adicLisseConstantRing X ((AdicCompletion I A) ⧸ J ^ (n + 1)) ≅
        adicLisseConstantRing X (A ⧸ I ^ (n + 1)) :=
      (constantSheaf (ProEt.topology X) CommRingCat.{u + 1}).mapIso
        (completion_quotient_iso I (n + 1))
    apply (cancel_mono q.hom).1
    change (φ ≫ e.inv ≫ limit.π (adicLisseRingSystem X J) (op n)) ≫
        (constantSheaf (ProEt.topology X) CommRingCat.{u + 1}).map
          (completion_quotient_iso I (n + 1)).hom =
      (constantSheaf (ProEt.topology X) CommRingCat.{u + 1}).map
        (CommRingCat.ofHom (Ideal.Quotient.mk (J ^ (n + 1)))) ≫
      (constantSheaf (ProEt.topology X) CommRingCat.{u + 1}).map
        (completion_quotient_iso I (n + 1)).hom
    have he : e.inv ≫ limit.π (adicLisseRingSystem X J) (op n) ≫
        (constantSheaf (ProEt.topology X) CommRingCat.{u + 1}).map
          (completion_quotient_iso I (n + 1)).hom =
        limit.π (adicLisseRingSystem X I) (op n) := by
      change e.inv ≫ limit.π (adicLisseRingSystem X J) (op n) ≫
        (completion_tower_iso X I).hom.app (op n) = _
      rw [← limMap_π]
      change e.inv ≫ e.hom ≫ _ = _
      rw [← Category.assoc, e.inv_hom_id, Category.id_comp]
    simp only [Category.assoc]
    rw [he, hφ, ← Functor.map_comp, completion_quotient_iso_mk]
  have he := (completed_constant_algebra_flat_quotients X J _ e φ hc).2.1
  exact he

private def exactExtensionDerived {X : Scheme.{u}}
    {R S : Sheaf (ProEt.topology X) CommRingCat.{u + 1}} (φ : R ⟶ S)
    [PreservesFiniteLimits (pbcExtend φ)] [PreservesFiniteColimits (pbcExtend φ)] :
    pbcDerivedExtend φ ≅ (pbcExtend φ).mapDerivedCategory := by
  let L := pbcExtend φ
  let D := pbcDerivedExtend φ
  let ε := pbcExtensionCounit φ
  have : D.IsLeftDerivedFunctor ε
      (HomotopyCategory.quasiIso _ (.up ℤ)) := pbcDerivedExtension_universal φ
  have : L.mapDerivedCategory.IsLeftDerivedFunctor L.mapDerivedCategoryFactorsh.hom
      (HomotopyCategory.quasiIso _ (.up ℤ)) :=
    Functor.isLeftDerivedFunctor_of_inverts _ _ L.mapDerivedCategoryFactorsh
  exact Functor.leftDerivedUnique L.mapDerivedCategory D ε
    L.mapDerivedCategoryFactorsh.hom (HomotopyCategory.quasiIso _ (.up ℤ))

private theorem completedComparison_eval (X : Scheme.{u})
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A) (n : ℕ) :
    limit.lift (pbcAdicRings X d) (constantAdicFiniteCone X d) ≫
        (pbcCompletedComparison X d).inv ≫
        limit.π (adicLisseRingSystem X d.ideal) (op n) =
      (constantSheaf (ProEt.topology X) CommRingCat.{u + 1}).map
        (CommRingCat.ofHom (AdicCompletion.evalₐ d.ideal (n + 1)).toRingHom) := by
  simp only [pbcCompletedComparison, HasLimit.isoOfNatIso_inv_π,
    limit.lift_π_assoc, constantAdicFiniteCone, NatTrans.comp_app,
    Category.assoc, Iso.hom_inv_id_app, Category.comp_id]
  rfl

private noncomputable def coefficientExtensionIso {X : Scheme.{u}}
    {R S R' S' : Sheaf (ProEt.topology X) CommRingCat.{u + 1}}
    (eR : R ≅ R') (eS : S ≅ S') (f : R ⟶ S) (f' : R' ⟶ S')
    (hsq : f ≫ eS.hom = eR.hom ≫ f') :
    pbcDerivedRestrict eR.hom ⋙ pbcDerivedExtend f ≅
      pbcDerivedExtend f' ⋙ pbcDerivedRestrict eS.hom := by
  let ER₀ := proEtaleScalarEquivalence X ((adicLisseForget X).mapIso eR)
  let ES₀ := proEtaleScalarEquivalence X ((adicLisseForget X).mapIso eS)
  have : ER₀.functor.Additive := inferInstanceAs (pbcRestrict eR.hom).Additive
  have : ER₀.inverse.Additive := inferInstanceAs (pbcRestrict eR.inv).Additive
  have : ES₀.functor.Additive := inferInstanceAs (pbcRestrict eS.hom).Additive
  have : ES₀.inverse.Additive := inferInstanceAs (pbcRestrict eS.inv).Additive
  let ER := ER₀.mapDerivedCategory
  let ES := ES₀.mapDerivedCategory
  have hi : eR.inv ≫ f = f' ≫ eS.inv := by
    simpa only [Category.assoc, Iso.hom_inv_id, Category.comp_id,
      Iso.inv_hom_id_assoc] using congrArg (fun k ↦ eR.inv ≫ k ≫ eS.inv) hsq
  let r : pbcDerivedRestrict f ⋙ pbcDerivedRestrict eR.inv ≅
      pbcDerivedRestrict eS.inv ⋙ pbcDerivedRestrict f' :=
    pbcDerivedRestrictComp eR.inv f (f' ≫ eS.inv) hi ≪≫
      (pbcDerivedRestrictComp f' eS.inv (f' ≫ eS.inv) rfl).symm
  let a : pbcDerivedRestrict eR.hom ⋙ pbcDerivedExtend f ⊣
      pbcDerivedRestrict f ⋙ pbcDerivedRestrict eR.inv :=
    ER.toAdjunction.comp (pbcDerivedScalarAdjunction f)
  let b : pbcDerivedExtend f' ⋙ pbcDerivedRestrict eS.hom ⊣
      pbcDerivedRestrict eS.inv ⋙ pbcDerivedRestrict f' :=
    (pbcDerivedScalarAdjunction f').comp ES.toAdjunction
  exact (a.ofNatIsoRight r).leftAdjointUniq b

private def constantModulePullback {X Y : Scheme.{u}} (g : Y ⟶ X)
    (B : Type (u + 1)) [CommRing B] :
    adicLisseConstantModules X B ⋙
        proEtaleRingModulePullback g (adicLisseConstantRing X B)
          ((adicTowerInverseImage g).obj (adicLisseConstantRing X B)) (Iso.refl _) ≅
      adicLisseConstantModules Y B ⋙
        pbcRestrict (proEtaleConstantInverseImageMap g CommRingCat.{u + 1}
          (CommRingCat.of B)) := by
  let e := (proEtaleRingModulePullbackAdjunction g (adicLisseConstantRing X B)
    _ (Iso.refl _)).leftAdjointUniq
      (proEtaleModuleInverseImageAdjunction g (adicLisseConstantRing X B))
  simpa only [constantCoefficients, asIso_hom] using
    Functor.isoWhiskerLeft (adicLisseConstantModules X B) e ≪≫
      concreteConstantModuleComparison g B

private theorem inverseCompleted_isIso (X Y : Scheme.{u}) (g : Y ⟶ X)
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A)
    (β : (adicTowerInverseImage g).obj (adicLisseCompletedRing X d.ideal) ⟶
      adicLisseCompletedRing Y d.ideal)
    (hβ : ∀ n : ℕ, β ≫ limit.π (adicLisseRingSystem Y d.ideal) (op n) =
      (adicTowerInverseImage g).map (limit.π (adicLisseRingSystem X d.ideal) (op n)) ≫
        proEtaleConstantInverseImageMap g CommRingCat.{u + 1}
          (CommRingCat.of (A ⧸ d.ideal ^ (n + 1)))) : IsIso β := by
  obtain ⟨β₀, hβ₀iso, hβ₀⟩ := completedConstant_pullback_iso Y X g d.ideal d.quotientFinite
  have : β = β₀ := by
    apply limit.hom_ext
    intro n
    exact (hβ n.unop).trans (hβ₀ n.unop).symm
  simpa only [this] using hβ₀iso

private theorem coefficientSquare (X Y : Scheme.{u}) (g : Y ⟶ X)
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A)
    (φ : adicLisseConstantRing Y (AdicCompletion d.ideal A) ⟶
      adicLisseCompletedRing Y d.ideal)
    (hφ : ∀ n : ℕ, φ ≫ limit.π (adicLisseRingSystem Y d.ideal) (op n) =
      (constantSheaf (ProEt.topology Y) CommRingCat.{u + 1}).map
        (CommRingCat.ofHom (AdicCompletion.evalₐ d.ideal (n + 1)).toRingHom))
    (β : (adicTowerInverseImage g).obj (adicLisseCompletedRing X d.ideal) ⟶
      adicLisseCompletedRing Y d.ideal)
    (hβ : ∀ n : ℕ, β ≫ limit.π (adicLisseRingSystem Y d.ideal) (op n) =
      (adicTowerInverseImage g).map (limit.π (adicLisseRingSystem X d.ideal) (op n)) ≫
        proEtaleConstantInverseImageMap g CommRingCat.{u + 1}
          (CommRingCat.of (A ⧸ d.ideal ^ (n + 1)))) :
    (adicTowerInverseImage g).map
        (limit.lift (pbcAdicRings X d) (constantAdicFiniteCone X d)) ≫
        (adicTowerInverseImage g).map (pbcCompletedComparison X d).inv ≫ β =
      proEtaleConstantInverseImageMap g CommRingCat.{u + 1}
        (CommRingCat.of (AdicCompletion d.ideal A)) ≫ φ := by
  apply limit.hom_ext
  intro n
  simp only [Category.assoc, hβ n.unop, hφ n.unop]
  rw [← Functor.map_comp_assoc, ← Functor.map_comp_assoc]
  rw [Category.assoc, completedComparison_eval]
  exact proEtaleConstantInverseImageMap_naturality g
    (CommRingCat.ofHom (AdicCompletion.evalₐ d.ideal (n.unop + 1)).toRingHom)

/-- Relative completed constant realization factors through the single coefficient map
from the inverse image of the constant algebraic completion to completed coefficients.
This statement contains no quotient reductions or transition compatibility.

Source: Stacks Tags 06YY, 06YU and 0D6D; the scalar-extension computation in the first step
of lem-weil-pbc-completed-constant-unbounded-finite-diagram-comparison.
(blueprint: lem-weil-pbc-completed-constant-derived-scalar-factorization).

Proof: form the evaluation map from the constant completion on X to the limit of its
finite quotient sheaves. Its composite with the fixed constant-to-continuous ring
comparison is the limit lift of constantAdicFiniteCone. The evaluation equations for
phi and beta identify its inverse image with the map on Y, after transporting the
constant ring by the canonical constant-inverse-image isomorphism. The latter map
and beta are isomorphisms on the relevant coefficient presentations: for beta this
is profinite coefficient inverse image applied to the finite quotient rings.
The extended ideal in the algebraic completion has the same quotient rings as the
original ideal. Apply flatness of the completed constant algebra to this quotient
tower to prove that extension along phi preserves finite limits and colimits.
Its exact derived-category functor therefore computes its universal left derived
functor. Ordinary inverse image preserves constant module sheaves naturally in the
algebraic module. Derive this comparison using exact-functor composition. Restriction
along the two coefficient isomorphisms gives equivalences; the coefficient square
identifies the composite right adjoints, so uniqueness of left adjoints identifies
the corresponding derived scalar extensions. Combine this with restriction of
scalars along the composite coefficient isomorphism and exact-functor composition.
The resulting natural isomorphism applies to all unbounded complexes. -/
theorem completed_constant_derived_scalar_factorization
    (X Y : Scheme.{u}) (g : Y ⟶ X)
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A)
    (φ : adicLisseConstantRing Y (AdicCompletion d.ideal A) ⟶
      adicLisseCompletedRing Y d.ideal)
    (hφ : ∀ n : ℕ, φ ≫ limit.π (adicLisseRingSystem Y d.ideal) (op n) =
      (constantSheaf (ProEt.topology Y) CommRingCat.{u + 1}).map
        (CommRingCat.ofHom (AdicCompletion.evalₐ d.ideal (n + 1)).toRingHom))
    (β : (adicTowerInverseImage g).obj (adicLisseCompletedRing X d.ideal) ⟶
      adicLisseCompletedRing Y d.ideal)
    (hβ : ∀ n : ℕ, β ≫ limit.π (adicLisseRingSystem Y d.ideal) (op n) =
      (adicTowerInverseImage g).map (limit.π (adicLisseRingSystem X d.ideal) (op n)) ≫
        proEtaleConstantInverseImageMap g CommRingCat.{u + 1}
          (CommRingCat.of (A ⧸ d.ideal ^ (n + 1)))) :
    let c := completedConstantRealization Y d.ideal φ ⋙ pbcRestrict β ⋙
      pbcRestrict ((adicTowerInverseImage g).map (pbcCompletedComparison X d).inv)
    ∀ (hc : c.Additive) (hlim : PreservesFiniteLimits c)
      (hcolim : PreservesFiniteColimits c),
      letI := hc
      letI := hlim
      letI := hcolim
      Nonempty (c.mapDerivedCategory ≅ constantAdicFiniteRealization g d ⋙
        pbcDerivedExtend ((adicTowerInverseImage g).map
          (limit.lift (pbcAdicRings X d) (constantAdicFiniteCone X d)))) := by
  dsimp only
  intro hc hlim hcolim
  letI := hc
  letI := hlim
  letI := hcolim
  letI := d.noetherian
  let C := AdicCompletion d.ideal A
  letI := CompletedConstantReduction.constant_additive X C
  letI := CompletedConstantReduction.constant_additive Y C
  letI := (constantAdicFinite_constant_exact X C).1
  letI := (constantAdicFinite_constant_exact X C).2
  letI := (constantAdicFinite_constant_exact Y C).1
  letI := (constantAdicFinite_constant_exact Y C).2
  let F := adicLisseConstantModules Y C
  let E := pbcExtend φ
  have hE := scalarExtensionExact Y d.ideal φ hφ
  letI := hE.1
  letI := hE.2
  have hF := constantAdicFinite_constant_exact Y C
  letI := hF.1
  letI := hF.2
  have hFX := constantAdicFinite_constant_exact X C
  letI := hFX.1
  letI := hFX.2
  haveI := inverseCompleted_isIso X Y g d β hβ
  letI := relativeFiniteConstantInverseImage_isIso g C
  let κ : (adicTowerInverseImage g).obj (adicLisseConstantRing X C) ≅
      adicLisseConstantRing Y C :=
    asIso (proEtaleConstantInverseImageMap g CommRingCat.{u + 1} (CommRingCat.of C))
  let a := (adicTowerInverseImage g).map
    (limit.lift (pbcAdicRings X d) (constantAdicFiniteCone X d))
  let b : (adicTowerInverseImage g).obj (pbcAdicCompletion X d) ≅
      adicLisseCompletedRing Y d.ideal :=
    asIso ((adicTowerInverseImage g).map (pbcCompletedComparison X d).inv ≫ β)
  let t := coefficientExtensionIso κ b a φ
    (by
      dsimp [a, b, κ, C]
      exact coefficientSquare X Y g d φ hφ β hβ)
  let z := Functor.isoWhiskerLeft (F ⋙ E)
    (pbcRestrictComp ((adicTowerInverseImage g).map (pbcCompletedComparison X d).inv)
      β b.hom rfl)
  let k := Functor.mapDerivedCategoryCompIso
      (adicLisseConstantModules X C)
      (proEtaleRingModulePullback g (adicLisseConstantRing X C)
        ((adicTowerInverseImage g).obj (adicLisseConstantRing X C)) (Iso.refl _))
  let q := k ≪≫
    Functor.mapDerivedCategoryNatIso (constantModulePullback g C) ≪≫
      (Functor.mapDerivedCategoryCompIso F (pbcRestrict κ.hom)).symm
  refine ⟨Functor.mapDerivedCategoryNatIso z ≪≫
    (Functor.mapDerivedCategoryCompIso (F ⋙ E) (pbcRestrict b.hom)).symm ≪≫
    Functor.isoWhiskerRight (Functor.mapDerivedCategoryCompIso F E).symm
      (pbcDerivedRestrict b.hom) ≪≫
    Functor.associator F.mapDerivedCategory E.mapDerivedCategory
      (pbcDerivedRestrict b.hom) ≪≫
    Functor.isoWhiskerLeft F.mapDerivedCategory
      (Functor.isoWhiskerRight (exactExtensionDerived φ).symm
        (pbcDerivedRestrict b.hom)) ≪≫
    Functor.isoWhiskerLeft F.mapDerivedCategory t.symm ≪≫
    (Functor.associator F.mapDerivedCategory (pbcDerivedRestrict κ.hom)
      (pbcDerivedExtend a)).symm ≪≫
    Functor.isoWhiskerRight q.symm (pbcDerivedExtend a)⟩

end AlgebraicGeometry.Scheme
