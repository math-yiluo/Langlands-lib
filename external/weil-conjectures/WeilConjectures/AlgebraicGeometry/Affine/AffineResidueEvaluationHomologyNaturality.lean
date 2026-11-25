/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.AffineResidueCycleHomology
public import Mathlib.CategoryTheory.Adjunction.Additive
public import Mathlib.AlgebraicGeometry.ResidueField
import WeilConjectures.AlgebraicGeometry.Affine.AffineResidueQuotientHomologyNaturality
import WeilConjectures.AlgebraicGeometry.AffineResidueScalarTransport
public import WeilConjectures.AlgebraicGeometry.DerivedHomMayerVietoris

/-! # Natural residue homology after transport to the scheme residue field

Source: Stacks Project, Tags 0098 and 010V.
(blueprint: new-affine-residue-evaluation-homology-naturality)
-/

@[expose] public section
set_option autoImplicit false
universe v
open CategoryTheory
namespace AlgebraicGeometry.Scheme
noncomputable section

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private def restrictionHomologyIso
    {A B : Type v} [CommRing A] [CommRing B] (f : A →+* B) (i : ℤ) :
    HomologicalComplex.homologyFunctor (ModuleCat.{v} B) (.up ℤ) i ⋙
      ModuleCat.restrictScalars f ≅
    (ModuleCat.restrictScalars f).mapHomologicalComplex (.up ℤ) ⋙
      HomologicalComplex.homologyFunctor (ModuleCat.{v} A) (.up ℤ) i :=
  NatIso.ofComponents (fun K ↦ ((K.sc i).mapHomologyIso (ModuleCat.restrictScalars f)).symm)
    (fun g ↦ ShortComplex.mapHomologyIso_inv_naturality
      ((HomologicalComplex.shortComplexFunctor _ _ i).map g) (ModuleCat.restrictScalars f))

-- Scalar extension, residue restriction and quotient carriers use different module structures.
set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- The affine cycle quotient agrees naturally with homology after residue evaluation.
Source: Stacks Project, Tags 0098 and 010V.
(blueprint: new-affine-residue-evaluation-homology-naturality)

Proof: The kernel hypothesis identifies p with the point of the canonical affine
chart. Its prime residue field and the scheme residue field are canonically
isomorphic. The natural scalar-transport comparison identifies extension to the
prime residue field followed by restriction along that isomorphism with extension
by section evaluation. Restriction preserves homology. Compose its natural
homology comparison, the natural scalar-transport comparison of complexes, and
the quotient-to-homology comparison. Naturality of these factors gives the
equation for every complex map. Perfectness is not required. -/
theorem affine_residue_evaluation_homology_naturality
    (W : Scheme.{v}) (w : W) (U : W.Opens) (hwU : w ∈ U) (hU : IsAffineOpen U)
    (p : Ideal Γ(W, U)) [p.IsPrime]
    (hp : p = RingHom.ker (W.evaluation U w hwU).hom) :
    let F : SheafOfModules.{v} ((moduleRings W.toRingedSpace).over U) ⥤
        ModuleCat.{v} Γ(W, U) := SheafOfModules.evaluation _ (.op (Over.mk (𝟙 U)))
    letI : F.Additive := inferInstanceAs
      ((SheafOfModules.forget _ ⋙ PresheafOfModules.evaluation _ _).Additive)
    let T := ModuleCat.extendScalars.{v, v, v} (W.evaluation U w hwU).hom
    letI : T.Additive := (ModuleCat.extendRestrictScalarsAdj _).left_adjoint_additive
    let G := (F ⋙ T).mapHomologicalComplex (.up ℤ)
    ∃ e : ∀ K, affineResidueCycleHomology W U p K ≃+ (G.obj K).homology 1,
      ∀ K C (φ : K ⟶ C) z,
        e C (affineResidueCycleHomologyMap φ z) =
          HomologicalComplex.homologyMap (G.map φ) 1 (e K z) := by
  classical
  dsimp only
  have hp' : p = (hU.isoSpec.hom ⟨w, hwU⟩).asIdeal := by
    rw [hp, hU.isoSpec_hom_apply]
    ext a
    change W.evaluation U w hwU a = 0 ↔
      W.presheaf.germ U w hwU a ∈ IsLocalRing.maximalIdeal _
    exact IsLocalRing.residue_eq_zero_iff _
  clear hp
  subst p
  let F : SheafOfModules.{v} ((moduleRings W.toRingedSpace).over U) ⥤
      ModuleCat.{v} Γ(W, U) := SheafOfModules.evaluation _ (.op (Over.mk (𝟙 U)))
  have : F.Additive := inferInstanceAs
    ((SheafOfModules.forget _ ⋙ PresheafOfModules.evaluation _ _).Additive)
  have : (hU.isoSpec.hom ⟨w, hwU⟩).asIdeal.IsPrime := by
    set_option backward.isDefEq.respectTransparency false in infer_instance
  let κ := (hU.isoSpec.hom ⟨w, hwU⟩).asIdeal.ResidueField
  have : IsIso (U.ι.residueFieldMap ⟨w, hwU⟩) := by
    set_option backward.isDefEq.respectTransparency false in infer_instance
  have : IsIso (hU.isoSpec.hom.residueFieldMap ⟨w, hwU⟩) := by
    set_option backward.isDefEq.respectTransparency false in infer_instance
  let e := asIso (U.ι.residueFieldMap ⟨w, hwU⟩) ≪≫
    (asIso (hU.isoSpec.hom.residueFieldMap ⟨w, hwU⟩)).symm ≪≫
      Spec.residueFieldIso Γ(W, U) (hU.isoSpec.hom ⟨w, hwU⟩)
  let S := ModuleCat.extendScalars.{v, v, v} (algebraMap Γ(W, U) κ)
  have : S.Additive := (ModuleCat.extendRestrictScalarsAdj _).left_adjoint_additive
  let R := ModuleCat.restrictScalars.{v, v, v} e.hom.hom
  let T := ModuleCat.extendScalars.{v, v, v} (W.evaluation U w hwU).hom
  have : T.Additive := (ModuleCat.extendRestrictScalarsAdj _).left_adjoint_additive
  let Gp := (F ⋙ S).mapHomologicalComplex (.up ℤ)
  let G := (F ⋙ T).mapHomologicalComplex (.up ℤ)
  let δ : S ⋙ R ≅ T := Classical.choice
    (affine_residue_scalar_transport W U hU ⟨w, hwU⟩)
  let σ : Gp ⋙ R.mapHomologicalComplex (.up ℤ) ≅ G := by
    set_option backward.isDefEq.respectTransparency false in
    set_option backward.isDefEq.respectTransparency.types false in
      exact Functor.mapHomologicalComplexCompIso
        (Functor.associator F S R ≪≫ Functor.isoWhiskerLeft F δ) (.up ℤ)
  let γ : Gp ⋙ HomologicalComplex.homologyFunctor (ModuleCat.{v} κ) (.up ℤ) 1 ⋙ R ≅
      G ⋙ HomologicalComplex.homologyFunctor
        (ModuleCat.{v} (W.residueField w)) (.up ℤ) 1 :=
    Functor.isoWhiskerLeft Gp (restrictionHomologyIso e.hom.hom 1) ≪≫
      Functor.isoWhiskerRight σ
        (HomologicalComplex.homologyFunctor (ModuleCat.{v} (W.residueField w)) (.up ℤ) 1)
  let q := Classical.choose (affine_residue_quotient_homology_naturality
    W U (hU.isoSpec.hom ⟨w, hwU⟩).asIdeal)
  have hq := Classical.choose_spec (affine_residue_quotient_homology_naturality
    W U (hU.isoSpec.hom ⟨w, hwU⟩).asIdeal)
  exact ⟨fun K ↦ (q K).trans (γ.app K).toLinearEquiv.toAddEquiv, fun K C φ z ↦
    (congrArg (γ.app C).hom (hq K C φ z)).trans
      (ConcreteCategory.congr_hom (γ.hom.naturality φ) (q K z))⟩

end
end AlgebraicGeometry.Scheme
