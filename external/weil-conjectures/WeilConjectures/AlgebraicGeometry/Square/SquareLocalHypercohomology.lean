/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Derived.DerivedSquareLocalClassModels
public import WeilConjectures.AlgebraicGeometry.Derived.DerivedSquareUnitMap
public import WeilConjectures.AlgebraicGeometry.ModuleCohomologyFMap
import WeilConjectures.AlgebraicGeometry.Square.SquareInjectiveRoofAction
import WeilConjectures.AlgebraicGeometry.Restricted.RestrictedCoefficientRoof
import all WeilConjectures.AlgebraicGeometry.ModuleCohomologyFMap
import all WeilConjectures.AlgebraicGeometry.Unbounded.UnboundedDirectImageSectionPresheaf

/-! # Local hypercohomology of a normalized coefficient square

Source: Stacks Project, Cohomology, Tags 01E4, 01FB, 0BKJ and 0D5X.
(blueprint: lem-weil-pbc-square-local-hypercohomology).
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048
universe u w
open CategoryTheory CategoryTheory.Limits Opposite
noncomputable section
namespace AlgebraicGeometry
open Scheme.Modules
/-- The standard injective replacement and augmentation lift, with the two endpoint
resolutions fixed in advance. -/
private theorem coefficient_roof_exists {X Z : Scheme.{u}} (v : Z ⟶ X)
    (F : X.Modules) (G : Z.Modules) (φ : F ⟶ (pushforward v).obj G)
    (I : InjectiveResolution F) (J : InjectiveResolution G) :
    ∃ (L : CochainComplex X.Modules ℕ)
      (ell : ((pushforward v).mapHomologicalComplex (ComplexShape.up ℕ)).obj J.cocomplex ⟶ L)
      (beta : I.cocomplex ⟶ L),
      (∀ n : ℕ, Injective (L.X n)) ∧ QuasiIso ell ∧
      I.ι.f 0 ≫ beta.f 0 = φ ≫ (pushforward v).map (J.ι.f 0) ≫ ell.f 0 := by
  obtain ⟨L, ell, hL, hell⟩ := nat_complex_injective_resolution
    (((pushforward v).mapHomologicalComplex (ComplexShape.up ℕ)).obj J.cocomplex)
  let gamma := φ ≫ (pushforward v).map (J.ι.f 0) ≫ ell.f 0
  have hgamma : gamma ≫ L.d 0 1 = 0 := by
    dsimp only [gamma]
    rw [Category.assoc, Category.assoc, ell.comm]
    change φ ≫ (pushforward v).map (J.ι.f 0) ≫
      (pushforward v).map (J.cocomplex.d 0 1) ≫ ell.f 1 = 0
    rw [← Functor.map_comp_assoc, J.ι_f_zero_comp_complex_d, Functor.map_zero]
    simp
  obtain ⟨beta, hbeta⟩ := lift_to_nat_injectives I L hL gamma hgamma
  exact ⟨L, ell, beta, hL, hell, hbeta⟩

/-- Sections of the denominator of the roof are a quasi-isomorphism on every open.
The unbounded local-sections theorem supplies all opens at once. -/
private theorem coefficient_roof_sections_quasiIso {X Z : Scheme.{u}} (v : Z ⟶ X)
    {G : Z.Modules} (J : InjectiveResolution G)
    (L : CochainComplex X.Modules ℕ) (hL : ∀ n : ℕ, Injective (L.X n))
    (ell : ((pushforward v).mapHomologicalComplex (ComplexShape.up ℕ)).obj J.cocomplex ⟶ L)
    (hell : QuasiIso ell) (U : X.Opens) :
    QuasiIso (((RingedSpace.openModuleSections X.toRingedSpace U).mapHomologicalComplex
      (ComplexShape.up ℤ)).map
        ((J.cocomplex.mapExtendIso ComplexShape.embeddingUpNat (pushforward v)).hom ≫
          HomologicalComplex.extendMap ell ComplexShape.embeddingUpNat)) := by
  let : HasDerivedCategory (SheafOfModules.{u} (moduleRings X.toRingedSpace)) :=
    HasDerivedCategory.standard _
  let : QuasiIso ell := hell
  let : ∀ n : ℕ, Injective (L.X n) := hL
  let : J.cochainComplex.IsKInjective :=
    CochainComplex.isKInjective_of_injective J.cochainComplex 0
  let : CochainComplex.IsKInjective (L.extend ComplexShape.embeddingUpNat) :=
    CochainComplex.isKInjective_of_injective (L.extend ComplexShape.embeddingUpNat) 0
  let ellZ := (J.cocomplex.mapExtendIso ComplexShape.embeddingUpNat (pushforward v)).hom ≫
    HomologicalComplex.extendMap ell ComplexShape.embeddingUpNat
  have hZ : QuasiIso ellZ := by dsimp only [ellZ]; infer_instance
  let := hZ
  have hP := RingedSpace.localSections_directImage_resolution_quasiIso
    v.toLRSHom.toShHom J.cochainComplex (L.extend ComplexShape.embeddingUpNat) ellZ
  let E := (CategoryTheory.evaluation X.Opensᵒᵖ AddCommGrpCat.{u}).obj (op U)
  let := hP
  have hE : QuasiIso ((E.mapHomologicalComplex (ComplexShape.up ℤ)).map
      (((RingedSpace.localAbelianSections X.toRingedSpace).mapHomologicalComplex
        (ComplexShape.up ℤ)).map ellZ)) := by infer_instance
  exact hE

private theorem cancel_roof {C : Type*} [Category C]
    {A B D E L : C} (a : A ≅ B) (b : D ≅ E)
    (p : B ⟶ E) (m : A ⟶ D) (ell : D ⟶ L) (beta : B ⟶ L)
    [IsIso ell] (hp : p ≫ b.inv ≫ ell = beta)
    (hm : m ≫ ell = a.hom ≫ beta) :
    a.hom ≫ p = m ≫ b.hom := by
  apply (cancel_mono b.inv).mp
  apply (cancel_mono ell).mp
  simpa only [Category.assoc, Iso.hom_inv_id_assoc] using
    (congrArg (fun z ↦ a.hom ≫ z) hp).trans hm.symm

variable [∀ Y : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]

/-- Local hypercohomology of a normalized coefficient square.
Source: Stacks Project, Cohomology, Tags 01E4, 01FB, 0BKJ and 0D5X
(blueprint: lem-weil-pbc-square-local-hypercohomology).

Proof: Factor each endpoint comparison into the classical-to-section comparison and the
raw injective local comparison. Choose an injective replacement ell of v_*J, then extend the
coefficient augmentation to beta:I -> L. The already proved local direct-image sections
theorem and exact evaluation show that sections of ell are a quasi-isomorphism on U.
The derived injective-roof action and the restricted coefficient-roof equation have the
same numerator H(Gamma(U,beta)) and denominator H(Gamma(U,ell)). Postcompose by the inverse
raw target comparison and this invertible denominator, use both equations, and cancel.
The original endpoint factorizations give the required equality before sheafification. -/
theorem square_localHypercohomology {X S Z T : Scheme.{u}}
    (f : X ⟶ S) (k : Z ⟶ T) (g : T ⟶ S) (v : Z ⟶ X) (h : v ≫ f = k ≫ g)
    (F : X.Modules) (G : Z.Modules) (φ : F ⟶ (pushforward v).obj G) (q : ℕ)
    (V : S.Opens) (I : InjectiveResolution F) (J : InjectiveResolution G)
    (R : RestrictedResolutionSections I (f ⁻¹ᵁ V))
    (R' : RestrictedResolutionSections J (v ⁻¹ᵁ (f ⁻¹ᵁ V))) :
    (squareLocalResolutionComparison f F q V I (f ⁻¹ᵁ V) rfl R).hom ≫
      ((RingedSpace.localHypercohomologyPresheaf S.toRingedSpace (q : ℤ)).map
        (derivedSquareUnitMap f k g v h F G φ)).app (op V) ≫
      (RingedSpace.topEdgeLocalLeray g.toLRSHom.toShHom (q : ℤ)
        ((schemeDerivedDirectImage k).obj ((DerivedCategory.singleFunctor
          (SheafOfModules.{u} (moduleRings Z.toRingedSpace)) 0).obj G))).hom.app (op V) ≫
      (squareInverseOpenComparison g (q : ℤ)
        ((schemeDerivedDirectImage k).obj ((DerivedCategory.singleFunctor
          (SheafOfModules.{u} (moduleRings Z.toRingedSpace)) 0).obj G))).hom.app (op V) =
    moduleCohomologyFMap (v.resLE (f ⁻¹ᵁ V) (v ⁻¹ᵁ (f ⁻¹ᵁ V)) le_rfl)
      (restrictedDirectImageMap v φ (f ⁻¹ᵁ V)) q ≫
      (squareLocalResolutionComparison k G q (g ⁻¹ᵁ V) J (v ⁻¹ᵁ (f ⁻¹ᵁ V)) (by
        rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, h]) R').hom := by
  obtain ⟨L, ell, beta, hL, hell, hbeta⟩ := coefficient_roof_exists v F G φ I J
  let U := f ⁻¹ᵁ V
  let U' := v ⁻¹ᵁ U
  have hU' : U' = k ⁻¹ᵁ (g ⁻¹ᵁ V) := by
    dsimp only [U', U]
    rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, h]
  let Γ := (RingedSpace.openModuleSections X.toRingedSpace U).mapHomologicalComplex
    (ComplexShape.up ℤ)
  let H := HomologicalComplex.homologyFunctor AddCommGrpCat.{u}
    (ComplexShape.up ℤ) (q : ℤ)
  let ellZ := (J.cocomplex.mapExtendIso ComplexShape.embeddingUpNat (pushforward v)).hom ≫
    HomologicalComplex.extendMap ell ComplexShape.embeddingUpNat
  let betaZ := HomologicalComplex.extendMap beta ComplexShape.embeddingUpNat
  let ellH := H.map (Γ.map ellZ)
  have hΓ : QuasiIso (Γ.map ellZ) := coefficient_roof_sections_quasiIso v J L hL ell hell U
  let := hΓ
  have hEll : IsIso ellH := by
    change IsIso (HomologicalComplex.homologyMap (Γ.map ellZ) (q : ℤ))
    infer_instance
  let := hEll
  have hderived := square_injectiveRoof_action f k g v h F G φ I J L hL
    ell hell beta hbeta q V
  have hclassical := restrictedCoefficient_roof v F G φ I J L hL
    ell hell beta hbeta U R R' q
  rw [squareLocalResolutionComparison_factor f F q V I U rfl R,
    squareLocalResolutionComparison_factor k G q (g ⁻¹ᵁ V) J U' hU' R']
  simp only [Category.assoc]
  simpa only [Category.assoc] using cancel_roof
    (squareResolutionCohomologyIso I U R q)
    (squareInjectiveLocalComparison k G q (g ⁻¹ᵁ V) J U' hU')
    ((squareInjectiveLocalComparison f F q V I U rfl).hom ≫
      ((RingedSpace.localHypercohomologyPresheaf S.toRingedSpace (q : ℤ)).map
        (derivedSquareUnitMap f k g v h F G φ)).app (op V) ≫
      (RingedSpace.topEdgeLocalLeray g.toLRSHom.toShHom (q : ℤ)
        ((schemeDerivedDirectImage k).obj ((DerivedCategory.singleFunctor
          (SheafOfModules.{u} (moduleRings Z.toRingedSpace)) 0).obj G))).hom.app (op V) ≫
      (squareInverseOpenComparison g (q : ℤ)
        ((schemeDerivedDirectImage k).obj ((DerivedCategory.singleFunctor
          (SheafOfModules.{u} (moduleRings Z.toRingedSpace)) 0).obj G))).hom.app (op V))
    (moduleCohomologyFMap (v.resLE U U' le_rfl) (restrictedDirectImageMap v φ U) q ≫
      (squareResolutionCohomologyIso J U' R' q).hom)
    ellH (H.map (Γ.map betaZ)) (by simpa only [Category.assoc] using hderived)
    (by simpa only [Category.assoc] using hclassical)

end AlgebraicGeometry
