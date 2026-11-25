/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.AdicCoefficientDatum.FourCornersSupplement
public import WeilConjectures.AlgebraicGeometry.WeilSheaf.ProfiniteCoefficientInverseImageSupplement
import all WeilConjectures.AlgebraicGeometry.Adic.AdicLisseRelativeRestriction
import all WeilConjectures.AlgebraicGeometry.Pbc.PbcFinitePullbackConstructibility
import all WeilConjectures.AlgebraicGeometry.Relative.RelativeCompletedModuleRealizationExact

/-! Local complexes under an isomorphism of base schemes.

## References

* Stacks Tags 09AI and 09BT
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme

section Transport

variable {T : Scheme.{u}}

/-- Restriction of scalars along the identity is the identity on sections. -/
def pbcRestrictId (R : Sheaf (ProEt.topology T) CommRingCat.{u + 1}) :
    pbcRestrict (𝟙 R) ≅ 𝟭 _ :=
  NatIso.ofComponents (fun M ↦ (SheafOfModules.fullyFaithfulForget _).preimageIso
      (PresheafOfModules.isoMk (fun U ↦ ModuleCat.restrictScalarsId'App
          ((𝟙 R : R ⟶ R).hom.app U).hom rfl (M.val.obj U))
        (fun {U V} f ↦ by ext x; rfl)))
    (fun f ↦ by ext U x; rfl)

/-- Derived restriction of scalars along a ring-sheaf isomorphism is an equivalence. -/
def pbcDerivedRestrictEquivalence {R S : Sheaf (ProEt.topology T) CommRingCat.{u + 1}}
    (e : R ≅ S) : DerivedCategory (pbcModules T S) ≌ DerivedCategory (pbcModules T R) :=
  CategoryTheory.Equivalence.mk (pbcDerivedRestrict e.hom) (pbcDerivedRestrict e.inv)
    (pbcDerivedRestrictComp e.inv e.hom (𝟙 S) e.inv_hom_id ≪≫
      Functor.mapDerivedCategoryNatIso (pbcRestrictId S) ≪≫
      Functor.mapDerivedCategoryIdIso _).symm
    (pbcDerivedRestrictComp e.hom e.inv (𝟙 R) e.hom_inv_id ≪≫
      Functor.mapDerivedCategoryNatIso (pbcRestrictId R) ≪≫
      Functor.mapDerivedCategoryIdIso _)

/-- Derived scalar extension commutes with derived restriction along coefficient
isomorphisms compatible with the extension maps. -/
def pbcDerivedExtendRestrictIso
    {R R' S S' : Sheaf (ProEt.topology T) CommRingCat.{u + 1}}
    (ψ : R ≅ R') (κ : S ≅ S') (φ : R ⟶ S) (φ' : R' ⟶ S') (w : φ ≫ κ.hom = ψ.hom ≫ φ') :
    pbcDerivedRestrict ψ.hom ⋙ pbcDerivedExtend φ ≅
      pbcDerivedExtend φ' ⋙ pbcDerivedRestrict κ.hom :=
  (((pbcDerivedRestrictEquivalence ψ).toAdjunction.comp
      (pbcDerivedScalarAdjunction φ)).ofNatIsoRight
    (pbcDerivedRestrictComp ψ.inv φ (ψ.inv ≫ φ) rfl ≪≫
      (pbcDerivedRestrictComp φ' κ.inv (ψ.inv ≫ φ) (by
        rw [Iso.eq_inv_comp, ← Category.assoc, ← w, Category.assoc, Iso.hom_inv_id,
          Category.comp_id])).symm)).leftAdjointUniq
    ((pbcDerivedScalarAdjunction φ').comp (pbcDerivedRestrictEquivalence κ).toAdjunction)

/-- Cohomology of the derived extension of a relabeled complex is the relabeled cohomology
of the derived extension. -/
def pbcHomologyExtendRestrictIso
    {R R' S S' : Sheaf (ProEt.topology T) CommRingCat.{u + 1}}
    (ψ : R ≅ R') (κ : S ≅ S') (φ : R ⟶ S) (φ' : R' ⟶ S') (w : φ ≫ κ.hom = ψ.hom ≫ φ')
    (C : CochainComplex (pbcModules T R') ℤ) (q : ℤ) :
    (DerivedCategory.homologyFunctor _ q).obj ((pbcDerivedExtend φ).obj
        (DerivedCategory.Q.obj (((pbcRestrict ψ.hom).mapHomologicalComplex (.up ℤ)).obj C))) ≅
      (pbcRestrict κ.hom).obj ((DerivedCategory.homologyFunctor _ q).obj
        ((pbcDerivedExtend φ').obj (DerivedCategory.Q.obj C))) :=
  (DerivedCategory.homologyFunctor _ q).mapIso
      ((pbcDerivedExtend φ).mapIso
          ((pbcRestrict ψ.hom).mapDerivedCategoryFactors.app C).symm ≪≫
        (pbcDerivedExtendRestrictIso ψ κ φ φ' w).app (DerivedCategory.Q.obj C)) ≪≫
    (((pbcRestrict κ.hom).mapDerivedCategoryHomologyFunctorIso q).app _).symm

end Transport

variable {X Y U : Scheme.{u}} (f : X ⟶ Y) [IsIso f]
  {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A) (g : U ⟶ Y)

/-- The local coefficient comparison uses composition of inverse images followed by
inverse image of the completed coefficient comparison for the inverse isomorphism. -/
def pbcIsoLocalCoefficient :
    (adicTowerInverseImage (g ≫ inv f)).obj (pbcAdicCompletion X d) ≅
      (adicTowerInverseImage g).obj (pbcAdicCompletion Y d) :=
  (proEtaleRingInverseImageComp g (inv f)).app (pbcAdicCompletion X d) ≪≫
    (adicTowerInverseImage g).mapIso (d.integralRingIso (inv f))

/-- Relabel the scalar action of each term through the specified local coefficient
isomorphism. Differentials and underlying sheaves are unchanged. No witness is chosen. -/
def pbcIsoLocalComplex
    (C : CochainComplex (pbcModules U
      ((adicTowerInverseImage g).obj (pbcAdicCompletion Y d))) ℤ) :
    CochainComplex (pbcModules U
      ((adicTowerInverseImage (g ≫ inv f)).obj (pbcAdicCompletion X d))) ℤ :=
  ((pbcRestrict (pbcIsoLocalCoefficient f d g).hom).mapHomologicalComplex (.up ℤ)).obj C

/-- The constant-ring comparison of inverse images is natural in the coefficient ring. -/
private theorem constantCoefficients_naturality {Z : Scheme.{u}} (a : U ⟶ Z)
    {B B' : Type (u + 1)} [CommRing B] [CommRing B'] (r : B →+* B') :
    (adicTowerInverseImage a).map
        ((constantSheaf (ProEt.topology Z) CommRingCat.{u + 1}).map (CommRingCat.ofHom r)) ≫
      (constantCoefficients a B').hom =
    (constantCoefficients a B).hom ≫
      (constantSheaf (ProEt.topology U) CommRingCat.{u + 1}).map (CommRingCat.ofHom r) := by
  simp only [constantCoefficients, asIso_hom]
  exact proEtaleConstantInverseImageMap_naturality a (CommRingCat.ofHom r)

/-- The constant-ring comparison of a composite at a finite quotient level. -/
private theorem constantCoefficients_comp_hom {Z W : Scheme.{u}} (a : U ⟶ Z) (b : Z ⟶ W)
    (n : ℕ) :
    (constantCoefficients (a ≫ b) (A ⧸ d.ideal ^ (n + 1))).hom =
      (proEtaleRingInverseImageComp a b).hom.app
          (adicLisseConstantRing W (A ⧸ d.ideal ^ (n + 1))) ≫
        (adicTowerInverseImage a).map (proEtaleConstantInverseImageMap b CommRingCat.{u + 1}
          (CommRingCat.of (A ⧸ d.ideal ^ (n + 1)))) ≫
        (constantCoefficients a (A ⧸ d.ideal ^ (n + 1))).hom := by
  simp only [constantCoefficients, asIso_hom]
  exact (proEtale_profinite_coefficient_inverse_image d.ringTower).2.2.2.2.2.2.2.2.2.1
    U Z W a b (op n)

/-- The finite-level coefficient isomorphism induced by the constant comparisons. -/
private def pbcIsoLevelCoefficient (n : ℕ) :
    (adicTowerInverseImage (g ≫ inv f)).obj ((pbcAdicRings X d).obj (op n)) ≅
      (adicTowerInverseImage g).obj ((pbcAdicRings Y d).obj (op n)) :=
  ((adicTowerInverseImage (g ≫ inv f)).mapIso (pbcLevelConstantComparison X d n)).symm ≪≫
    constantCoefficients (g ≫ inv f) (A ⧸ d.ideal ^ (n + 1)) ≪≫
    (constantCoefficients g (A ⧸ d.ideal ^ (n + 1))).symm ≪≫
    (adicTowerInverseImage g).mapIso (pbcLevelConstantComparison Y d n)

/-- The projection square of the local coefficient isomorphism. -/
private theorem pbcIsoLevelCoefficient_comm (n : ℕ) :
    (adicTowerInverseImage (g ≫ inv f)).map (pbcAdicProjection X d n) ≫
        (pbcIsoLevelCoefficient f d g n).hom =
      (pbcIsoLocalCoefficient f d g).hom ≫
        (adicTowerInverseImage g).map (pbcAdicProjection Y d n) := by
  have hp : (d.integralRingIso (inv f)).hom ≫ pbcAdicProjection Y d n =
      (adicTowerInverseImage (inv f)).map (pbcAdicProjection X d n) ≫
        (d.finiteRingIso (inv f) n).hom := d.projection_comm (inv f) n
  have hn := (proEtaleRingInverseImageComp g (inv f)).hom.naturality
      (pbcAdicProjection X d n ≫ (pbcLevelConstantComparison X d n).inv)
  simp only [Functor.map_comp, Functor.comp_map, Category.assoc] at hn
  simp only [pbcIsoLevelCoefficient, pbcIsoLocalCoefficient, Iso.trans_hom, Iso.symm_hom,
    Functor.mapIso_hom, Functor.mapIso_inv, Iso.app_hom, Category.assoc,
    constantCoefficients_comp_hom d g (inv f) n, Iso.hom_inv_id_assoc]
  rw [← Functor.map_comp (adicTowerInverseImage g) (d.integralRingIso (inv f)).hom, hp]
  simp only [AdicCoefficientDatum.finiteRingIso, Iso.trans_hom, Functor.mapIso_hom,
    Iso.symm_hom, asIso_hom, Functor.map_comp]
  rw [reassoc_of% hn]
  rfl

/-- Finite lissity is invariant under isomorphism of module sheaves. -/
private theorem relativelyFiniteLisse_of_iso {Z : Scheme.{u}} {a : U ⟶ Z}
    {B : Type (u + 1)} [CommRing B]
    {F G : pbcModules U ((adicTowerInverseImage a).obj (adicLisseConstantRing Z B))}
    (e : F ≅ G) (h : IsRelativelyFiniteLisseModule a B G) :
    IsRelativelyFiniteLisseModule a B F := by
  obtain ⟨S, hS, hs⟩ := h
  refine ⟨S, hS, fun V b hb ↦ ?_⟩
  obtain ⟨M, hM, ⟨i⟩⟩ := hs V b hb
  exact ⟨M, hM, ⟨(SheafOfModules.overFunctor _ V).mapIso e ≪≫ i⟩⟩

/-- Restriction along a map of inverse-image constant rings compatible with the constant
comparisons preserves finite lissity. -/
private theorem relativelyFiniteLisse_restrict {Z₁ Z₂ : Scheme.{u}} (g₁ : U ⟶ Z₁)
    (g₂ : U ⟶ Z₂) (B : Type (u + 1)) [CommRing B]
    (γ : (adicTowerInverseImage g₁).obj (adicLisseConstantRing Z₁ B) ⟶
      (adicTowerInverseImage g₂).obj (adicLisseConstantRing Z₂ B))
    (hγ : γ ≫ (constantCoefficients g₂ B).hom = (constantCoefficients g₁ B).hom)
    (G : pbcModules U ((adicTowerInverseImage g₂).obj (adicLisseConstantRing Z₂ B)))
    (hG : IsRelativelyFiniteLisseModule g₂ B G) :
    IsRelativelyFiniteLisseModule g₁ B ((pbcRestrict γ).obj G) := by
  have hu : relativeUnit g₁ B ≫ ((adicLisseForget U).map γ).hom = relativeUnit g₂ B := by
    have hi : (constantCoefficients g₁ B).inv ≫ γ = (constantCoefficients g₂ B).inv := by
      rw [Iso.inv_comp_eq, ← hγ, Category.assoc, Iso.hom_inv_id, Category.comp_id]
    simp only [relativeUnit, Category.assoc]
    rw [← hi, Functor.map_comp]
    rfl
  let E : (relativeRestriction g₁ B).obj ((pbcRestrict γ).obj G) ≅
      (relativeRestriction g₂ B).obj G :=
    (fullyFaithfulSheafToPresheaf _ _).preimageIso (NatIso.ofComponents (fun W ↦
      LinearEquiv.toModuleIso (R := B)
        (X₁ := ((relativeRestriction g₁ B).obj ((pbcRestrict γ).obj G)).obj.obj W)
        (X₂ := ((relativeRestriction g₂ B).obj G).obj.obj W)
        { toFun := fun x ↦ x
          invFun := fun x ↦ x
          left_inv := fun _ ↦ rfl
          right_inv := fun _ ↦ rfl
          map_add' := fun _ _ ↦ rfl
          map_smul' := fun b x ↦
            congrArg (fun r ↦ r • (show G.val.obj W from x))
              (ConcreteCategory.congr_hom (congr_app hu W) b) })
      (fun _ ↦ rfl))
  rw [relativeFinite_iff] at hG ⊢
  obtain ⟨S, hS, h⟩ := hG
  refine ⟨S, hS, fun V a ha ↦ ?_⟩
  obtain ⟨M, hM, ⟨e⟩⟩ := h V a ha
  exact ⟨M, hM, ⟨((ProEt.topology U).overPullback _ V).mapIso E ≪≫ e⟩⟩

/-- Restriction along a completed-coefficient map compatible with the constant comparisons
of all quotient rings preserves relative adic lissity. -/
private theorem relativelyAdicLisse_restrict [IsNoetherianRing A] {Z₁ Z₂ : Scheme.{u}}
    (g₁ : U ⟶ Z₁) (g₂ : U ⟶ Z₂) (I : Ideal A)
    (β : (adicTowerInverseImage g₁).obj (adicLisseCompletedRing Z₁ I) ⟶
      (adicTowerInverseImage g₂).obj (adicLisseCompletedRing Z₂ I))
    (hβ : ∀ n : ℕ,
      (adicTowerInverseImage g₁).map (limit.π (adicLisseRingSystem Z₁ I) (op n)) ≫
          (constantCoefficients g₁ (A ⧸ I ^ (n + 1))).hom =
        β ≫ (adicTowerInverseImage g₂).map (limit.π (adicLisseRingSystem Z₂ I) (op n)) ≫
          (constantCoefficients g₂ (A ⧸ I ^ (n + 1))).hom)
    (G : pbcModules U ((adicTowerInverseImage g₂).obj (adicLisseCompletedRing Z₂ I)))
    (hG : IsRelativelyAdicLisseModule g₂ I G) :
    IsRelativelyAdicLisseModule g₁ I ((pbcRestrict β).obj G) := by
  let α := (constantCoefficients g₁ A).hom ≫ (constantCoefficients g₂ A).inv
  have hα : α ≫ (constantCoefficients g₂ A).hom = (constantCoefficients g₁ A).hom := by
    simp [α]
  obtain ⟨T, hT, hmodels⟩ := hG
  refine ⟨T, hT, fun V a ha ↦ ?_⟩
  obtain ⟨N, hN, hfin, hm⟩ := hmodels V a ha
  refine ⟨N, hN, hfin, ?_⟩
  exact localModel_restrict U _ _ _ _ ((adicLisseForget U).map α) ((adicLisseForget U).map β)
    (fun n ↦ (adicLisseForget U).map ((constantCoefficients g₁ (A ⧸ I ^ (n + 1))).hom ≫
      (constantCoefficients g₂ (A ⧸ I ^ (n + 1))).inv))
    (fun n ↦ by
      rw [← Functor.map_comp, ← Functor.map_comp]
      congr 1
      rw [reassoc_of% (constantCoefficients_naturality g₁ (Ideal.Quotient.mk (I ^ (n + 1)))),
        Category.assoc, cancel_epi, Iso.comp_inv_eq, Category.assoc,
        constantCoefficients_naturality g₂ (Ideal.Quotient.mk (I ^ (n + 1))),
        Iso.inv_hom_id_assoc])
    (fun n ↦ by
      rw [← Functor.map_comp, ← Functor.map_comp]
      congr 1
      rw [← Category.assoc, hβ n]
      simp)
    _ _
    (concreteModuleSystemComparison g₁ I N ≪≫
      Functor.isoWhiskerLeft (adicLisseModuleSystem U I N)
        (pbcRestrictComp α (constantCoefficients g₂ A).hom _ hα).symm ≪≫
      Functor.isoWhiskerRight (concreteModuleSystemComparison g₂ I N).symm (pbcRestrict α))
    G V hm

/-- Relabeling the completed action preserves adic-lisse terms and finite-lisse
cohomology of each reduction. -/
theorem pbcIsoLocalComplex_properties
    (M : AdicTower Y d) (a b : ℤ) (L : AdicTowerLocalModel d g M a b) :
    (∀ q : ℤ, @IsRelativelyAdicLisseModule _ _ (g ≫ inv f) A _ d.noetherian d.ideal
      ((pbcRestrict ((adicTowerInverseImage (g ≫ inv f)).map
        (pbcCompletedComparison X d).hom)).obj ((pbcIsoLocalComplex f d g L.complex).X q))) ∧
    (∀ (n : ℕ) (q : ℤ), IsRelativelyFiniteLisseModule (g ≫ inv f)
      (A ⧸ d.ideal ^ (n + 1))
      ((pbcRestrict ((adicTowerInverseImage (g ≫ inv f)).map
        (pbcLevelConstantComparison X d n).hom)).obj
          ((DerivedCategory.homologyFunctor _ q).obj
            (adicTowerLocalReduction d (g ≫ inv f) (pbcIsoLocalComplex f d g L.complex) n)))) := by
  let := d.noetherian
  let Lh := adicTowerInverseImage (g ≫ inv f)
  let Lg := adicTowerInverseImage g
  let ψ := pbcIsoLocalCoefficient f d g
  refine ⟨fun q ↦ ?_, fun n q ↦ ?_⟩
  · let β := Lh.map (pbcCompletedComparison X d).hom ≫ ψ.hom ≫
      Lg.map (pbcCompletedComparison Y d).inv
    have hβ (n : ℕ) :
        Lh.map (limit.π (adicLisseRingSystem X d.ideal) (op n)) ≫
            (constantCoefficients (g ≫ inv f) (A ⧸ d.ideal ^ (n + 1))).hom =
          β ≫ Lg.map (limit.π (adicLisseRingSystem Y d.ideal) (op n)) ≫
            (constantCoefficients g (A ⧸ d.ideal ^ (n + 1))).hom := by
      have hK := pbcIsoLevelCoefficient_comm f d g n
      have h1 : (pbcCompletedComparison Y d).inv ≫
          limit.π (adicLisseRingSystem Y d.ideal) (op n) =
            pbcAdicProjection Y d n ≫ (pbcLevelConstantComparison Y d n).inv :=
        HasLimit.isoOfNatIso_inv_π _ _
      have h2 : (pbcCompletedComparison X d).hom ≫ pbcAdicProjection X d n =
          limit.π (adicLisseRingSystem X d.ideal) (op n) ≫
            (pbcLevelConstantComparison X d n).hom :=
        HasLimit.isoOfNatIso_hom_π _ _
      simp only [β, Category.assoc]
      rw [← Functor.map_comp_assoc Lg, h1, Functor.map_comp_assoc, ← reassoc_of% hK]
      simp only [pbcIsoLevelCoefficient, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
        Functor.mapIso_inv, Category.assoc, ← Functor.map_comp_assoc]
      rw [← Functor.map_comp_assoc, ← Functor.map_comp_assoc, reassoc_of% h2,
        Iso.hom_inv_id, Category.comp_id]
      simp
    have hβ' : β ≫ Lg.map (pbcCompletedComparison Y d).hom =
        Lh.map (pbcCompletedComparison X d).hom ≫ ψ.hom := by
      rw [Category.assoc, Category.assoc, ← Functor.map_comp, Iso.inv_hom_id,
        CategoryTheory.Functor.map_id]
      erw [Category.comp_id]
    exact relativelyLisse_of_iso (g ≫ inv f) d.ideal
      ((pbcRestrictComp _ ψ.hom _ rfl).app _ ≪≫ ((pbcRestrictComp β _ _ hβ').app _).symm)
      (relativelyAdicLisse_restrict (g ≫ inv f) g d.ideal β hβ _ (L.adicLisse q))
  · let κ := pbcIsoLevelCoefficient f d g n
    let γ := (constantCoefficients (g ≫ inv f) (A ⧸ d.ideal ^ (n + 1))).hom ≫
      (constantCoefficients g (A ⧸ d.ideal ^ (n + 1))).inv
    have hκ : Lh.map (pbcLevelConstantComparison X d n).hom ≫ κ.hom =
        γ ≫ Lg.map (pbcLevelConstantComparison Y d n).hom := by
      simp [κ, γ, pbcIsoLevelCoefficient, Lh, Lg]
    exact relativelyFiniteLisse_of_iso
      ((pbcRestrict (Lh.map (pbcLevelConstantComparison X d n).hom)).mapIso
          (pbcHomologyExtendRestrictIso ψ κ _ _ (pbcIsoLevelCoefficient_comm f d g n)
            L.complex q) ≪≫
        (pbcRestrictComp _ κ.hom _ hκ).app _ ≪≫ ((pbcRestrictComp γ _ _ rfl).app _).symm)
      (relativelyFiniteLisse_restrict (g ≫ inv f) g _ γ (by simp [γ]) _ (L.finiteLisse n q))

end AlgebraicGeometry.Scheme
