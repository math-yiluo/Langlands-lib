/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Rational.RationalModuleRealizationFunctor
public import WeilConjectures.CategoryTheory.Scalar.ScalarLocalizationDerivedHom
public import Mathlib.CategoryTheory.Linear.Basic
import WeilConjectures.AlgebraicGeometry.Rational.RationalRealizationOrdinaryLocalization
import WeilConjectures.CategoryTheory.Scalar.ScalarLocalizationTelescopeOfUniverses
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import all WeilConjectures.CategoryTheory.Scalar.ScalarLocalizationDerivedHom

/-!
# Transport of the scalar-localization Hom comparison to normalized rational coefficients

## References

* Bhatt--Scholze, Lemma 6.8.12 and Proposition 6.8.14(2), pp. 61--62
* Bhatt--Scholze, Proposition 6.8.14(2)
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
variable (X : Scheme.{u}) [IsNoetherian X]
  [Fact (∃ n : ℕ, topologicalKrullDim X ≤ n)]
  [Fact (∀ x : X, IsUnit (l : X.presheaf.stalk x))]

/-- Restrict the realization's normalized constant field action along the canonical
identification of the localized valuation ring with E. This constructs only the scalar
structure required to apply the existing localized-Hom comparison predicate. -/
@[instance_reducible]
def rationalRealizationLocalizedLinear (R : RationalModuleRealization l E X) :
    Linear (Localization.Away (pbcUniformizer l E))
      (DerivedCategory (pbcModules X (rationalCoefficientSheaf l X E))) :=
  letI := R.moduleLinear
  letI : Linear E (DerivedCategory (pbcModules X (rationalCoefficientSheaf l X E))) :=
    inferInstance
  { homModule := fun M N ↦
      Module.compHom (M ⟶ N) (pbcRationalCoefficientEquiv l E).toRingHom
    smul_comp := fun M N P a f g ↦
      Linear.smul_comp M N P (pbcRationalCoefficientEquiv l E a) f g
    comp_smul := fun M N P f a g ↦
      Linear.comp_smul M N P f (pbcRationalCoefficientEquiv l E a) g }

private def homConjugation (S : Type*) [CommRing S]
    {T : Type*} [Category T] [Preadditive T] [Linear S T]
    {K L K' L' : T} (a : K ≅ K') (b : L ≅ L') :
    (K ⟶ L) ≃ₗ[S] (K' ⟶ L') where
  toFun f := a.inv ≫ f ≫ b.hom
  invFun f := a.hom ≫ f ≫ b.inv
  left_inv f := by simp [Category.assoc]
  right_inv f := by simp [Category.assoc]
  map_add' f g := by simp [Preadditive.comp_add, Preadditive.add_comp]
  map_smul' r f := by simp [Linear.comp_smul, Linear.smul_comp]

private theorem transportHomComparison
    (A : Type*) [CommRing A] (t : A)
    {D T U : Type*} [Category D] [Category T] [Category U]
    [Preadditive D] [Preadditive T] [Preadditive U]
    [HasShift D ℤ] [HasShift T ℤ] [HasShift U ℤ]
    [Linear A D] [Linear (Localization.Away t) T] [Linear (Localization.Away t) U]
    [∀ q : ℤ, (shiftFunctor U q).Linear (Localization.Away t)]
    (F : D ⥤ T) [F.CommShift ℤ]
    (G : T ⥤ U) [G.Full] [G.Faithful] [G.Additive]
    [G.Linear (Localization.Away t)] [G.CommShift ℤ]
    (H : D ⥤ U) (δ : F ⋙ G ≅ H) (P B : D → Prop)
    (h : scalarLocalizationHomComparison A t F P B) :
    ∃ (_shift : H.CommShift ℤ), scalarLocalizationHomComparison A t H P B := by
  let := Functor.CommShift.ofIso δ ℤ
  refine ⟨inferInstance, ?_⟩
  apply CategoryTheory.scalarHomComparison_of_normalized
  obtain ⟨e, he, _⟩ := h
  let c (K L : D) (q : ℤ) :
      (F.obj K ⟶ (F.obj L)⟦q⟧) ≃ₗ[Localization.Away t]
        (H.obj K ⟶ (H.obj L)⟦q⟧) :=
    (LinearEquiv.ofBijective (G.mapLinearMap (Localization.Away t))
      ⟨G.map_injective, G.map_surjective⟩).trans
      ((homConjugation (Localization.Away t) (Iso.refl _) ((G.commShiftIso q).app _)).trans
        (homConjugation (Localization.Away t) (δ.app K)
          ((shiftFunctor U q).mapIso (δ.app L))))
  refine ⟨fun K hK L hL q ↦ (e K hK L hL q).trans (c K L q), ?_⟩
  intro K hK L hL q f n
  change c K L q (e K hK L hL q (LocalizedModule.mk f _)) = _
  have hn := congrArg (c K L q) (he K hK L hL q f n)
  change c K L q (e K hK L hL q (LocalizedModule.mk f _)) = _ at hn
  rw [hn, map_smul]
  congr 1
  change δ.inv.app K ≫ (𝟙 _ ≫ G.map
      (F.map f ≫ (F.commShiftIso q).hom.app L) ≫
        (G.commShiftIso q).hom.app (F.obj L)) ≫ (δ.hom.app L)⟦q⟧' = _
  simp only [Category.id_comp, G.map_comp, Category.assoc,
    Functor.CommShift.ofIso_commShiftIso_hom_app,
    Functor.commShiftIso_comp_hom_app]
  simpa only [Functor.comp_map, Category.assoc] using
    (δ.inv.naturality_assoc f
      (G.map ((F.commShiftIso q).hom.app L) ≫
        (G.commShiftIso q).hom.app (F.obj L) ≫ (δ.hom.app L)⟦q⟧')).symm

/-- The general bounded-below Hom localization comparison, in the normalized continuous
coefficient presentation and for the universal derived tensor functor. No constructibility
hypothesis or conclusion about the raw rationalization functor occurs here. -/
theorem rationalRealizationHomTransport (R : RationalModuleRealization l E X) :
    (fun [_localizedLinear : Linear (Localization.Away (pbcUniformizer l E))
        (DerivedCategory (pbcModules X (rationalCoefficientSheaf l X E)))] ↦
      ∃ (_shift : (pbcDerivedExtend (R.integralIso.hom ≫ R.inclusion)).CommShift ℤ),
        scalarLocalizationHomComparison (PbcIntegralRing l E) (pbcUniformizer l E)
          (pbcDerivedExtend (R.integralIso.hom ≫ R.inclusion))
          DerivedCategory.CountableBoundedBelowHomContinuous
          (fun L ↦ ∃ b : ℤ, L.IsGE b))
      (_localizedLinear := rationalRealizationLocalizedLinear l E X R) := by
  classical
  let B := pbcAdicCompletion X (pbcIntegralDatum l E)
  let a := pbcCompletedScalarSections X (pbcIntegralDatum l E)
  let t := pbcUniformizer l E
  let S := ringedLocalizationRingOfUniverses.{u + 1, u + 1, u} B (a t)
  let := R.moduleLinear
  let : Linear E (DerivedCategory (pbcModules X (rationalCoefficientSheaf l X E))) :=
    inferInstance
  let : Linear (Localization.Away t) (DerivedCategory (pbcModules X S)) :=
    scalarLocalizationDerivedLinearOfUniverses (Localization.Away t) S
      (scalarLocalizationCoefficientMapOfUniverses (PbcIntegralRing l E) B a t)
  let : EssentiallySmall.{u + 1} X.ProEt := essentiallySmallSelf.{0, u, u + 1} _
  obtain ⟨F, hF, hmap, hAdd, hLim, hCol, _⟩ :=
    scalarLocalization_sheaf_exact (ProEt.topology X) B (a t)
  let := hAdd
  let := hLim
  let := hCol
  let : Linear (Localization.Away t) (pbcModules X S) :=
    rationalLocalizationModulesLinear X (PbcIntegralRing l E) B a t
  obtain ⟨G₀, hEquiv, hGAdd, hscalar, ⟨e⟩⟩ :=
    rationalRealizationOrdinaryLocalization l E X R F hF hmap
  have := hEquiv
  have := hGAdd
  let G := G₀.mapDerivedCategory
  let α := R.integralIso.hom ≫ R.inclusion
  let H := pbcExtend α
  have := R.ordinary_exact.1
  have := R.ordinary_exact.2
  have := pbcDerivedExtension_universal α
  have : H.mapDerivedCategory.IsLeftDerivedFunctor H.mapDerivedCategoryFactorsh.hom
      (HomotopyCategory.quasiIso (pbcModules X B) (.up ℤ)) :=
    Functor.isLeftDerivedFunctor_of_inverts _ _ _
  let model : pbcDerivedExtend α ≅ H.mapDerivedCategory :=
    Functor.leftDerivedUnique _ _ (pbcExtensionCounit α) H.mapDerivedCategoryFactorsh.hom
      (HomotopyCategory.quasiIso (pbcModules X B) (.up ℤ))
  have := comp_preservesFiniteLimits F G₀
  have := comp_preservesFiniteColimits F G₀
  let δ : F.mapDerivedCategory ⋙ G ≅ pbcDerivedExtend α :=
    Functor.mapDerivedCategoryCompIso F G₀ ≪≫
      Functor.mapDerivedCategoryNatIso e ≪≫ model.symm
  let : Linear (Localization.Away t)
      (DerivedCategory (pbcModules X (rationalCoefficientSheaf l X E))) :=
    rationalRealizationLocalizedLinear l E X R
  have : G.Linear (Localization.Away t) := ⟨fun f r ↦
    CategoryTheory.exact_derived_semilinear (pbcRationalCoefficientEquiv l E).toRingHom G₀
      (fun M r ↦ by
        have h := hscalar (𝟙 M) r
        change G₀.map (r • 𝟙 M) =
          (pbcRationalCoefficientEquiv l E) r • 𝟙 (G₀.obj M)
        simpa only [G₀.map_id] using h) f r⟩
  have : ∀ q : ℤ, (shiftFunctor
      (DerivedCategory (pbcModules X (rationalCoefficientSheaf l X E))) q).Linear
        (Localization.Away t) := fun q ↦
    ⟨fun f r ↦ (shiftFunctor _ q).map_smul (pbcRationalCoefficientEquiv l E r) f⟩
  obtain ⟨U, hUadd, hUshift, adj, htel, hsemi⟩ :=
    scalarLocalization_telescopeOfUniverses (PbcIntegralRing l E) B a t F hF hmap
  let := hUadd
  let := hUshift
  have hHom := CategoryTheory.hom_comparison_of_telescope (PbcIntegralRing l E) t
    F.mapDerivedCategory U adj hsemi htel
  exact transportHomComparison (PbcIntegralRing l E) t F.mapDerivedCategory G _ δ
    DerivedCategory.CountableBoundedBelowHomContinuous (fun L ↦ ∃ b : ℤ, L.IsGE b)
    hHom

end AlgebraicGeometry.Scheme
