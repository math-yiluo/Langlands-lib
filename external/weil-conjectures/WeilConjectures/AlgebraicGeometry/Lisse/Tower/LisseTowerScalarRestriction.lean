/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Lisse.Tower.LisseTowerEtaleDescentData
import WeilConjectures.AlgebraicGeometry.WeilSheaf.ProfiniteCoefficientInverseImageSupplement
import WeilConjectures.AlgebraicGeometry.CoefficientSheafificationSquare.CoefficientSheafificationSections
import all WeilConjectures.AlgebraicGeometry.Constant.ConstantAdicQuotientScalarComparison
import WeilConjectures.CategoryTheory.Constant.ConstantDerivedNormalizationUniversalSupplement
import WeilConjectures.AlgebraicGeometry.Comparison.ComparisonNormalizationReflectsUniversal
import WeilConjectures.AlgebraicGeometry.Etale.EtaleSourceNormalizationUniversal
import Mathlib.CategoryTheory.Adjunction.Comma
import Mathlib.CategoryTheory.Adjunction.Limits

/-! # The scalar square for the fixed finite coefficient realization

## References

* Stacks Tag 03CZ
* Stacks Tags 05RU and 03DA
* Stacks Tags 06YY and 03ED
* Stacks Project, Tags 03CY, 03DA, 06YY, 099Z and 09B1
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genInjectivity false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genCtorIdx false
set_option Elab.async false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme
attribute [local irreducible] HasDerivedCategory.standard pbcDerivedRestrict
  lisseTowerFixedRealization

/-- The ordinary functor whose exact localization is the fixed realization. -/
def lisseTowerFixedSheafRealization {X Z : Scheme.{u}} (f : Z ⟶ X)
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A) (n : ℕ) :=
  sheafCompose (ProEt.topology Z)
      (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} (constantAdicQuotientMap d.ideal n)) ⋙
    lisseTowerFiniteSheafRealization f d n

instance lisseTowerFixedSheafRealization_additive {X Z : Scheme.{u}} (f : Z ⟶ X)
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A) (n : ℕ) :
    (lisseTowerFixedSheafRealization f d n).Additive := by
  unfold lisseTowerFixedSheafRealization
  infer_instance

instance lisseTowerFixedSheafRealization_limits {X Z : Scheme.{u}} (f : Z ⟶ X)
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A) (n : ℕ) :
    PreservesFiniteLimits (lisseTowerFixedSheafRealization f d n) := by
  unfold lisseTowerFixedSheafRealization
  infer_instance

instance lisseTowerFixedSheafRealization_colimits {X Z : Scheme.{u}} (f : Z ⟶ X)
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A) (n : ℕ) :
    PreservesFiniteColimits (lisseTowerFixedSheafRealization f d n) := by
  unfold lisseTowerFixedSheafRealization
  infer_instance

/-- The exact composition comparison; it does not change the fixed realization. -/
def lisseTowerFixedRealizationIso {X Z : Scheme.{u}} (f : Z ⟶ X)
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A) (n : ℕ) :
    (lisseTowerFixedSheafRealization f d n).mapDerivedCategory ≅
      lisseTowerFixedRealization f d n := by
  unfold lisseTowerFixedSheafRealization lisseTowerFixedRealization normalizationRestrict
  exact (Functor.mapDerivedCategoryCompIso _ _).symm

/-- Forget the scalar action after associated-module-sheaf realization. -/
def lisseTowerCoefficientRealizationForgetIso
    {C : Type (u + 1)} [Category.{u} C] (J : GrothendieckTopology C)
    (B R : Type (u + 1)) [CommRing B] [CommRing R] (q : R →+* B)
    (S : Sheaf J RingCat.{u + 1})
    (a : (Functor.const Cᵒᵖ).obj (RingCat.of R) ⟶ S.obj)
    [Presheaf.IsLocallyInjective J a] [Presheaf.IsLocallySurjective J a]
    [HasSheafify J AddCommGrpCat.{u + 1}] [J.WEqualsLocallyBijective AddCommGrpCat.{u + 1}] :
    (sheafCompose J (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} q) ⋙
      (sheafToPresheaf J (ModuleCat.{u + 1} R) ⋙
        ProEtale.finiteCoefficientModulePresheaf C R ⋙
        PresheafOfModules.sheafification a)) ⋙ SheafOfModules.toSheaf S ≅
      sheafCompose J (forget₂ (ModuleCat.{u + 1} B) AddCommGrpCat.{u + 1}) := by
  let G := sheafCompose J (forget₂ (ModuleCat.{u + 1} B) AddCommGrpCat.{u + 1})
  change (G ⋙ sheafToPresheaf _ _) ⋙ presheafToSheaf _ _ ≅ G
  exact Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft G (asIso (sheafificationAdjunction J AddCommGrpCat.{u + 1}).counit) ≪≫
      Functor.rightUnitor G

/-- Forgetting the scalar action identifies realization with the original abelian sheaf.
The identification is the counit of ordinary abelian sheafification. -/
def lisseTowerFixedForgetIso {X Z : Scheme.{u}} (f : Z ⟶ X)
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A) (n : ℕ) :
    lisseTowerFixedSheafRealization f d n ⋙ SheafOfModules.toSheaf _ ≅
      sheafCompose (ProEt.topology Z)
        (forget₂ (ModuleCat.{u + 1} (lisseTowerEtaleRing d n)) AddCommGrpCat.{u + 1}) := by
  exact lisseTowerCoefficientRealizationForgetIso (ProEt.topology Z) _ _
    (constantAdicQuotientMap d.ideal n) _ (lisseTowerFiniteScalarMap f d n)

/-- Scalar restriction does not change the underlying abelian sheaf. -/
def lisseTowerRestrictForgetIso {Z : Scheme.{u}}
    {R S : Sheaf (ProEt.topology Z) CommRingCat.{u + 1}} (a : R ⟶ S) :
    pbcRestrict a ⋙ SheafOfModules.toSheaf _ ≅ SheafOfModules.toSheaf _ := Iso.refl _

/-- The etale comparison followed by the prescribed fixed realization. -/
abbrev lisseTowerEtaleRealization {X Z : Scheme.{u}} (f : Z ⟶ X)
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A) (n : ℕ) :=
  (ProEtale.comparisonUpperStar
    (ModuleCat.{u + 1} (lisseTowerEtaleRing d n)) Z).mapDerivedCategory ⋙
      lisseTowerFixedRealization f d n

/-- The type of the ordinary consecutive scalar square. -/
abbrev LisseTowerScalarSquare {X Z : Scheme.{u}} (f : Z ⟶ X)
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A) (n : ℕ) :=
  sheafCompose (ProEt.topology Z)
      (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} (lisseTowerEtaleQuotient d n)) ⋙
        lisseTowerFixedSheafRealization f d (n + 1) ≅
    lisseTowerFixedSheafRealization f d n ⋙
      pbcRestrict ((adicTowerInverseImage f).map
        (pbcAdicQuotient X d (n + 1) n (Nat.le_succ n)))

/-- Fixed-ring restriction preserves the underlying abelian sheaf. -/
def lisseTowerFixedRestrictForgetIso
    {C : Type (u + 1)} [Category.{u} C] (J : GrothendieckTopology C)
    {R S : Type (u + 1)} [CommRing R] [CommRing S] (q : R →+* S) :
    sheafCompose J (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} q) ⋙
        sheafCompose J (forget₂ (ModuleCat.{u + 1} R) AddCommGrpCat.{u + 1}) ≅
      sheafCompose J (forget₂ (ModuleCat.{u + 1} S) AddCommGrpCat.{u + 1}) := Iso.refl _

/-- Normalize a scalar square against specified comparisons of underlying objects.
Keeping this generic prevents reduction of the concrete adic coefficient constructions. -/
@[irreducible] def lisseTowerScalarSquareNormalized
    {C C' D D' E : Type*} [Category C] [Category C'] [Category D] [Category D'] [Category E]
    {Q : C ⥤ C'} {R : D ⥤ D'} {F : C ⥤ D} {F' : C' ⥤ D'}
    {H : D ⥤ E} {H' : D' ⥤ E} {G : C ⥤ E} {G' : C' ⥤ E}
    (c : Q ⋙ F' ≅ F ⋙ R) (r : R ⋙ H' ≅ H)
    (a : F ⋙ H ≅ G) (a' : F' ⋙ H' ≅ G') (q : Q ⋙ G' ≅ G) : Prop :=
  (Functor.isoWhiskerRight c H' ≪≫ Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft F r ≪≫ a).hom =
      (Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft Q a' ≪≫ q).hom

/-- The square is normalized by the identity on the original fixed sections. -/
@[irreducible] def LisseTowerScalarSquareSections {X Z : Scheme.{u}} (f : Z ⟶ X)
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A) (n : ℕ)
    (c : LisseTowerScalarSquare f d n) : Prop :=
  lisseTowerScalarSquareNormalized c
    (lisseTowerRestrictForgetIso ((adicTowerInverseImage f).map
      (pbcAdicQuotient X d (n + 1) n (Nat.le_succ n))))
    (lisseTowerFixedForgetIso f d n) (lisseTowerFixedForgetIso f d (n + 1))
    (lisseTowerFixedRestrictForgetIso (ProEt.topology Z) (lisseTowerEtaleQuotient d n))

/-- Localize the ordinary square and paste the comparison coefficient mate. -/
def lisseTowerEtaleScalarIso {X Z : Scheme.{u}} (f : Z ⟶ X)
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A) (n : ℕ)
    (c : LisseTowerScalarSquare f d n) :
    normalizationRestrict Z.smallEtaleTopology (lisseTowerEtaleQuotient d n) ⋙
        lisseTowerEtaleRealization f d (n + 1) ≅
      lisseTowerEtaleRealization f d n ⋙
        pbcDerivedRestrict ((adicTowerInverseImage f).map
          (pbcAdicQuotient X d (n + 1) n (Nat.le_succ n))) := by
  unfold pbcDerivedRestrict
  let k := Functor.isoWhiskerLeft
      (normalizationRestrict (ProEt.topology Z) (lisseTowerEtaleQuotient d n))
      (lisseTowerFixedRealizationIso f d (n + 1)).symm ≪≫
    Functor.mapDerivedCategorySquareIso c ≪≫
    Functor.isoWhiskerRight (lisseTowerFixedRealizationIso f d n)
      (pbcRestrict ((adicTowerInverseImage f).map
        (pbcAdicQuotient X d (n + 1) n (Nat.le_succ n)))).mapDerivedCategory
  exact (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (localIsomorphismComparisonCoefficients (lisseTowerEtaleQuotient d n))
      (lisseTowerFixedRealization f d (n + 1)) ≪≫
    Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft _ k ≪≫
    (Functor.associator _ _ _).symm

/-- Reflection of one actual normalized transition on every etale source through
its section-normalized coefficient square. -/
@[irreducible] def LisseTowerScalarSquareReflects {X Z : Scheme.{u}} (f : Z ⟶ X)
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A) (n : ℕ)
    (c : LisseTowerScalarSquare f d n) : Prop :=
  ∀ (M : AdicTower X d)
    (C : DerivedCategory
      (Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} (lisseTowerEtaleRing d (n + 1)))))
    (C' : DerivedCategory
      (Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} (lisseTowerEtaleRing d n))))
    (_hC : ∃ a b : ℤ, ∀ q : ℤ, q < a ∨ b < q →
      IsZero ((DerivedCategory.homologyFunctor _ q).obj C))
    (_hC' : ∃ a b : ℤ, ∀ q : ℤ, q < a ∨ b < q →
      IsZero ((DerivedCategory.homologyFunctor _ q).obj C'))
    (e : (lisseTowerEtaleRealization f d (n + 1)).obj C ≅
      (adicTowerPullback f ((pbcAdicRings X d).obj (op (n + 1)))).obj (M.level (n + 1)))
    (e' : (lisseTowerEtaleRealization f d n).obj C' ≅
      (adicTowerPullback f ((pbcAdicRings X d).obj (op n))).obj (M.level n))
    (δ : C ⟶ (normalizationRestrict Z.smallEtaleTopology
      (lisseTowerEtaleQuotient d n)).obj C'),
    (lisseTowerEtaleRealization f d (n + 1)).map δ ≫
        (lisseTowerEtaleScalarIso f d n c).hom.app C' ≫
        (pbcDerivedRestrict ((adicTowerInverseImage f).map
          (pbcAdicQuotient X d (n + 1) n (Nat.le_succ n)))).map e'.hom =
      e.hom ≫ adicTowerRestrictedTransition d f M (n + 1) n (Nat.le_succ n) →
    ∀ V : Z.Etale, Nonempty (StructuredArrow.IsUniversal
      (StructuredArrow.mk (etaleIsomorphismNormalizationArrow Z
        (lisseTowerEtaleQuotient d n) δ V)))

/-- Local universality of constant algebraic normalization arrows at this quotient. -/
@[irreducible] def LisseTowerConstantLocalUniversal (Z : Scheme.{u})
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A) (n : ℕ) : Prop :=
  ∀ (E : DerivedCategory (ModuleCat.{u + 1} (lisseTowerEtaleRing d (n + 1))))
    (E' : DerivedCategory (ModuleCat.{u + 1} (lisseTowerEtaleRing d n)))
    (k : E ⟶ (normalizationModuleRestrict (lisseTowerEtaleQuotient d n)).obj E'),
    Nonempty (StructuredArrow.IsUniversal (StructuredArrow.mk k)) →
      ∀ V : Z.Etale, Nonempty (StructuredArrow.IsUniversal
        (StructuredArrow.mk (etaleIsomorphismNormalizationArrow Z
          (lisseTowerEtaleQuotient d n)
          (normalizationConstantArrow Z.smallEtaleTopology (lisseTowerEtaleQuotient d n) k) V)))

open CoefficientSheafificationSquare

attribute [local irreducible] lisseTowerFiniteScalarMap lisseTowerFiniteCoefficientIso
  pbcLevelConstantComparison pbcAdicQuotient

private theorem finiteCoefficientIso_square {X Z : Scheme.{u}} (f : Z ⟶ X)
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A) (n : ℕ) :
    (adicTowerInverseImage f).map (pbcAdicQuotient X d (n + 1) n (Nat.le_succ n)) ≫
        (lisseTowerFiniteCoefficientIso f d n).hom =
      (lisseTowerFiniteCoefficientIso f d (n + 1)).hom ≫
        (constantSheaf (ProEt.topology Z) CommRingCat.{u + 1}).map
          (CommRingCat.ofHom (Ideal.Quotient.factorPowSucc d.ideal (n + 1))) := by
  let F := adicTowerInverseImage f
  let t := (constantSheaf (ProEt.topology X) CommRingCat.{u + 1}).map
    (CommRingCat.ofHom (Ideal.Quotient.factorPowSucc d.ideal (n + 1)))
  let a := pbcAdicQuotient X d (n + 1) n (Nat.le_succ n)
  let c := pbcLevelConstantComparison X d (n + 1)
  let c' := pbcLevelConstantComparison X d n
  have hc : t ≫ c'.hom = c.hom ≫ a := by
    simpa only [t, c, c', a, pbcAdicQuotient, adicLisseRingSystem,
      Functor.ofOpSequence_map_homOfLE_succ, Functor.ofOpSequence_obj]
      using pbcConstantSystemComparison_naturality X d (homOfLE (Nat.le_succ n)).op
  have hi : a ≫ c'.inv = c.inv ≫ t := by
    apply (cancel_epi c.hom).mp
    rw [← Category.assoc, ← hc]
    simp only [Category.assoc, Iso.hom_inv_id, Iso.hom_inv_id_assoc, Category.comp_id]
  unfold lisseTowerFiniteCoefficientIso
  change F.map a ≫ (F.map c'.inv ≫ _) = (F.map c.inv ≫ _) ≫ _
  rw [← F.map_comp_assoc, hi, F.map_comp, Category.assoc, Category.assoc]
  exact congrArg (fun z ↦ F.map c.inv ≫ z)
    (proEtaleConstantInverseImageMap_naturality f
      (CommRingCat.ofHom (Ideal.Quotient.factorPowSucc d.ideal (n + 1))))

private theorem finiteScalarMap_square {X Z : Scheme.{u}} (f : Z ⟶ X)
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A) (n : ℕ) :
    (Functor.const Z.ProEtᵒᵖ).map
        (RingCat.ofHom (Ideal.Quotient.factorPowSucc d.ideal (n + 1))) ≫
      lisseTowerFiniteScalarMap f d n =
    lisseTowerFiniteScalarMap f d (n + 1) ≫
      ((adicLisseForget Z).map ((adicTowerInverseImage f).map
        (pbcAdicQuotient X d (n + 1) n (Nat.le_succ n)))).hom := by
  let a := (adicTowerInverseImage f).map
    (pbcAdicQuotient X d (n + 1) n (Nat.le_succ n))
  let t := (constantSheaf (ProEt.topology Z) CommRingCat.{u + 1}).map
    (CommRingCat.ofHom (Ideal.Quotient.factorPowSucc d.ideal (n + 1)))
  let c := lisseTowerFiniteCoefficientIso f d (n + 1)
  let c' := lisseTowerFiniteCoefficientIso f d n
  have hi : t ≫ c'.inv = c.inv ≫ a := by
    apply (cancel_epi c.hom).mp
    rw [← Category.assoc, ← finiteCoefficientIso_square f d n]
    change (a ≫ c'.hom) ≫ c'.inv = c.hom ≫ c.inv ≫ a
    simp only [Category.assoc, Iso.hom_inv_id, Iso.hom_inv_id_assoc, Category.comp_id]
  have hu : (Functor.const Z.ProEtᵒᵖ).map
      (RingCat.ofHom (Ideal.Quotient.factorPowSucc d.ideal (n + 1))) ≫
        adicLisseConstantUnit Z (A ⧸ d.ideal ^ (n + 1)) =
      adicLisseConstantUnit Z (A ⧸ d.ideal ^ (n + 2)) ≫
        ((adicLisseForget Z).map t).hom := by
    exact congrArg (fun k ↦ Functor.whiskerRight k (forget₂ CommRingCat RingCat))
      (toSheafify_naturality (ProEt.topology Z)
        ((Functor.const Z.ProEtᵒᵖ).map
          (CommRingCat.ofHom (Ideal.Quotient.factorPowSucc d.ideal (n + 1)))))
  unfold lisseTowerFiniteScalarMap
  rw [← Category.assoc, hu, Category.assoc, ← ObjectProperty.FullSubcategory.comp_hom,
    ← Functor.map_comp, hi, Functor.map_comp, ObjectProperty.FullSubcategory.comp_hom,
    Category.assoc]

private theorem completionQuotient_square {A : Type (u + 1)} [CommRing A]
    (d : AdicCoefficientDatum A) (n : ℕ) :
    (constantAdicQuotientMap d.ideal n).comp
        (Ideal.Quotient.factorPowSucc d.ideal (n + 1)) =
      (lisseTowerEtaleQuotient d n).comp (constantAdicQuotientMap d.ideal (n + 1)) := by
  apply Ideal.Quotient.ringHom_ext
  ext x
  rfl

@[irreducible] private def scalarSquare {X Z : Scheme.{u}} (f : Z ⟶ X)
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A) (n : ℕ) :
    LisseTowerScalarSquare f d n :=
  coefficientScalarIso (J := ProEt.topology Z) (q := lisseTowerEtaleQuotient d n)
    (b := constantAdicQuotientMap d.ideal (n + 1)) (b' := constantAdicQuotientMap d.ideal n)
    (a := (adicLisseForget Z).map ((adicTowerInverseImage f).map
      (pbcAdicQuotient X d (n + 1) n (Nat.le_succ n))))
    (α := lisseTowerFiniteScalarMap f d (n + 1)) (β := lisseTowerFiniteScalarMap f d n)
    (r := Ideal.Quotient.factorPowSucc d.ideal (n + 1))
    (h := completionQuotient_square d n) (ha := finiteScalarMap_square f d n)

private theorem coefficientForgetIso_eq
    {C : Type (u + 1)} [Category.{u} C] (J : GrothendieckTopology C)
    (B R : Type (u + 1)) [CommRing B] [CommRing R] (q : R →+* B)
    (S : Sheaf J RingCat.{u + 1})
    (a : (Functor.const Cᵒᵖ).obj (RingCat.of R) ⟶ S.obj)
    [Presheaf.IsLocallyInjective J a] [Presheaf.IsLocallySurjective J a]
    [HasSheafify J AddCommGrpCat.{u + 1}] [J.WEqualsLocallyBijective AddCommGrpCat.{u + 1}] :
    lisseTowerCoefficientRealizationForgetIso J B R q S a =
      forgetIso J B R q S a := rfl

private theorem scalarNormalized_iff
    {C C' D D' E : Type*} [Category C] [Category C'] [Category D] [Category D'] [Category E]
    {Q : C ⥤ C'} {R : D ⥤ D'} {F : C ⥤ D} {F' : C' ⥤ D'}
    {H : D ⥤ E} {H' : D' ⥤ E} {G : C ⥤ E} {G' : C' ⥤ E}
    (c : Q ⋙ F' ≅ F ⋙ R) (r : R ⋙ H' ≅ H)
    (a : F ⋙ H ≅ G) (a' : F' ⋙ H' ≅ G') (q : Q ⋙ G' ≅ G) :
    lisseTowerScalarSquareNormalized c r a a' q ↔ normalized c r a a' q := by
  unfold lisseTowerScalarSquareNormalized normalized
  rfl

private theorem fixedRestrictForgetIso_eq
    {C : Type (u + 1)} [Category.{u} C] (J : GrothendieckTopology C)
    {R S : Type (u + 1)} [CommRing R] [CommRing S] (q : R →+* S) :
    lisseTowerFixedRestrictForgetIso J q = fixedRestrictForgetIso J q := rfl

private theorem restrictForgetIso_eq {Z : Scheme.{u}}
    {R S : Sheaf (ProEt.topology Z) CommRingCat.{u + 1}} (a : R ⟶ S) :
    lisseTowerRestrictForgetIso a = restrictForgetIso ((adicLisseForget Z).map a) := rfl

private theorem fixedForgetIso_eq {X Z : Scheme.{u}} (f : Z ⟶ X)
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A) (n : ℕ) :
    lisseTowerFixedForgetIso f d n =
      forgetIso (ProEt.topology Z) (lisseTowerEtaleRing d n) (A ⧸ d.ideal ^ (n + 1))
        (constantAdicQuotientMap d.ideal n)
        ((adicLisseForget Z).obj ((adicTowerInverseImage f).obj
          ((pbcAdicRings X d).obj (op n)))) (lisseTowerFiniteScalarMap f d n) := by
  unfold lisseTowerFixedForgetIso
  exact coefficientForgetIso_eq _ _ _ _ _ _

private theorem scalarSquare_sections {X Z : Scheme.{u}} (f : Z ⟶ X)
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A) (n : ℕ) :
    LisseTowerScalarSquareSections f d n (scalarSquare f d n) := by
  unfold LisseTowerScalarSquareSections
  rw [scalarNormalized_iff]
  rw [fixedForgetIso_eq f d n, fixedForgetIso_eq f d (n + 1)]
  rw [restrictForgetIso_eq, fixedRestrictForgetIso_eq]
  unfold scalarSquare
  exact coefficientScalarIso_normalized (J := ProEt.topology Z)
    (q := lisseTowerEtaleQuotient d n)
    (b := constantAdicQuotientMap d.ideal (n + 1)) (b' := constantAdicQuotientMap d.ideal n)
    (a := (adicLisseForget Z).map ((adicTowerInverseImage f).map
      (pbcAdicQuotient X d (n + 1) n (Nat.le_succ n))))
    (α := lisseTowerFiniteScalarMap f d (n + 1)) (β := lisseTowerFiniteScalarMap f d n)
    (r := Ideal.Quotient.factorPowSucc d.ideal (n + 1))
    (h := completionQuotient_square d n) (ha := finiteScalarMap_square f d n)

attribute [local semireducible] pbcDerivedRestrict

private theorem universal_map_of_mate
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    {L₁ : A ⥤ B} {R₁ : B ⥤ A} {L₂ : C ⥤ D} {R₂ : D ⥤ C}
    {F : A ⥤ C} {G : B ⥤ D}
    (a₁ : L₁ ⊣ R₁) (a₂ : L₂ ⊣ R₂) (s : R₁ ⋙ F ≅ G ⋙ R₂)
    [IsIso ((mateEquiv a₁ a₂).symm s.hom)]
    {E : A} {E' : B} (d : E ⟶ R₁.obj E')
    (h : StructuredArrow.IsUniversal (StructuredArrow.mk d)) :
    Nonempty (StructuredArrow.IsUniversal
      (StructuredArrow.mk (F.map d ≫ s.hom.app E') :
        StructuredArrow (F.obj E) R₂)) := by
  let e := (mkInitialOfLeftAdjoint _ a₁ E).uniqueUpToIso h
  let α : L₁.obj E ≅ E' := (StructuredArrow.proj E R₁).mapIso e
  have hα : a₁.unit.app E ≫ R₁.map α.hom = d := e.hom.w
  let t : L₂.obj (F.obj E) ≅ G.obj E' :=
    asIso (((mateEquiv a₁ a₂).symm s.hom).app E) ≪≫ G.mapIso α
  have ht : a₂.unit.app (F.obj E) ≫ R₂.map t.hom = F.map d ≫ s.hom.app E' := by
    simp only [t, Iso.trans_hom, asIso_hom, Functor.mapIso_hom,
      Functor.map_comp, ← Category.assoc]
    erw [← unit_mateEquiv_symm a₁ a₂ s.hom E, Category.assoc,
      ← s.hom.naturality α.hom]
    dsimp only [Functor.comp_map]
    rw [← Category.assoc, ← F.map_comp, hα]
  let i : (StructuredArrow.mk (a₂.unit.app (F.obj E)) : StructuredArrow (F.obj E) R₂) ≅
      StructuredArrow.mk (F.map d ≫ s.hom.app E') := StructuredArrow.isoMk t ht
  exact ⟨(mkInitialOfLeftAdjoint _ a₂ (F.obj E)).ofIso i⟩

private theorem universal_conjugate
    {A B : Type*} [Category A] [Category B] {R : B ⥤ A}
    {E E' : A} {N N' : B} (d : E ⟶ R.obj N) (d' : E' ⟶ R.obj N')
    (e : E ≅ E') (e' : N ≅ N')
    (he : d ≫ R.map e'.hom = e.hom ≫ d')
    (h : StructuredArrow.IsUniversal (StructuredArrow.mk d' : StructuredArrow E' R)) :
    Nonempty (StructuredArrow.IsUniversal (StructuredArrow.mk d : StructuredArrow E R)) := by
  let k : R ⋙ 𝟭 A ≅ 𝟭 B ⋙ R :=
    Functor.rightUnitor R ≪≫ (Functor.leftUnitor R).symm
  let T : StructuredArrow E' R ⥤ StructuredArrow E R :=
    StructuredArrow.map₂ (F := 𝟭 B) (G := 𝟭 A) e.hom k.hom
  have : T.IsEquivalence := by dsimp only [T]; infer_instance
  have hi := h.isInitialObj T _
  have ht : (T.obj (StructuredArrow.mk d')).hom ≫ R.map e'.inv = d := by
    change (e.hom ≫ d' ≫ k.hom.app N') ≫ R.map e'.inv = d
    simp only [k, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
      Functor.rightUnitor_hom_app, Functor.leftUnitor_inv_app, Category.comp_id]
    rw [← he, Category.assoc, ← R.map_comp, e'.hom_inv_id,
      R.map_id, Category.comp_id]
  exact ⟨hi.ofIso (StructuredArrow.isoMk e'.symm ht)⟩

private theorem restrictedTransition_universal {X Z : Scheme.{u}} (f : Z ⟶ X)
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A) (n : ℕ)
    (M : AdicTower X d) :
    Nonempty (StructuredArrow.IsUniversal (StructuredArrow.mk
      (adicTowerRestrictedTransition d f M (n + 1) n (Nat.le_succ n)) :
        StructuredArrow _ (pbcDerivedRestrict ((adicTowerInverseImage f).map
          (pbcAdicQuotient X d (n + 1) n (Nat.le_succ n)))))) := by
  let a := pbcAdicQuotient X d (n + 1) n (Nat.le_succ n)
  let b := (adicTowerInverseImage f).map a
  let k : pbcDerivedRestrict a ⋙
      adicTowerPullback f ((pbcAdicRings X d).obj (op (n + 1))) ≅
      adicTowerPullback f ((pbcAdicRings X d).obj (op n)) ⋙ pbcDerivedRestrict b :=
    (proEtaleRingRestrictionDerivedPullback f
      ((pbcAdicRings X d).obj (op (n + 1))) ((pbcAdicRings X d).obj (op n))
      ((adicTowerInverseImage f).obj ((pbcAdicRings X d).obj (op (n + 1))))
      ((adicTowerInverseImage f).obj ((pbcAdicRings X d).obj (op n)))
      a b (Iso.refl _) (Iso.refl _)
      ((Category.id_comp _).trans (Category.comp_id _).symm)).symm
  have : IsIso ((mateEquiv (pbcDerivedScalarAdjunction a)
      (pbcDerivedScalarAdjunction b)).symm k.hom) := by
    simpa only [k, b, id, Iso.symm_hom] using inverseImage_mate_isIso f a
  let i : (StructuredArrow.mk ((pbcDerivedScalarAdjunction a).unit.app
      (M.level (n + 1))) : StructuredArrow _ (pbcDerivedRestrict a)) ≅
      StructuredArrow.mk (adicTowerSemilinearTransition X d M.level M.normalization
        (n + 1) n (Nat.le_succ n)) :=
    StructuredArrow.isoMk (M.normalization (n + 1) n (Nat.le_succ n)) rfl
  let h := (mkInitialOfLeftAdjoint _ (pbcDerivedScalarAdjunction a)
    (M.level (n + 1))).ofIso i
  exact universal_map_of_mate (pbcDerivedScalarAdjunction a)
    (pbcDerivedScalarAdjunction b) k _ h

private theorem anyScalarSquare_reflects {X Z : Scheme.{u}} (f : Z ⟶ X)
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A) (n : ℕ)
    (c : LisseTowerScalarSquare f d n) : LisseTowerScalarSquareReflects f d n c := by
  unfold LisseTowerScalarSquareReflects
  intro M C C' hC hC' e e' δ h V
  let q := lisseTowerEtaleQuotient d n
  let a := (adicTowerInverseImage f).map
    (pbcAdicQuotient X d (n + 1) n (Nat.le_succ n))
  let F := lisseTowerFixedRealization f d (n + 1)
  let G := lisseTowerFixedRealization f d n
  let k : normalizationRestrict (ProEt.topology Z) q ⋙ F ≅ G ⋙ pbcDerivedRestrict a :=
    Functor.isoWhiskerLeft (normalizationRestrict (ProEt.topology Z) q)
        (lisseTowerFixedRealizationIso f d (n + 1)).symm ≪≫
      Functor.mapDerivedCategorySquareIso c ≪≫
      Functor.isoWhiskerRight (lisseTowerFixedRealizationIso f d n)
        (pbcRestrict a).mapDerivedCategory
  let δp := (ProEtale.comparisonUpperStar (ModuleCat.{u + 1}
      (lisseTowerEtaleRing d (n + 1))) Z).mapDerivedCategory.map δ ≫
    (localIsomorphismComparisonCoefficients q).hom.app C'
  let T := StructuredArrow.map₂ (R := normalizationRestrict (ProEt.topology Z) q)
    (G := F) (F := G) (R' := pbcDerivedRestrict a)
    (𝟙 ((lisseTowerEtaleRealization f d (n + 1)).obj C)) k.hom
  have ht : F.map δp ≫ k.hom.app
        ((ProEtale.comparisonUpperStar (ModuleCat.{u + 1}
          (lisseTowerEtaleRing d n)) Z).mapDerivedCategory.obj C') ≫
        (pbcDerivedRestrict a).map e'.hom =
      e.hom ≫ adicTowerRestrictedTransition d f M (n + 1) n (Nat.le_succ n) := by
    simpa only [lisseTowerEtaleScalarIso, lisseTowerEtaleRealization, δp, F, k, q, a, id,
      Iso.symm_hom,
      Functor.comp_map,
      Functor.map_comp, Iso.trans_hom, NatTrans.comp_app,
      Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
      Functor.whiskerRight_app, Functor.whiskerLeft_app,
      Functor.associator_hom_app, Functor.associator_inv_app,
      Category.comp_id, Category.id_comp, Category.assoc] using h
  have ht' : Nonempty (StructuredArrow.IsUniversal (T.obj (StructuredArrow.mk δp))) := by
    have hi := universal_conjugate (R := pbcDerivedRestrict a)
      (F.map δp ≫ k.hom.app
        ((ProEtale.comparisonUpperStar (ModuleCat.{u + 1}
          (lisseTowerEtaleRing d n)) Z).mapDerivedCategory.obj C'))
      (adicTowerRestrictedTransition d f M (n + 1) n (Nat.le_succ n)) e e'
      (by simpa only [Category.assoc] using ht) (restrictedTransition_universal f d n M).some
    exact ⟨hi.some.ofIso (StructuredArrow.isoMk (Iso.refl _) (by
      simp only [T, StructuredArrow.map₂_obj_hom, StructuredArrow.mk_hom_eq_self,
        Iso.refl_hom, Category.id_comp, StructuredArrow.mk_right]
      rw [(pbcDerivedRestrict a).map_id, Category.comp_id]))⟩
  have hp : Nonempty (StructuredArrow.IsUniversal
      (StructuredArrow.mk δp : StructuredArrow _
        (normalizationRestrict (ProEt.topology Z) q))) :=
    ⟨ht'.some.isInitialOfObj T _⟩
  exact etaleSourceNormalization_universal Z q δ
    (comparisonNormalization_reflects_universal Z q hC hC' δ hp) V

private theorem constantLocal_universal (Z : Scheme.{u})
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A) (n : ℕ) :
    LisseTowerConstantLocalUniversal Z d n := by
  unfold LisseTowerConstantLocalUniversal
  intro E E' k hk V
  exact etaleSourceNormalization_universal Z (lisseTowerEtaleQuotient d n) _
    (normalizationConstantArrow_isUniversal Z.smallEtaleTopology _ k hk) V

private theorem scalarSquareNormalized_unique
    {C C' D D' E : Type*} [Category C] [Category C'] [Category D] [Category D'] [Category E]
    {Q : C ⥤ C'} {R : D ⥤ D'} {F : C ⥤ D} {F' : C' ⥤ D'}
    {H : D ⥤ E} {H' : D' ⥤ E} [H'.Faithful] {G : C ⥤ E} {G' : C' ⥤ E}
    (c c' : Q ⋙ F' ≅ F ⋙ R) (r : R ⋙ H' ≅ H)
    (a : F ⋙ H ≅ G) (a' : F' ⋙ H' ≅ G') (q : Q ⋙ G' ≅ G)
    (hc : lisseTowerScalarSquareNormalized c r a a' q)
    (hc' : lisseTowerScalarSquareNormalized c' r a a' q) : c = c' := by
  unfold lisseTowerScalarSquareNormalized at hc hc'
  apply Iso.ext
  ext X
  apply H'.map_injective
  have h := congrArg (fun t ↦ t.app X) (hc.trans hc'.symm)
  dsimp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.whiskerRight_app] at h
  exact (cancel_mono _).mp h

/-- The consecutive fixed-realization square is uniquely normalized on sections and
reflects the universality of an actual normalized transition. This is a single
coefficient-change statement; it constructs neither a descended arrow nor any
realization or marking on further pro-etale objects. -/
theorem lisseTower_scalar_restriction {X Z : Scheme.{u}} (f : Z ⟶ X)
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A) (n : ℕ) :
    ∃! c : LisseTowerScalarSquare f d n,
      LisseTowerScalarSquareSections f d n c ∧ LisseTowerScalarSquareReflects f d n c ∧
        LisseTowerConstantLocalUniversal Z d n := by
  refine ⟨scalarSquare f d n,
    ⟨scalarSquare_sections f d n, anyScalarSquare_reflects f d n _,
      constantLocal_universal Z d n⟩, ?_⟩
  intro c hc
  apply scalarSquareNormalized_unique c (scalarSquare f d n)
    (lisseTowerRestrictForgetIso ((adicTowerInverseImage f).map
      (pbcAdicQuotient X d (n + 1) n (Nat.le_succ n))))
    (lisseTowerFixedForgetIso f d n) (lisseTowerFixedForgetIso f d (n + 1))
    (lisseTowerFixedRestrictForgetIso (ProEt.topology Z) (lisseTowerEtaleQuotient d n))
  · have hs := hc.1
    unfold LisseTowerScalarSquareSections at hs
    exact hs
  · have hs := scalarSquare_sections f d n
    unfold LisseTowerScalarSquareSections at hs
    exact hs

end AlgebraicGeometry.Scheme
