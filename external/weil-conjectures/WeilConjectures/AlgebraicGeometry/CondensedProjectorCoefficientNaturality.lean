/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.CondensedArtinSchreier
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.ContinuousMapGlobalSections
public import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalarsRegularEnd
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.UnitCoherence

/-! Naturality of the condensed Artin–Schreier character projector under coefficients.

Source: latest blueprint, lemma-fourier-transform-constant-sheaf proof, coefficient paragraph
(blueprint: lem-fd-unit-punctured-kernel-coefficient-comparison).
-/
@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale
set_option allowUnsafeReducibility true in
attribute [local reducible] condensedArtinSchreierPushforward Mod.extendScalars

/-- Coefficient maps commute with the `eqToHom` between equal pushforwards. -/
private theorem coefficientCongr
    {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj Λ] [MonObj Λ'] (a : Λ ⟶ Λ')
    {X Y : Scheme.{u}} {f g : X ⟶ Y} (h : f = g) :
    (eqToHom (congrArg (fun t ↦ (CondensedRing.lowerStar Λ t).obj
      (Mod.regular (condensedRingObj Λ X))) h)).hom ≫
        (ProEtale.lowerStar Ab.{u + 1} g).map (coefficientMap a X) =
      (ProEtale.lowerStar Ab.{u + 1} f).map (coefficientMap a X) ≫
        (eqToHom (congrArg (fun t ↦ (CondensedRing.lowerStar Λ' t).obj
          (Mod.regular (condensedRingObj Λ' X))) h)).hom := by
  subst g
  simp only [eqToHom_refl, Mod.id_hom', Category.id_comp]
  erw [Category.comp_id]

/-- The underlying object of the monoidal unit module is the coefficient ring. -/
private theorem unitUnderlying
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (X : Scheme.{u}) :
    (𝟙_ (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X))).X = condensedRingObj Λ X := rfl

-- Explicit coefficient and module-object coercions require additional elaboration.
/-- Deck translations commute with the coefficient map on pushforwards. -/
private theorem translationCoefficient
    {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj Λ] [IsCommMonObj Λ] [MonObj Λ'] [IsCommMonObj Λ']
    (a : Λ ⟶ Λ') [IsMonHom a] (k : Type u) [Field k] [Fintype k] (c : k) :
    (condensedArtinSchreierTranslationAction Λ k c).asHom.hom ≫
        (ProEtale.lowerStar Ab.{u + 1}
          (AffineSpace.artinSchreierMap PUnit (Spec (.of k)) (Fintype.card k))).map
            (coefficientMap a (AffineSpace PUnit (Spec (.of k)))) =
      (ProEtale.lowerStar Ab.{u + 1}
        (AffineSpace.artinSchreierMap PUnit (Spec (.of k)) (Fintype.card k))).map
          (coefficientMap a (AffineSpace PUnit (Spec (.of k)))) ≫
        (condensedArtinSchreierTranslationAction Λ' k c).asHom.hom := by
  unfold condensedArtinSchreierTranslationAction
  simp only [Mod.comp_hom', CondensedRing.lowerStar_map_hom, Category.assoc]
  erw [CondensedRing.homEquiv_εIso_inv_hom Λ (Etale.artinSchreierTranslation k c),
    CondensedRing.homEquiv_εIso_inv_hom Λ' (Etale.artinSchreierTranslation k c)]
  rw [coefficientCongr a (Etale.artinSchreierTranslation_comp_artinSchreierMap k c)]
  rw [CondensedRing.lowerStarComp_hom_app_hom,
    CondensedRing.lowerStarComp_hom_app_hom]
  rw [← NatTrans.naturality_assoc]
  simp only [Functor.comp_map]
  rw [← Functor.map_comp_assoc,
    condensedPushforwardHom_comp_map_coefficientMap a (Etale.artinSchreierTranslation k c),
    Functor.map_comp]
  simp only [Category.assoc, unitUnderlying]

/-- Multiplication by a global section commutes with a monoid-object morphism. -/
private theorem regularCoefficient
    {C : Type*} [Category* C] [MonoidalCategory C] [Preadditive C]
    [MonoidalPreadditive C] [BraidedCategory C]
    {R S : C} [MonObj R] [IsCommMonObj R] [MonObj S] [IsCommMonObj S]
    (a : R ⟶ S) [IsMonHom a] (s : MonObj.Γ R) :
    (Mod.regularEndRingHom s).asHom.hom ≫ a =
      a ≫ (Mod.regularEndRingHom (MonObj.Γ.map a s)).asHom.hom := by
  have h : (Mod.regularEndRingHom s).asHom ≫ Mod.regularHomComap a =
      Mod.regularHomComap a ≫ (Mod.comap a).map
        (Mod.regularEndRingHom (MonObj.Γ.map a s)).asHom := by
    apply Mod.regular_hom_ext
    change (MonObj.one : 𝟙_ C ⟶ R) ≫ ((Mod.regularEndRingHom s).asHom.hom ≫ a) =
      (MonObj.one : 𝟙_ C ⟶ R) ≫
        (a ≫ (Mod.regularEndRingHom (MonObj.Γ.map a s)).asHom.hom)
    rw [← Category.assoc, ← Category.assoc, IsMonHom.one_hom (f := a)]
    erw [Mod.regularEndRingHom_apply, Mod.one_comp_regularLift_regular,
      Mod.regularEndRingHom_apply, Mod.one_comp_regularLift_regular]
    rfl
  exact congrArg Mod.Hom.hom h

/-- A ring map sends the `Ring.inverse` of a unit to the `Ring.inverse` of its image. -/
private theorem mapRingInverse
    {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) {r : R} (h : IsUnit r) :
    f (Ring.inverse r) = Ring.inverse (f r) := by
  obtain ⟨v, rfl⟩ := h
  have hi := Ring.inverse_unit (v.map f.toMonoidHom)
  rw [Ring.inverse_unit]
  exact hi.symm

/-- Coefficient maps commute with global sections pulled back from the point. -/
private theorem coefficientSection
    {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj Λ] [IsCommMonObj Λ] [MonObj Λ'] [IsCommMonObj Λ']
    (a : Λ ⟶ Λ') [IsMonHom a] (X : Scheme.{u}) (s : MonObj.Γ Λ) :
    MonObj.Γ.map (coefficientMap a X)
        (MonObj.Γ.mapFunctorMonoidHom (upperStarFromPoint X) s) =
      MonObj.Γ.mapFunctorMonoidHom (upperStarFromPoint X) (MonObj.Γ.map a s) := by
  ext
  simp only [MonObj.Γ.map_hom, MonObj.Γ.mapFunctorMonoidHom_hom,
    coefficientMap, Category.assoc, ← Functor.map_comp]

/-- The underlying morphism of a finite sum of module morphisms is the sum. -/
private theorem sumUnderlying
    {C : Type*} [Category* C] [MonoidalCategory C] [Preadditive C]
    [MonoidalPreadditive C] {R : C} [MonObj R] {M N : Mod C R}
    {I : Type*} [Fintype I] (f : I → (M ⟶ N)) :
    (∑ i, f i).hom = ∑ i, (f i).hom :=
  (Mod.forget R).map_sum f Finset.univ

/-- The Artin–Schreier character projector commutes with a coefficient map when the finite-field
cardinality is a unit in the source coefficient ring. -/
theorem condensed_projector_coefficient_naturality
    {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj Λ] [IsCommMonObj Λ] [MonObj Λ'] [IsCommMonObj Λ']
    (a : Λ ⟶ Λ') [IsMonHom a] (k : Type u) [Field k] [Fintype k]
    (hq : IsUnit (Fintype.card k : MonObj.Γ Λ))
    (ψ : AddChar k (MonObj.Γ Λ)) :
    (condensedArtinSchreierProjector Λ k ψ).asHom.hom ≫
        (ProEtale.lowerStar Ab.{u + 1}
          (AffineSpace.artinSchreierMap PUnit (Spec (.of k)) (Fintype.card k))).map
            (coefficientMap a (AffineSpace PUnit (Spec (.of k)))) =
      (ProEtale.lowerStar Ab.{u + 1}
        (AffineSpace.artinSchreierMap PUnit (Spec (.of k)) (Fintype.card k))).map
          (coefficientMap a (AffineSpace PUnit (Spec (.of k)))) ≫
        (condensedArtinSchreierProjector Λ' k
          ((MonObj.Γ.map a).toMonoidHom.compAddChar ψ)).asHom.hom := by
  unfold condensedArtinSchreierProjector
  simp only [End.sum_asHom]
  rw [sumUnderlying, sumUnderlying, Preadditive.sum_comp, Preadditive.comp_sum]
  refine Finset.sum_congr rfl fun c _ ↦ ?_
  simp only [Mod.comp_hom', CondensedRing.lowerStar_map_hom, Category.assoc]
  rw [← Functor.map_comp, regularCoefficient, coefficientSection, Functor.map_comp,
    ← Category.assoc, translationCoefficient, Category.assoc]
  congr 4
  rw [map_mul, mapRingInverse _ hq, map_natCast]
  rfl

end AlgebraicGeometry.ProEtale
