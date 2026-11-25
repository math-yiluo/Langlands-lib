/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SystemProjection.EtaleSystemProjectionData
import all WeilConjectures.AlgebraicGeometry.Etale.Proper.EtaleProperCoefficientTensorUnit
import all WeilConjectures.AlgebraicGeometry.Finite.Coefficient.FiniteCoefficientDirectImage
import WeilConjectures.AlgebraicGeometry.Etale.Open.EtaleOpenScalarCoherence
import all WeilConjectures.AlgebraicGeometry.Etale.Compact.EtaleCompactScalarCoherence
import all WeilConjectures.AlgebraicGeometry.Etale.Open.EtaleOpenScalarExchange
import all WeilConjectures.AlgebraicGeometry.EtaleRestrictScalarsAdjunctionIdentities
import all WeilConjectures.AlgebraicGeometry.Etale.Open.EtaleOpenTensorDefs
import WeilConjectures.SixFunctors.Etale.Derived.CoefficientChangeOpenImmersionSheaf

/-! # Single-ring normalization and coefficient cocycle

Source: Zheng, Constructions 4.1 and 5.14--5.15, Lemma 5.16; Stacks Tag 0GL6.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Etale.SystemProjection

attribute [local instance] cachedEtaleGroth cachedEtaleSheafify
attribute [local instance] cachedEtaleMonoidalPreadditive cachedEtaleCoproducts
  cachedEtaleColimits cachedEtaleFlatResolution cachedEtaleInjectiveResolution
  cachedEtaleExactColimits cachedEtaleTensor4 cachedEtaleTensor12 cachedEtaleTensor23
  cachedEtaleTensorColimits cachedEtaleTensorFlipColimits

private theorem single_open_eq
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B)
    {U T : Scheme.{u}} (j : U ⟶ T) [IsOpenImmersion j] :
    ExceptionalCoefficients.openIso φ j = openScalarExtension φ j := by
  suffices h : (ExceptionalCoefficients.openIso φ j).symm =
      (openScalarExtension φ j).symm from congrArg Iso.symm h
  apply Iso.ext
  ext M
  change (ExceptionalCoefficients.openIso φ j).inv.app M =
    (openScalarExtension φ j).inv.app M
  rw [compactScalarOpen_normalization]
  let adj := derivedOpenImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} B) j
  apply (adj.homEquiv _ _).injective
  unfold properOpenCoefficientOpenInverse
  rw [Equiv.apply_symm_apply]
  simpa only [Adjunction.homEquiv_unit, adj] using (scalarOpen_unit φ j M).symm

private theorem single_inverse_restriction_eq
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B)
    {T X : Scheme.{u}} (f : T ⟶ X) :
    upperStarRestrictScalarsIsoSheaf φ f = upperStarRestrictScalarsIso φ f := by
  apply Iso.ext
  apply (conjugateEquiv
    ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} B) f).comp
      (Sheaf.restrictCoextendScalarsAdj T.smallEtaleTopology φ))
    ((Sheaf.restrictCoextendScalarsAdj X.smallEtaleTopology φ).comp
      (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f))).injective
  rw [conjugateEquiv_upperStarRestrictScalarsIso_hom]
  simp only [upperStarRestrictScalarsIsoSheaf, Adjunction.leftAdjointUniq,
    Iso.symm_hom, conjugateIsoEquiv_symm_apply_inv, Iso.refl_inv]
  exact (conjugateEquiv _ _).apply_symm_apply _

private theorem single_pullback_eq
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B)
    {T X : Scheme.{u}} (f : T ⟶ X) :
    ProEtale.scalarPullbackEtaleIso φ f = scalarPullbackIso φ f := rfl

private theorem single_proper_chain
    {A B D : CommRingCat.{u + 1}} (a : A ⟶ B) (b : B ⟶ D)
    {X Y : Scheme.{u}} (f : X ⟶ Y) (M : DerivedCategoryModule A X) :
    (scalarMate (a ≫ b).hom f).app M =
      (ProEtale.pbcFixedScalarExtensionComp Y.smallEtaleTopology
        a.hom b.hom (a ≫ b).hom rfl).inv.app
          ((lowerStar (ModuleCat.{u + 1} A) f).rightDerivedFunctor.obj M) ≫
      (scalarExtension b.hom Y).map ((scalarMate a.hom f).app M) ≫
      (scalarMate b.hom f).app ((scalarExtension a.hom X).obj M) ≫
      (lowerStar (ModuleCat.{u + 1} D) f).rightDerivedFunctor.map
        ((ProEtale.pbcFixedScalarExtensionComp X.smallEtaleTopology
          a.hom b.hom (a ≫ b).hom rfl).hom.app M) := by
  simpa only [finiteCoefficientDirectImageMap_eq_mate, single_pullback_eq, scalarMate,
    scalarExtension, CommRingCat.hom_comp] using
    finiteCoefficientDirectImageMap_coefficientChain a.hom b.hom f M

private theorem single_open_mate
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B)
    {X Z : Scheme.{u}} (j : X ⟶ Z) [IsOpenImmersion j] :
    ((mateEquiv
      (derivedOpenImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} B) j)
      (derivedOpenImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) j))
      (TwoSquare.mk _ _ _ _
        (derivedRestrictScalarsCompOpenImmersionLowerShriekIso φ j).hom)) =
      (openDerivedRestrictScalarsIso φ j).hom := by
  apply mateEquiv_eq_of_unit
  intro K
  let τ := (upperStarRestrictScalarsIsoSheaf.{u} φ j).symm
  let β := openImmersionLowerShriekRestrictScalarsIso.{u} φ j
  have h := Adjunction.mapDerivedCategoryAdjunction_mate.{u + 2, u + 2, u + 2, u + 2,
      u + 1, u + 1, u + 1, u + 1, u + 1, u + 1, u + 1, u + 1}
    (C₁ := Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B))
    (D₁ := Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} B))
    (C₂ := Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))
    (D₂ := Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} A))
    (openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} B) j)
    (openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) j)
    τ β
    (fun (G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B)) ↦ by
      have h := openImmersionLowerShriekUpperStarAdjunction_unit_app_comp_upperStarMap
        φ j G
      have hh := congrArg (fun z ↦ z ≫
        (upperStarRestrictScalarsIso φ j).inv.app
          ((openImmersionLowerShriek (ModuleCat.{u + 1} B) j).obj G)) h
      simp only [Category.assoc, Iso.hom_inv_id_app] at hh
      erw [Category.comp_id] at hh
      simpa only [τ, β, Iso.symm_hom, single_inverse_restriction_eq] using hh) K
  have he : (openRestrictScalarsIso φ j).symm =
      upperStarRestrictScalarsIsoSheaf φ j := Iso.ext (openRestrictScalarsIso_inv_eq φ j)
  have he' := congrArg Iso.symm he
  simp only [Iso.symm_symm_eq] at he'
  change _ = _ at h
  have he'' : Functor.mapDerivedCategorySquareIso τ =
      openDerivedRestrictScalarsIso φ j := by
    dsimp only [openDerivedRestrictScalarsIso, τ]
    rw [← he']
  rw [he''] at h
  exact h.symm

private theorem single_open_unit
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B)
    {X Z : Scheme.{u}} (j : X ⟶ Z) [IsOpenImmersion j]
    (M : DerivedCategoryModule A X) :
    (Adjunction.ofIsRightAdjoint
        (Sheaf.derivedRestrictScalars Z.smallEtaleTopology φ)).unit.app
        ((openImmersionLowerShriek (ModuleCat.{u + 1} A) j).mapDerivedCategory.obj M) ≫
      (Sheaf.derivedRestrictScalars Z.smallEtaleTopology φ).map
        ((ExceptionalCoefficients.openIso φ j).hom.app M) =
    (openImmersionLowerShriek (ModuleCat.{u + 1} A) j).mapDerivedCategory.map
        ((Adjunction.ofIsRightAdjoint
          (Sheaf.derivedRestrictScalars X.smallEtaleTopology φ)).unit.app M) ≫
      (derivedRestrictScalarsCompOpenImmersionLowerShriekIso φ j).hom.app
        ((scalarExtension φ X).obj M) := by
  let a := derivedOpenImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) j
  let b := derivedOpenImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} B) j
  let x := Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars X.smallEtaleTopology φ)
  let z := Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars Z.smallEtaleTopology φ)
  let q := openDerivedRestrictScalarsIso φ j
  let β := openScalarExtension φ j
  let d := derivedRestrictScalarsCompOpenImmersionLowerShriekIso φ j
  have hc : conjugateEquiv (x.comp b) (a.comp z) β.hom = q.hom := by
    apply conjugateEquiv_eq_of_unit
    intro K
    exact (Adjunction.unit_leftAdjointUniq_hom_app
      (a.comp z) ((x.comp b).ofNatIsoRight q) K).symm
  have hm := iterated_mateEquiv_conjugateEquiv x z a b
    (TwoSquare.mk _ _ _ _ β.hom)
  have hd : (mateEquiv b a (TwoSquare.mk _ _ _ _ d.hom)) = q.hom :=
    single_open_mate φ j
  have hh : mateEquiv x z (TwoSquare.mk _ _ _ _ β.hom) =
      TwoSquare.mk _ _ _ _ d.hom := by
    apply (mateEquiv b a).injective
    refine NatTrans.ext (funext fun K ↦ ?_)
    exact congrArg (fun e ↦ e.app K) (hm.trans (hc.trans hd.symm))
  have h := unit_mateEquiv x z (TwoSquare.mk _ _ _ _ β.hom) M
  change _ ≫ (mateEquiv x z (TwoSquare.mk _ _ _ _ β.hom)).app _ = _ at h
  rw [hh] at h
  rw [single_open_eq]
  exact h.symm

private theorem single_transpose_forward
    {A B : CommRingCat.{u + 1}} (a : A ⟶ B)
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (M : DerivedCategoryModule A X) :
    (Adjunction.ofIsRightAdjoint
        (Sheaf.derivedRestrictScalars Y.smallEtaleTopology a.hom)).homEquiv
        _ _ ((compactScalarMap a.hom c).app M) ≫
      (singleRestriction a c).app ((scalarExtension a.hom X).obj M) =
    (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c).map
      ((Adjunction.ofIsRightAdjoint
        (Sheaf.derivedRestrictScalars X.smallEtaleTopology a.hom)).unit.app M) := by
  rw [Adjunction.homEquiv_unit]
  dsimp only [compactScalarMap, ExceptionalCoefficients.compactSupportMap,
    singleRestriction, rightDerivedLowerShriekOfCompactification, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.comp_map, Functor.comp_obj]
  simp only [Functor.map_comp, Category.assoc]
  have hn := (scalarRestrictionDirectImageMap a.hom c.g).naturality
    ((ExceptionalCoefficients.openIso a.hom c.i).hom.app M)
  dsimp only [Functor.comp_map, Functor.comp_obj] at hn
  rw [reassoc_of% hn]
  have hu := scalar_unit_directImage a.hom c.g
    ((openImmersionLowerShriek (ModuleCat.{u + 1} A) c.i).mapDerivedCategory.obj M)
  change (Adjunction.ofIsRightAdjoint
    (Sheaf.derivedRestrictScalars Y.smallEtaleTopology a.hom)).unit.app
      ((lowerStar (ModuleCat.{u + 1} A) c.g).rightDerivedFunctor.obj
        ((openImmersionLowerShriek (ModuleCat.{u + 1} A) c.i).mapDerivedCategory.obj M)) ≫
    (Sheaf.derivedRestrictScalars Y.smallEtaleTopology a.hom).map
      ((scalarMate a.hom c.g).app _) ≫
    (scalarRestrictionDirectImageMap a.hom c.g).app _ ≫ _ = _
  rw [reassoc_of% hu]
  rw [← Functor.map_comp_assoc, single_open_unit]
  rw [Functor.map_comp]
  simp only [Category.assoc, ← Functor.map_comp, Iso.hom_inv_id_app]
  congr 1
  erw [Category.comp_id]

private theorem single_coefficient_chain
    {A B D : CommRingCat.{u + 1}} (a : A ⟶ B) (b : B ⟶ D)
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) :
    compactScalarMap (a ≫ b).hom c = singlePath a b c := by
  ext M
  dsimp only [compactScalarMap, ExceptionalCoefficients.compactSupportMap,
    singlePath, rightDerivedLowerShriekOfCompactification, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.comp_map]
  simp only [Functor.map_comp, Category.assoc]
  have hn := (scalarMate b.hom c.g).naturality
    ((ExceptionalCoefficients.openIso a.hom c.i).hom.app M)
  dsimp only [Functor.comp_map, Functor.comp_obj] at hn
  rw [reassoc_of% hn]
  have ho := (etaleOpenScalarComparisons a.hom c.i).successive_scalar b.hom M
  simp only [← single_open_eq] at ho
  change (scalarExtension b.hom c.Z).map
    ((ExceptionalCoefficients.openIso a.hom c.i).hom.app M) ≫
    (ExceptionalCoefficients.openIso b.hom c.i).hom.app
      ((scalarExtension a.hom X).obj M) ≫
    (openImmersionLowerShriek (ModuleCat.{u + 1} D) c.i).mapDerivedCategory.map
      ((ProEtale.pbcFixedScalarExtensionComp X.smallEtaleTopology
        a.hom b.hom (a ≫ b).hom rfl).hom.app M) = _ at ho
  have ho' := congrArg ((lowerStar (ModuleCat.{u + 1} D) c.g).rightDerivedFunctor.map) ho
  simp only [Functor.map_comp] at ho'
  rw [ho']
  rw [single_proper_chain]
  simp only [Category.assoc, CommRingCat.hom_comp, derivedExtension, Functor.comp_obj]

/-- The ordinary coefficient projection has its restriction adjunct and scalar cocycle.
Source: Zheng Construction 2.26, Lemma 5.16; Stacks Tag 0GL6
(blueprint: lem-pur-etale-single-coefficient-projection).

Proof: The proper restriction comparison is invertible by uniqueness of the right
adjoint to the common composite inverse image. The open restriction comparison is
an isomorphism on sheaves, and both functors are exact. Paste these isomorphisms to
obtain d with the stated hom. Transpose the proper coefficient map through the
scalar adjunction: the two geometric/scalar mate operations commute, so its
transpose is proper image of the scalar unit followed by inverse restriction.
For the open factor use the open-unit normalization of its scalar balancing map.
Naturality pastes the resulting transpose formulas, proving the first assertion.
For three rings, identify the normalized proper scalar mate with the existing
finiteCoefficientDirectImageMap and apply its coefficient-chain theorem. Apply
etaleOpenScalarComparisons.successive_scalar to the open factor, using the open-unit
normalization to identify its comparison with ExceptionalCoefficients.openIso.
Naturality of the proper scalar mate pastes these two coefficient-chain equations.
The resulting word is exactly singlePath, with its published balanced associators. -/
theorem etaleSingleCoefficientProjection
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) (l : ℕ) :
    (∀ (A B : CommRingCat.{u + 1}) (_hA : Finite A) (_hB : Finite B)
        (_htA : ∃ m : ℕ, (l ^ m : A) = 0) (_htB : ∃ m : ℕ, (l ^ m : B) = 0)
        (a : A ⟶ B),
        ∃ d : rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} B) c ⋙
            Sheaf.derivedRestrictScalars Y.smallEtaleTopology a.hom ≅
          Sheaf.derivedRestrictScalars X.smallEtaleTopology a.hom ⋙
            rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c,
          d.hom = singleRestriction a c ∧
          ∀ M : DerivedCategoryModule A X,
            (Adjunction.ofIsRightAdjoint
              (Sheaf.derivedRestrictScalars Y.smallEtaleTopology a.hom)).homEquiv
                _ _ ((compactScalarMap a.hom c).app M) =
              (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c).map
                ((Adjunction.ofIsRightAdjoint
                  (Sheaf.derivedRestrictScalars X.smallEtaleTopology a.hom)).unit.app M) ≫
                d.inv.app ((scalarExtension a.hom X).obj M)) ∧
    (∀ (A B D : CommRingCat.{u + 1}) (_hA : Finite A) (_hB : Finite B)
        (_hD : Finite D) (_htA : ∃ m : ℕ, (l ^ m : A) = 0)
        (_htB : ∃ m : ℕ, (l ^ m : B) = 0) (_htD : ∃ m : ℕ, (l ^ m : D) = 0)
        (a : A ⟶ B) (b : B ⟶ D),
        compactScalarMap (a ≫ b).hom c = singlePath a b c) := by
  constructor
  · intro A B _ _ _ _ a
    have := scalar_directImage_isIso a.hom c.g
    have hd : IsIso (singleRestriction a c) := by
      dsimp only [singleRestriction]
      infer_instance
    let d := asIso (singleRestriction a c)
    refine ⟨d, rfl, ?_⟩
    intro M
    apply (Iso.eq_comp_inv (d.app ((scalarExtension a.hom X).obj M))).2
    exact single_transpose_forward a c M
  · intro A B D _ _ _ _ _ _ a b
    exact single_coefficient_chain a b c

end AlgebraicGeometry.Etale.SystemProjection
