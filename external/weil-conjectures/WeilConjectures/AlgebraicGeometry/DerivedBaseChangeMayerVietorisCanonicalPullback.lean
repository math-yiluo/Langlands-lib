/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedBaseChangeMayerVietorisCanonicalData
import all WeilConjectures.AlgebraicGeometry.DerivedMayerVietorisFunctorial
import WeilConjectures.AlgebraicGeometry.DerivedBaseChangeOpenTranspose

/-! Canonical compatibility for relative Mayer--Vietoris.
Source: Stacks Project, Tags 08BV, 08HY and 0DJ9. -/

@[expose] public section
universe u w v u' v'
open CategoryTheory CategoryTheory.Limits TopologicalSpace Pretriangulated
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace AlgebraicGeometry

attribute [local instance 2000] schemeMVModuleAbelian


private theorem boundary_pullback_of_transpose
    {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
    [HasShift C ℤ] [HasShift D ℤ]
    (L : C ⥤ D) (R : D ⥤ C) [L.CommShift ℤ] [R.CommShift ℤ]
    (a : L ⊣ R) {A K : C} {B K' : D}
    (δ : A ⟶ K⟦(1 : ℤ)⟧) (δ' : B ⟶ K'⟦(1 : ℤ)⟧)
    (ψ : L.obj K ⟶ K') (t : L.obj A ⟶ B)
    (T : C) (c : R.obj B ≅ T) (h : A ⟶ T) (ε : T ⟶ (R.obj K')⟦(1 : ℤ)⟧)
    (hshift : (a.homEquiv K K' ψ)⟦(1 : ℤ)⟧' =
      a.homEquiv (K⟦(1 : ℤ)⟧) (K'⟦(1 : ℤ)⟧)
        ((L.commShiftIso (1 : ℤ)).hom.app K ≫ ψ⟦(1 : ℤ)⟧') ≫
          (R.commShiftIso (1 : ℤ)).hom.app K')
    (hnat : δ ≫ (a.homEquiv K K' ψ)⟦(1 : ℤ)⟧' = h ≫ ε)
    (himage : R.map δ' ≫ (R.commShiftIso (1 : ℤ)).hom.app K' = c.hom ≫ ε)
    (hmate : a.homEquiv A B t = h ≫ c.inv) :
    L.map δ ≫ (L.commShiftIso (1 : ℤ)).hom.app K ≫ ψ⟦(1 : ℤ)⟧' = t ≫ δ' := by
  apply (a.homEquiv A (K'⟦(1 : ℤ)⟧)).injective
  apply (cancel_mono ((R.commShiftIso (1 : ℤ)).hom.app K')).mp
  rw [a.homEquiv_naturality_left δ (_ ≫ _),
    a.homEquiv_naturality_right t δ', hmate]
  simp only [Category.assoc]
  rw [← hshift, himage, Iso.inv_hom_id_assoc]
  exact hnat

variable [∀ Y : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]

private theorem canonical_boundary_eq (X : Scheme.{u}) (U V : X.Opens)
    (hcover : U ⊔ V = ⊤) (K : schemeDerivedCategory X) :
    mvCanonicalBoundary X U V (U ⊓ V) rfl hcover K =
      schemeMVBoundary X U V hcover K := by
  unfold mvCanonicalBoundary mvCanonicalOpenComparison schemeMVBoundary
  simp only [Iso.trans_inv, Functor.mapIso_inv, Category.assoc]
  unfold mvOpenRestrictionAdjunction
  rfl

-- Fixed-resolution transport uses nested derived comparisons.
private theorem canonical_boundary_naturality (X : Scheme.{u}) (U V : X.Opens)
    (hcover : U ⊔ V = ⊤) (K L : schemeDerivedCategory X) (φ : K ⟶ L) :
    mvCanonicalBoundary X U V (U ⊓ V) rfl hcover K ≫ φ⟦(1 : ℤ)⟧' =
      (schemeDerivedDirectImage (U ⊓ V).ι).map
        ((schemeOpenRestriction X (U ⊓ V)).mapDerivedCategory.map φ) ≫
          mvCanonicalBoundary X U V (U ⊓ V) rfl hcover L := by
  rw [canonical_boundary_eq, canonical_boundary_eq]
  exact (canonicalMV_spec X U V hcover).2 K L φ

/-- Naturality of the concrete SES boundary under pullback to the inverse-image
cover, before applying any further direct image. All shifts and SES comparisons
are the fixed constructions, and the overlap morphism is the pinned open mate.
Source: Stacks Tags 08BV, 08HY and 0DJ9, relative Mayer--Vietoris diagram.
(blueprint: lem-pc-rf-mv-canonical-boundary-pullback).

Proof: represent K by schemeMVResolution and transpose ψ under the pinned
Lg'^* / Rg'_* adjunction. Compute Rg'_*K' using the fixed K-injective resolution
of K', followed by a K-injective replacement of its direct-image complex. A
chain map represents the transposed derived morphism into this replacement.
Restrict it to U, V and their intersection. These restrictions give a morphism
of the concrete short exact Mayer--Vietoris sequences. The direct-image sequence
of the target cover is termwise split: the first term is injective in each degree,
so its monomorphism splits. Applying direct image preserves this splitting.
All three target complexes are K-injective: the first is the fixed resolution;
open restriction preserves K-injectivity by lem-sc-derived-k-injective-restrict-open;
open direct image preserves it by lem-weil-pbc-right-adjoint-preserves-kinjective
because its left adjoint, open restriction, is exact; and finite biproducts preserve
it by additivity of Hom from acyclic complexes.
Consequently its SES boundary computes Rg'_* of the target SES boundary with
the existing right-derived shift. Apply triangleOfSESδ_naturality and transport
by the fixed resolution and open comparisons. On sections, inverse-image cover
restriction agrees with restricting the direct image, so the overlap comparison
is the mate of the pinned pullback/open-restriction comparison; its unit/counit
identities identify the third component with the displayed overlap map. Transpose
back under the pinned g' adjunction. mvCanonicalHomEquiv_shift gives precisely
the constructed pullback shift. This proves the equation on X', without f or f'.
For empty or repeated opens the same SES and chain-map construction applies. -/
theorem mvCanonicalBoundary_pullback
    {X X' : Scheme.{u}} (g' : X' ⟶ X)
    (K : schemeDerivedCategory X) (K' : schemeDerivedCategory X')
    (ψ : (derivedPullback g').obj K ⟶ K')
    (U V : X.Opens) (hcover : U ⊔ V = ⊤) :
    letI := mvCanonicalPullbackShift g'
    let δ := mvCanonicalBoundary X U V (U ⊓ V) rfl hcover K
    let δ' := mvCanonicalBoundary X' (g' ⁻¹ᵁ U) (g' ⁻¹ᵁ V) (g' ⁻¹ᵁ (U ⊓ V))
      (Scheme.Hom.preimage_inf g').symm
      (by rw [← Scheme.Hom.preimage_sup, hcover, Scheme.Hom.preimage_top]) K'
    (derivedPullback g').map δ ≫
        ((derivedPullback g').commShiftIso (1 : ℤ)).hom.app K ≫ ψ⟦(1 : ℤ)⟧' =
      (schemeDerivedBaseChangeMap (U ⊓ V).ι (g' ⁻¹ᵁ (U ⊓ V)).ι g'
          (g'.resLE (U ⊓ V) (g' ⁻¹ᵁ (U ⊓ V)) le_rfl)
          (Scheme.Hom.resLE_comp_ι g' le_rfl)
          ((schemeOpenRestriction X (U ⊓ V)).mapDerivedCategory.obj K) ≫
        (schemeDerivedDirectImage (g' ⁻¹ᵁ (U ⊓ V)).ι).map
          ((mvPullbackOpenRestrictionIso g' (U ⊓ V)).inv.app K ≫
            (schemeOpenRestriction X' (g' ⁻¹ᵁ (U ⊓ V))).mapDerivedCategory.map ψ)) ≫ δ' := by
  let := mvCanonicalPullbackShift g'
  let R := schemeDerivedDirectImage g'
  let a := mvDerivedPullbackAdjunction g'
  let W := U ⊓ V
  let H := (schemeOpenRestriction X W).mapDerivedCategory ⋙ schemeDerivedDirectImage W.ι
  let α := a.homEquiv K K' ψ
  let δ := mvCanonicalBoundary X U V W rfl hcover K
  have hcover' : (g' ⁻¹ᵁ U) ⊔ (g' ⁻¹ᵁ V) = ⊤ := by
    rw [← Scheme.Hom.preimage_sup, hcover, Scheme.Hom.preimage_top]
  let δ' := mvCanonicalBoundary X' (g' ⁻¹ᵁ U) (g' ⁻¹ᵁ V) (g' ⁻¹ᵁ W)
    (Scheme.Hom.preimage_inf g').symm hcover' K'
  let t := schemeDerivedBaseChangeMap W.ι (g' ⁻¹ᵁ W).ι g'
      (g'.resLE W (g' ⁻¹ᵁ W) le_rfl) (Scheme.Hom.resLE_comp_ι g' le_rfl)
      ((schemeOpenRestriction X W).mapDerivedCategory.obj K) ≫
    (schemeDerivedDirectImage (g' ⁻¹ᵁ W).ι).map
      ((mvPullbackOpenRestrictionIso g' W).inv.app K ≫
        (schemeOpenRestriction X' (g' ⁻¹ᵁ W)).mapDerivedCategory.map ψ)
  let c := schemeMVOpenComparison g' W K'
  let ε := mvCanonicalBoundary X U V W rfl hcover (R.obj K')
  change (derivedPullback g').map δ ≫
    ((derivedPullback g').commShiftIso (1 : ℤ)).hom.app K ≫ ψ⟦(1 : ℤ)⟧' = t ≫ δ'
  have hnat : δ ≫ α⟦(1 : ℤ)⟧' = H.map α ≫ ε :=
    canonical_boundary_naturality X U V hcover K (R.obj K') α
  have hδ' : δ' = schemeMVBoundary X' (g' ⁻¹ᵁ U) (g' ⁻¹ᵁ V) hcover' K' := by
    dsimp only [δ', W]
    simpa only [Scheme.Hom.preimage_inf] using
      canonical_boundary_eq X' (g' ⁻¹ᵁ U) (g' ⁻¹ᵁ V) hcover' K'
  have himage : R.map δ' ≫ (R.commShiftIso (1 : ℤ)).hom.app K' = c.hom ≫ ε := by
    rw [hδ']
    dsimp only [ε, W]
    rw [canonical_boundary_eq]
    exact schemeMV_directImage_boundary X' X g' U V hcover hcover' K'
  exact boundary_pullback_of_transpose (derivedPullback g') R a δ δ' ψ t
    (H.obj (R.obj K')) c (H.map α) ε
    (mvCanonicalHomEquiv_shift g' K K' ψ (1 : ℤ)) hnat himage
    (derivedBaseChange_open_transpose g' W K K' ψ)

end AlgebraicGeometry
