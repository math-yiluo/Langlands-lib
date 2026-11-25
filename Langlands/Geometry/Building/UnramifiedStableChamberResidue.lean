import Langlands.Geometry.Building.ConstructedMaximalGaloisFacetResidue
import Langlands.Geometry.Building.GaloisFacetCentroids
import Langlands.Geometry.Building.IntegerValuationAffineWeylProof
import Langlands.Geometry.Building.AffineReflectionGalleryGeometry

/-! # Maximal Galois facets and residue quotients from stable ordinary chambers -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry IsLocalRing
open scoped CategoryTheory.MonObj ValuativeRel Pointwise
open Langlands.GroupScheme Langlands.GroupScheme.GaloisPointComparison
open Langlands.LocalGalois Langlands.LocalGalois.Separable
open Langlands.BruhatTits.IntegralModels

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option Elab.async false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1600000

namespace Langlands.Geometry.Building.KPApartmentData

section General

variable (k K : Type u) [Field k] [Field K] [Algebra k K]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  (i : T.toGrp ⟶ G)
  [Mono ((GroupScheme.baseChange (algebraBaseMap k K)).map i).hom.hom.left]
  {v : Valuation K (WithZero (Multiplicative ℤ))}
  (D : KPApartmentData
    (S := (CommGroupScheme.baseChange (algebraBaseMap k K)).obj T)
    ((GroupScheme.baseChange (algebraBaseMap k K)).map i) (IntegerValuation.order v))
  (hD : GaloisStable k K i D)
  (hG : IsConnectedReductive (baseChanged k K G))
  (hi : IsMaximalSplitTorus
    (T := (CommGroupScheme.baseChange (algebraBaseMap k K)).obj T)
    ((GroupScheme.baseChange (algebraBaseMap k K)).map i))
  (C : CentralizerDatum
    (S := (CommGroupScheme.baseChange (algebraBaseMap k K)).obj T)
    ((GroupScheme.baseChange (algebraBaseMap k K)).map i))
  (h6 : IntegerValuation.IsOmegaCompatible v D C)

private instance stableChamber_extendedAffine :
    IsAffineHom (baseChanged k K G).X.hom := by
  change IsAffineHom
    (CategoryTheory.Limits.pullback.snd G.X.hom (algebraBaseMap k K))
  infer_instance

local notation "B" => integerBuildingData D hG hi C h6

/-- A Gamma-facet represented by an ordinary regular apartment facet is
already maximal for the original full-facet incidence relation. -/
theorem isMaximalGaloisFacet_of_regular_apartmentFacet
    (x : D.Apartment) (hx : AffineRootSystem.GalleryGeometry.IsRegular D.affineRoots x)
    (E : GaloisFacet k K i D hD hG hi C h6)
    (hE : E.val.val = D.apartmentMap '' AffineRootSystem.facet D.affineRoots x) :
    IsMaximalGaloisFacet k K i D hD hG hi C h6 E := by
  have hcount : (B).facetVanishingRootCount E.val = 0 := by
    rw [(B).facetVanishingRootCount_eq_of_image E.val 1 x
      (by
        change E.val.val = (fun a => (1 : rationalPoints (baseChanged k K G)) •
          D.apartmentMap a) '' AffineRootSystem.facet D.affineRoots x
        simpa only [one_smul] using hE)]
    have hempty : AffineRootSystem.vanishingRoots D.affineRoots x = ∅ := by
      ext ψ
      simp only [Set.mem_empty_iff_false, iff_false]
      exact fun hψ => hx ψ hψ.1 hψ.2
    change (AffineRootSystem.vanishingRoots D.affineRoots x).ncard = 0
    rw [hempty, Set.ncard_empty]
  intro F hEF
  apply Subtype.ext
  by_contra hne
  have hlt := (B).facetVanishingRootCount_lt_of_facetPrecedes hEF (Ne.symm hne)
  rw [hcount] at hlt
  exact Nat.not_lt_zero _ hlt

/-- Whole-facet coefficient stability supplies a fixed centroid, while
ordinary regularity makes this same original facet maximal. -/
theorem exists_maximalGaloisFacet_of_regular_stable_apartmentFacet
    (hunit : ∃ t : Kˣ, IntegerValuation.order v t = 1)
    (x : D.Apartment) (hx : AffineRootSystem.GalleryGeometry.IsRegular D.affineRoots x)
    (hstable : ∀ σ : K ≃ₐ[k] K,
      galoisAffineAction k K i D hD σ '' AffineRootSystem.facet D.affineRoots x =
        AffineRootSystem.facet D.affineRoots x) :
    ∃ E : GaloisFacet k K i D hD hG hi C h6,
      E.val.val = D.apartmentMap '' AffineRootSystem.facet D.affineRoots x ∧
        IsMaximalGaloisFacet k K i D hD hG hi C h6 E := by
  let F : (B).BuildingFacet :=
    ⟨D.apartmentMap '' AffineRootSystem.facet D.affineRoots x,
      (B).isFacet_image (AffineRootSystem.isFacet_facet _ x)⟩
  have hFinv : IsGaloisInvariantFacet k K i D hD hG hi C h6 F := by
    intro σ
    change galoisQuotientAction k K i D hD σ ''
      (D.apartmentMap '' AffineRootSystem.facet D.affineRoots x) =
        D.apartmentMap '' AffineRootSystem.facet D.affineRoots x
    calc
      _ = D.apartmentMap '' (galoisAffineAction k K i D hD σ ''
          AffineRootSystem.facet D.affineRoots x) := by
        rw [Set.image_image, Set.image_image]
        apply Set.image_congr
        intro a _
        exact galoisQuotientAction_apartmentMap k K i D hD σ a
      _ = _ := congrArg (Set.image D.apartmentMap) (hstable σ)
  let E : GaloisFacet k K i D hD hG hi C h6 :=
    ⟨F, (isGaloisFacet_iff_invariant k K i D hD hG hi C h6
      ((B).isAffineRootSystemWithRankZero_affineRoots hunit) F).mpr hFinv⟩
  exact ⟨E, rfl,
    isMaximalGaloisFacet_of_regular_apartmentFacet k K i D hD hG hi C h6 x hx E rfl⟩

end General

section Unramified

variable (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]

private local instance : Algebra ↥𝒪[F] (fixedFieldIntegers F) :=
  Valuation.HasExtension.instAlgebraInteger
    (vR := ValuativeRel.valuation F) (vA := fixedFieldValuation F)
private local instance : IsScalarTower ↥𝒪[F] (fixedFieldIntegers F) (inertiaFixedField F) :=
  Valuation.HasExtension.instIsScalarTowerInteger
    (vR := ValuativeRel.valuation F) (vA := fixedFieldValuation F)
private local instance : Algebra 𝓀[F] (ResidueField (fixedFieldIntegers F)) :=
  (residueToFixedField F).toAlgebra
private local instance : IsDiscreteValuationRing (fixedFieldIntegers F) :=
  (separableUnramifiedArithmetic F).2.2.2.1
private local instance : HenselianLocalRing (fixedFieldIntegers F) :=
  fixedFieldIntegersIsHenselian F
private local instance : Algebra.IsAlgebraic 𝓀[F] (ResidueField (fixedFieldIntegers F)) :=
  (fixedFieldResidueIsAlgClosure F).2
private local instance : Fintype 𝓀[F] := Fintype.ofFinite _
private local instance : IsAlgClosed (ResidueField (fixedFieldIntegers F)) :=
  (fixedFieldResidueIsAlgClosure F).1

variable
  {T : CommGroupScheme (Spec (CommRingCat.of F))}
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  (i : T.toGrp ⟶ G)
  [Mono ((GroupScheme.baseChange
    (algebraBaseMap F (inertiaFixedField F))).map i).hom.hom.left]
  (D : KPApartmentData
    (S := (CommGroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).obj T)
    ((GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map i)
    (IntegerValuation.order (MaximalUnramified.valuation F)))
  (hD : GaloisStable F (inertiaFixedField F) i D)
  (hG : IsConnectedReductive (baseChanged F (inertiaFixedField F) G))
  (hi : IsMaximalSplitTorus
    (T := (CommGroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).obj T)
    ((GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map i))
  (C : CentralizerDatum
    (S := (CommGroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).obj T)
    ((GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map i))
  (h6 : IntegerValuation.IsOmegaCompatible (MaximalUnramified.valuation F) D C)

private instance unramifiedStableChamber_extendedAffine :
    IsAffineHom (baseChanged F (inertiaFixedField F) G).X.hom := by
  change IsAffineHom (CategoryTheory.Limits.pullback.snd G.X.hom
    (algebraBaseMap F (inertiaFixedField F)))
  infer_instance

local notation "Z" => UnramifiedZeroDatum.ofConnectedReductive
  (baseChanged F (inertiaFixedField F) G) hG
local notation "B" => integerBuildingData D hG hi C h6
local notation "M" => unramifiedIntegerFacetModels Z B

/-- A supplied ordinary regular, coefficient-stable apartment facet is the
exact original maximal Gamma-facet of a constructed reference residue
quotient with no proper rational parabolics. -/
def UnramifiedStableChamberResidueStatement : Prop :=
  GeometricallyConnected G.X.hom →
  ∀ (x : D.Apartment),
    AffineRootSystem.GalleryGeometry.IsRegular D.affineRoots x →
    (∀ σ : inertiaFixedField F ≃ₐ[F] inertiaFixedField F,
      galoisAffineAction F (inertiaFixedField F) i D hD σ ''
          AffineRootSystem.facet D.affineRoots x =
        AffineRootSystem.facet D.affineRoots x) →
    ∃ (E : GaloisFacet F (inertiaFixedField F) i D hD hG hi C h6)
      (N0 : RelativeComponentModelData ↥𝒪[F] F G)
      (_t : UnramifiedComponentModelRecovery N0 ((M).model E.val))
      (Q0 : SpecialFibreQuotientData N0),
      E.val.val = D.apartmentMap '' AffineRootSystem.facet D.affineRoots x ∧
      IsMaximalGaloisFacet F (inertiaFixedField F) i D hD hG hi C h6 E ∧
      Q0.IsReductiveQuotient ∧
      ∀ (P : GroupScheme (Spec (CommRingCat.of 𝓀[F]))) (p : P ⟶ Q0.quotient),
        IsParabolicSubgroup p → IsIso p

set_option maxHeartbeats 3200000 in
/-- The actual order-one unit supplies the fixed centroid criterion; the
published maximal-facet construction supplies recovery and the quotient. -/
theorem unramifiedStableChamberResidue :
    UnramifiedStableChamberResidueStatement F i D hD hG hi C h6 := by
  intro hconn x hx hstable
  obtain ⟨E, hE, hmax⟩ :=
    exists_maximalGaloisFacet_of_regular_stable_apartmentFacet
      F (inertiaFixedField F) i D hD hG hi C h6
      (MaximalUnramified.exists_order_eq_one F) x hx hstable
  have hres : ConstructedMaximalGaloisFacetResidueStatement F i D hD hG hi C h6 E :=
    constructedMaximalGaloisFacetResidue F i D hD hG hi C h6 E
  obtain ⟨N0, t, Q0, hQ0, hno, _hcentral⟩ := hres hconn hmax
  exact ⟨E, N0, t, Q0, hE, hmax, hQ0, hno⟩

end Unramified

end Langlands.Geometry.Building.KPApartmentData
