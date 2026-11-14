import Langlands.Geometry.Building.GaloisFacetResidueParabolics
import Langlands.GroupScheme.SchematicImageFunctoriality

/-! # Residue image naturality from actual coefficient comparison squares -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
set_option maxHeartbeats 800000

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Pointwise
open Langlands
open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace
open Langlands.GroupScheme.GaloisPointComparison

local instance imageNaturality_baseChangeAffine {k L : Type u} [Field k] [Field L]
    (b : Spec (CommRingCat.of L) ⟶ Spec (CommRingCat.of k))
    (G : GroupScheme (Spec (CommRingCat.of k))) [IsAffineHom G.X.hom] :
    IsAffineHom ((GroupScheme.baseChange b).obj G).X.hom := by
  change IsAffineHom (CategoryTheory.Limits.pullback.snd G.X.hom b)
  infer_instance

local instance imageNaturality_isAffine {k : Type u} [Field k]
    (G : GroupScheme (Spec (CommRingCat.of k))) [IsAffineHom G.X.hom] :
    IsAffine G.X.left :=
  isAffine_of_isAffineHom G.X.hom

namespace Langlands.GroupScheme.SchematicImage

variable {f L : Type u} [Field f] [Field L] [Algebra f L]
  (H : GroupScheme (Spec (CommRingCat.of f))) [IsAffineHom H.X.hom]
  {A A' : GroupScheme (Spec (CommRingCat.of L))}
  [IsAffineHom A.X.hom] [IsAffineHom A'.X.hom]
  (σ : L ≃ₐ[f] L)

/-- A commuting coefficient square with an actual source isomorphism
transports the actual schematic-image subgroup by the canonical Galois action. -/
theorem range_inclusion_galois_of_square
    (p : A ⟶ baseChanged f L H) (q : A' ⟶ baseChanged f L H)
    (s : (GroupScheme.baseChange (galoisBaseMap f L σ)).obj A ≅ A')
    (hs : s.hom ≫ q =
      (GroupScheme.baseChange (galoisBaseMap f L σ)).map p ≫
        (descentBaseChangeIso (algebraBaseMap f L) (galoisBaseMap f L σ)
          (galoisBaseMap_over f L σ) H).hom) :
    SubgroupFunctor.range (inclusion q) =
      SubgroupFunctor.galoisTransport f L H σ (SubgroupFunctor.range (inclusion p)) := by
  let : IsIso (galoisBaseMap f L σ) :=
    isIso_SpecMap_iff.mpr σ.bijective
  calc
    _ = SubgroupFunctor.range (inclusion (s.hom ≫ q)) :=
      (range_inclusion_iso_comp s q).symm
    _ = SubgroupFunctor.range (inclusion
        ((GroupScheme.baseChange (galoisBaseMap f L σ)).map p ≫
          (descentBaseChangeIso (algebraBaseMap f L) (galoisBaseMap f L σ)
            (galoisBaseMap_over f L σ) H).hom)) := by rw [hs]
    _ = ((SubgroupFunctor.range (inclusion p)).baseChange
        (galoisBaseMap f L σ)).comap
          (descentBaseChangeIso (algebraBaseMap f L) (galoisBaseMap f L σ)
            (galoisBaseMap_over f L σ) H).inv := by
      rw [range_inclusion_comp_iso, range_inclusion_baseChange]
    _ = _ := rfl

end Langlands.GroupScheme.SchematicImage

namespace Langlands.Geometry.Building.KPApartmentData

variable (k K : Type u) [Field k] [Field K] [Algebra k K]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  (i : T.toGrp ⟶ G)

local notation "b" => algebraBaseMap k K
local notation "T_K" => CategoryTheory.Functor.obj (CommGroupScheme.baseChange b) T
local notation "G_K" => baseChanged k K G
local notation "i_K" => CategoryTheory.Functor.map (GroupScheme.baseChange b) i

variable [Mono (CategoryTheory.Functor.map
    (GroupScheme.baseChange (algebraBaseMap k K)) i).hom.hom.left]
  {v : Valuation K (WithZero (Multiplicative ℤ))}
  (D : KPApartmentData
    (S := CategoryTheory.Functor.obj (CommGroupScheme.baseChange (algebraBaseMap k K)) T)
    (CategoryTheory.Functor.map (GroupScheme.baseChange (algebraBaseMap k K)) i)
    (IntegerValuation.order v))
  (hD : GaloisStable k K i D)
  (hG : IsConnectedReductive (baseChanged k K G))
  (hi : IsMaximalSplitTorus
    (T := CategoryTheory.Functor.obj (CommGroupScheme.baseChange (algebraBaseMap k K)) T)
    (CategoryTheory.Functor.map (GroupScheme.baseChange (algebraBaseMap k K)) i))
  (C : CentralizerDatum
    (S := CategoryTheory.Functor.obj (CommGroupScheme.baseChange (algebraBaseMap k K)) T)
    (CategoryTheory.Functor.map (GroupScheme.baseChange (algebraBaseMap k K)) i))
  (h6 : IntegerValuation.IsOmegaCompatible v D C)

local notation "B" => integerBuildingData D hG hi C h6

include hG hi C h6

open Langlands.BruhatTits.IntegralModels

variable (R : Type u) [CommRing R] [IsDomain R] [Algebra R K] [IsFractionRing R K]
  [IsLocalRing R]
  (E : GaloisFacet k K i D hD hG hi C h6)
  (M : IntegerFacetModelData (K := K) (G := baseChanged k K G) (v := v)
    (integerBuildingData D hG hi C h6) R)
  (Q : SpecialFibreQuotientData (R := R) (K := K) (G := baseChanged k K G)
    (M.model (K := K) (G := baseChanged k K G) (v := v) E.val))
  (f : Type u) [Field f] [Algebra f (IsLocalRing.ResidueField R)]
  (H : GroupScheme (Spec (CommRingCat.of f))) [IsAffineHom H.X.hom]
  (e : Q.quotient ≅ baseChanged f (IsLocalRing.ResidueField R) H)
  (residueAction : (K ≃ₐ[k] K) →* (IsLocalRing.ResidueField R ≃ₐ[f] IsLocalRing.ResidueField R))

local notation "L" => IsLocalRing.ResidueField R
local notation "incAct" => galoisIncidentFacetAction k K i D hD hG hi C h6 E

local instance imageNaturality_neutralAffine
    (N : RelativeComponentModelData R K (baseChanged k K G)) :
    IsAffineHom N.neutral.specialFibre.X.hom := by
  change IsAffineHom (CategoryTheory.Limits.pullback.snd N.neutral.group.X.hom
    (IntegralModel.residueBaseMap R))
  infer_instance

/-- Actual source and target coefficient isomorphisms, with the neutral-map
and quotient comparison squares. Their existence is a separate obligation. -/
structure ResidueCoefficientComparisonData where
  sourceIso : ∀ (σ : K ≃ₐ[k] K) (F : (B).IncidentFacets E.val),
    (GroupScheme.baseChange (galoisBaseMap f L (residueAction σ))).obj
        (M.model F.val).neutral.specialFibre ≅
      (M.model (incAct σ F).val).neutral.specialFibre
  targetIso : ∀ σ : K ≃ₐ[k] K,
    (GroupScheme.baseChange (galoisBaseMap f L (residueAction σ))).obj
        (M.model E.val).neutral.specialFibre ≅
      (M.model E.val).neutral.specialFibre
  map_comm : ∀ (σ : K ≃ₐ[k] K) (F : (B).IncidentFacets E.val),
    (sourceIso σ F).hom ≫
        (M.morphism E.val (incAct σ F).val (incAct σ F).property).neutralSpecialFibreMap =
      (GroupScheme.baseChange (galoisBaseMap f L (residueAction σ))).map
          (M.morphism E.val F.val F.property).neutralSpecialFibreMap ≫
        (targetIso σ).hom
  quotient_comm : ∀ σ : K ≃ₐ[k] K,
    (targetIso σ).hom ≫ Q.projection ≫ e.hom =
      (GroupScheme.baseChange (galoisBaseMap f L (residueAction σ))).map
          (Q.projection ≫ e.hom) ≫
        (descentBaseChangeIso (algebraBaseMap f L)
          (galoisBaseMap f L (residueAction σ))
          (galoisBaseMap_over f L (residueAction σ)) H).hom

/-- The transported facet image is the actual schematic image of the
original neutral map followed by the specified quotient comparison. -/
theorem residueFacetImage_eq_schematicImage (F : (B).IncidentFacets E.val) :
    residueFacetImage k K i D hD hG hi C h6 R E M Q f H e F =
      SubgroupFunctor.range (SchematicImage.inclusion
        (((M.morphism E.val F.val F.property).neutralSpecialFibreMap ≫ Q.projection) ≫
          e.hom)) :=
  (SchematicImage.range_inclusion_comp_iso _ e).symm

/-- Actual coefficient comparison squares imply the all-test image
compatibility needed by the maximal-Gamma-facet residue argument. -/
theorem hasGaloisResidueImageCompatibility_of_coefficientComparisons
    (N : ResidueCoefficientComparisonData k K i D hD hG hi C h6 R E M Q f H e
      residueAction) :
    HasGaloisResidueImageCompatibility k K i D hD hG hi C h6 R E M Q f H e
      residueAction := by
  intro σ F
  let p := ((M.morphism E.val F.val F.property).neutralSpecialFibreMap ≫ Q.projection) ≫
    e.hom
  let q := ((M.morphism E.val (incAct σ F).val (incAct σ F).property).neutralSpecialFibreMap ≫
    Q.projection) ≫ e.hom
  have hs : (N.sourceIso σ F).hom ≫ q =
      (GroupScheme.baseChange (galoisBaseMap f L (residueAction σ))).map p ≫
        (descentBaseChangeIso (algebraBaseMap f L)
          (galoisBaseMap f L (residueAction σ))
          (galoisBaseMap_over f L (residueAction σ)) H).hom := by
    dsimp only [p, q]
    calc
      _ = ((N.sourceIso σ F).hom ≫
          (M.morphism E.val (incAct σ F).val (incAct σ F).property).neutralSpecialFibreMap) ≫
            Q.projection ≫ e.hom := by simp only [Category.assoc]
      _ = ((GroupScheme.baseChange (galoisBaseMap f L (residueAction σ))).map
          (M.morphism E.val F.val F.property).neutralSpecialFibreMap ≫
            (N.targetIso σ).hom) ≫ Q.projection ≫ e.hom := by rw [N.map_comm]
      _ = (GroupScheme.baseChange (galoisBaseMap f L (residueAction σ))).map
          (M.morphism E.val F.val F.property).neutralSpecialFibreMap ≫
            ((N.targetIso σ).hom ≫ Q.projection ≫ e.hom) := by simp only [Category.assoc]
      _ = _ := by rw [N.quotient_comm]; simp only [Functor.map_comp, Category.assoc]
  calc
    _ = SubgroupFunctor.range (SchematicImage.inclusion q) :=
      residueFacetImage_eq_schematicImage k K i D hD hG hi C h6 R E M Q f H e _
    _ = SubgroupFunctor.galoisTransport f L H (residueAction σ)
        (SubgroupFunctor.range (SchematicImage.inclusion p)) :=
      SchematicImage.range_inclusion_galois_of_square H (residueAction σ) p q
        (N.sourceIso σ F) hs
    _ = _ := congrArg (SubgroupFunctor.galoisTransport f L H (residueAction σ))
      (residueFacetImage_eq_schematicImage k K i D hD hG hi C h6 R E M Q f H e F).symm

/-- Coefficient isomorphisms and actual commutative morphism squares suffice
for Galois compatibility of the actual facet residue images. -/
def GaloisFacetImageNaturalityStatement : Prop :=
  Nonempty (ResidueCoefficientComparisonData k K i D hD hG hi C h6 R E M Q f H e
    residueAction) →
      HasGaloisResidueImageCompatibility k K i D hD hG hi C h6 R E M Q f H e residueAction

theorem galoisFacetImageNaturality :
    GaloisFacetImageNaturalityStatement k K i D hD hG hi C h6 R E M Q f H e residueAction := by
  rintro ⟨N⟩
  exact hasGaloisResidueImageCompatibility_of_coefficientComparisons
    k K i D hD hG hi C h6 R E M Q f H e residueAction N

end Langlands.Geometry.Building.KPApartmentData
