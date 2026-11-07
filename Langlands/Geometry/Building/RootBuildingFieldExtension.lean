import Langlands.Geometry.Building.RootApartmentFieldDescent
import Langlands.Geometry.Building.KPBuilding
import Langlands.Geometry.Building.ApartmentQuotientComparison

/-! # Actual scalar extension of the literal restricted building quotient -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace
open Langlands.GroupScheme.GaloisPointComparison

namespace Langlands.Geometry.Building.KPApartmentData

variable {k K : Type u} [Field k] [Field K] [Algebra k K]
  {S : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] [Smooth G.X.hom]
  (i : S.toGrp ⟶ G) [Mono i.hom.hom.left]

local notation "b" => algebraBaseMap k K
local notation "S_K" => CategoryTheory.Functor.obj (CommGroupScheme.baseChange b) S
local notation "G_K" => baseChanged k K G
local notation "i_K" => CategoryTheory.Functor.map (GroupScheme.baseChange b) i

private instance extendedAffine : IsAffineHom (G_K).X.hom := by
  change IsAffineHom (CategoryTheory.Limits.pullback.snd G.X.hom b)
  infer_instance

private instance extendedMono : Mono (i_K).hom.hom.left := by
  let : Mono i.hom.hom := Over.mono_of_mono_left _
  change Mono ((Over.pullback b).map i.hom.hom).left
  infer_instance

variable (hS : IsSplitTorus S.toGrp) (hE : RelativeRoot.HasOppositeFactorPairs i)
  (ω : Kˣ →* Multiplicative ℝ)
  (hω : ∃ t : kˣ, (ω (Units.map (algebraMap k K).toMonoidHom t)).toAdd ≠ 0)

/-- Extend a point of the literal restricted apartment by the inverse of the
proved actual affine restriction equivalence. -/
def fieldExtendPoint
    (D : KPApartmentData (S := S_K) (G := G_K) (i_K) (fun t => (ω t).toAdd))
    (x : (fieldRestrict i hS hE ω hω D).Apartment) : D.Apartment :=
  (fieldRestrictAffineEquiv i hS hE ω hω D).symm x

@[simp] theorem fieldRestrictPoint_fieldExtendPoint
    (D : KPApartmentData (S := S_K) (G := G_K) (i_K) (fun t => (ω t).toAdd))
    (x : (fieldRestrict i hS hE ω hω D).Apartment) :
    fieldRestrictPoint i hS hE ω hω D (fieldExtendPoint i hS hE ω hω D x) = x :=
  (fieldRestrictAffineEquiv i hS hE ω hω D).apply_symm_apply x

@[simp] theorem fieldExtendPoint_fieldRestrictPoint
    (D : KPApartmentData (S := S_K) (G := G_K) (i_K) (fun t => (ω t).toAdd))
    (x : D.Apartment) :
    fieldExtendPoint i hS hE ω hω D (fieldRestrictPoint i hS hE ω hω D x) = x :=
  (fieldRestrictAffineEquiv i hS hE ω hω D).symm_apply_apply x

theorem fieldExtendPoint_injective
    (D : KPApartmentData (S := S_K) (G := G_K) (i_K) (fun t => (ω t).toAdd)) :
    Function.Injective (fieldExtendPoint i hS hE ω hω D) :=
  (fieldRestrictAffineEquiv i hS hE ω hω D).symm.injective

/-- Original normalizer points extend to the actual upstairs normalizer
action; no separate equivariance premise is required. -/
theorem fieldExtendPoint_normalizer
    (D : KPApartmentData (S := S_K) (G := G_K) (i_K) (fun t => (ω t).toAdd))
    (n : normalizerPoints i) (x : (fieldRestrict i hS hE ω hω D).Apartment) :
    fieldExtendPoint i hS hE ω hω D (n • x) =
      normalizerPointsFieldExtend (K := K) i n • fieldExtendPoint i hS hE ω hω D x := by
  apply (fieldRestrictAffineEquiv i hS hE ω hω D).injective
  change fieldRestrictPoint i hS hE ω hω D
      (fieldExtendPoint i hS hE ω hω D (n • x)) =
    fieldRestrictPoint i hS hE ω hω D
      (normalizerPointsFieldExtend (K := K) i n • fieldExtendPoint i hS hE ω hω D x)
  rw [fieldRestrictPoint_fieldExtendPoint, fieldRestrictPoint_normalizer,
    fieldRestrictPoint_fieldExtendPoint]

/-- Every nonzero-character filtration is the exact preimage of its upstairs
filtration at the extended point and the same real bound. -/
theorem filtration_fieldExtendPoint
    (D : KPApartmentData (S := S_K) (G := G_K) (i_K) (fun t => (ω t).toAdd))
    (x : (fieldRestrict i hS hE ω hω D).Apartment) (a : characterLattice S)
    (ha : a ≠ 0) (r : ℝ) :
    (fieldRestrict i hS hE ω hω D).filtration x a r =
      (D.filtration (fieldExtendPoint i hS hE ω hω D x)
        (characterLattice.baseChange b S a) r).comap (rationalExtend k K G) := by
  have h := filtration_fieldRestrictPoint i hS hE ω hω D
    (fieldExtendPoint i hS hE ω hω D x) a ha r
  rwa [fieldRestrictPoint_fieldExtendPoint] at h

/-- Original sharp fixers map into the upstairs sharp fixers at extended
points, by the actual root-filtration comparisons. -/
theorem sharpFixer_le_fieldExtendSharpFixer
    (D : KPApartmentData (S := S_K) (G := G_K) (i_K) (fun t => (ω t).toAdd))
    (x : (fieldRestrict i hS hE ω hω D).Apartment) :
    (fieldRestrict i hS hE ω hω D).sharpFixer {x} ≤
      (D.sharpFixer {fieldExtendPoint i hS hE ω hω D x}).comap
        (rationalExtend k K G) := by
  change (⨆ a : relativeRoots i, (fieldRestrict i hS hE ω hω D).rootFixer a {x}) ≤ _
  refine iSup_le fun a => ?_
  rw [(fieldRestrict i hS hE ω hω D).rootFixer_singleton]
  intro g hg
  have hgK : rationalExtend k K G g ∈
      D.filtration (fieldExtendPoint i hS hE ω hω D x)
        (characterLattice.baseChange b S a.val) 0 := by
    change g ∈ (D.filtration (fieldExtendPoint i hS hE ω hω D x)
      (characterLattice.baseChange b S a.val) 0).comap (rationalExtend k K G)
    rw [← filtration_fieldExtendPoint i hS hE ω hω D x a.val a.property.1 0]
    exact hg
  let aK : relativeRoots (T := S_K) i_K :=
    ⟨characterLattice.baseChange b S a.val,
      (mem_roots_baseChange_iff (K := K) G S hS i a.val).mpr a.property⟩
  apply D.rootFixer_le_sharpFixer aK {fieldExtendPoint i hS hE ω hω D x}
  rw [D.rootFixer_singleton]
  exact hgK

/-- In particular every original sharp fixer fixes the extended apartment
point in the existing upstairs reduced quotient. -/
theorem sharpFixer_le_fieldExtendFixer
    (D : KPApartmentData (S := S_K) (G := G_K) (i_K) (fun t => (ω t).toAdd))
    (x : (fieldRestrict i hS hE ω hω D).Apartment) :
    (fieldRestrict i hS hE ω hω D).sharpFixer {x} ≤
      (D.reducedFixer (D.apartmentMap (fieldExtendPoint i hS hE ω hω D x))).comap
        (rationalExtend k K G) := by
  intro g hg
  exact D.sharpFixer_le_reducedFixer _ (sharpFixer_le_fieldExtendSharpFixer
    i hS hE ω hω D x hg)

section RestrictedAction

local instance restrictedAction
    (D : KPApartmentData (S := S_K) (G := G_K) (i_K) (fun t => (ω t).toAdd)) :
    MulAction (rationalPoints G) D.ReducedBuilding :=
  MulAction.compHom D.ReducedBuilding (rationalExtend k K G)

private def fieldExtendApartmentMap
    (D : KPApartmentData (S := S_K) (G := G_K) (i_K) (fun t => (ω t).toAdd)) :
    (fieldRestrict i hS hE ω hω D).Apartment →[normalizerPoints i] D.ReducedBuilding where
  toFun x := D.apartmentMap (fieldExtendPoint i hS hE ω hω D x)
  map_smul' n x := by
    change D.apartmentMap (fieldExtendPoint i hS hE ω hω D (n • x)) =
      rationalExtend k K G n.val • D.apartmentMap (fieldExtendPoint i hS hE ω hω D x)
    rw [fieldExtendPoint_normalizer, D.apartmentMap_smul, normalizerPointsFieldExtend_coe]

/-- The actual extension map of reduced quotients for a supplied upstairs
apartment and its literal field restriction. Normalizer compatibility and all
pointwise sharp-fixer inclusions have been proved above. -/
def fieldExtendBuilding
    (D : KPApartmentData (S := S_K) (G := G_K) (i_K) (fun t => (ω t).toAdd)) :
    (fieldRestrict i hS hE ω hω D).ReducedBuilding → D.ReducedBuilding :=
  ApartmentQuotient.lift (fieldRestrict i hS hE ω hω D).sharpFixerFamily
    (fieldExtendApartmentMap i hS hE ω hω D)
    (sharpFixer_le_fieldExtendFixer i hS hE ω hω D)

@[simp] theorem fieldExtendBuilding_mk
    (D : KPApartmentData (S := S_K) (G := G_K) (i_K) (fun t => (ω t).toAdd))
    (g : rationalPoints G) (x : (fieldRestrict i hS hE ω hω D).Apartment) :
    fieldExtendBuilding i hS hE ω hω D
        (ApartmentQuotient.mk (fieldRestrict i hS hE ω hω D).sharpFixerFamily (g, x)) =
      rationalExtend k K G g • D.apartmentMap (fieldExtendPoint i hS hE ω hω D x) :=
  rfl

@[simp] theorem fieldExtendBuilding_apartment
    (D : KPApartmentData (S := S_K) (G := G_K) (i_K) (fun t => (ω t).toAdd))
    (x : (fieldRestrict i hS hE ω hω D).Apartment) :
    fieldExtendBuilding i hS hE ω hω D ((fieldRestrict i hS hE ω hω D).apartmentMap x) =
      D.apartmentMap (fieldExtendPoint i hS hE ω hω D x) :=
  ApartmentQuotient.lift_apartment (fieldRestrict i hS hE ω hω D).sharpFixerFamily
    (fieldExtendApartmentMap i hS hE ω hω D)
    (sharpFixer_le_fieldExtendFixer i hS hE ω hω D) x

/-- Equivariance uses the actual rational-point extension and the existing
upstairs quotient action, without exporting another action instance. -/
theorem fieldExtendBuilding_smul
    (D : KPApartmentData (S := S_K) (G := G_K) (i_K) (fun t => (ω t).toAdd))
    (g : rationalPoints G) (q : (fieldRestrict i hS hE ω hω D).ReducedBuilding) :
    fieldExtendBuilding i hS hE ω hω D (g • q) =
      rationalExtend k K G g • fieldExtendBuilding i hS hE ω hω D q :=
  (ApartmentQuotient.lift (fieldRestrict i hS hE ω hω D).sharpFixerFamily
    (fieldExtendApartmentMap i hS hE ω hω D)
    (sharpFixer_le_fieldExtendFixer i hS hE ω hω D)).map_smul g q

/-- Common source apartments and an injective upstairs apartment map imply
global injectivity; these geometric properties are explicit hypotheses. -/
theorem fieldExtendBuilding_injective
    (D : KPApartmentData (S := S_K) (G := G_K) (i_K) (fun t => (ω t).toAdd))
    (hcommon : ApartmentQuotient.HasCommonTranslatedApartment
      (fieldRestrict i hS hE ω hω D).sharpFixerFamily)
    (hD : Function.Injective D.apartmentMap) :
    Function.Injective (fieldExtendBuilding i hS hE ω hω D) := by
  apply ApartmentQuotient.lift_injective (fieldRestrict i hS hE ω hω D).sharpFixerFamily
    (fieldExtendApartmentMap i hS hE ω hω D)
    (sharpFixer_le_fieldExtendFixer i hS hE ω hω D) hcommon
  exact hD.comp (fieldExtendPoint_injective i hS hE ω hω D)

end RestrictedAction

/-- Actual scalar-extension equivariance and the extended apartment values
determine the quotient map uniquely. -/
theorem fieldExtendBuilding_unique
    (D : KPApartmentData (S := S_K) (G := G_K) (i_K) (fun t => (ω t).toAdd))
    (f : (fieldRestrict i hS hE ω hω D).ReducedBuilding → D.ReducedBuilding)
    (hf : ∀ (g : rationalPoints G) (q : (fieldRestrict i hS hE ω hω D).ReducedBuilding),
      f (g • q) = rationalExtend k K G g • f q)
    (ha : ∀ x : (fieldRestrict i hS hE ω hω D).Apartment,
      f ((fieldRestrict i hS hE ω hω D).apartmentMap x) =
        D.apartmentMap (fieldExtendPoint i hS hE ω hω D x)) :
    f = fieldExtendBuilding i hS hE ω hω D := by
  funext q
  obtain ⟨g, x, rfl⟩ := (fieldRestrict i hS hE ω hω D).exists_smul_apartmentMap q
  rw [hf, ha, fieldExtendBuilding_smul, fieldExtendBuilding_apartment]

end Langlands.Geometry.Building.KPApartmentData
