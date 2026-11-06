import Langlands.Geometry.Building.ValuationBuildingQuotientComparison
import Langlands.Geometry.Building.MaximalUnramifiedBuildingData
import Langlands.GroupScheme.GaloisPointRational
import Mathlib.Algebra.Group.Action.Hom

/-! # Scalar-extension lift into a supplied maximal-unramified building quotient -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme
open Langlands.GroupScheme.GaloisPointComparison

namespace Langlands.Geometry.Building.MaximalUnramified

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]

private instance extensionAffineHom :
    IsAffineHom (baseChanged F (UnramifiedClosure F) G).X.hom := by
  change IsAffineHom
    (Limits.pullback.snd G.X.hom (baseMap F (UnramifiedClosure F)))
  infer_instance

variable (B : ValuationBuildingData G)
  (C : BuildingData F (baseChanged F (UnramifiedClosure F) G))
  (f : B.Apartment → C.Apartment)

/-- Comparing each actual depth-zero root subgroup with the upstairs point
fixer suffices to compare the generated sharp fixer at the given point. -/
theorem sharpFixer_le_comap_of_rootFiltration (x : B.Apartment)
    (hroot : ∀ a : relativeRoots B.i, B.filtration x a 0 ≤
      (C.fixer (C.apartmentMap (f x))).comap
        (rationalExtend F (UnramifiedClosure F) G)) :
    B.sharpFixer {x} ≤ (C.fixer (C.apartmentMap (f x))).comap
      (rationalExtend F (UnramifiedClosure F) G) := by
  change (⨆ a : relativeRoots B.i, B.apartment.rootFixer a {x}) ≤ _
  refine iSup_le fun a => ?_
  rw [B.apartment.rootFixer_singleton]
  exact hroot a

variable
  (hN : ∀ (n : normalizerPoints B.i) (x : B.Apartment),
    C.apartmentMap (f (n • x)) =
      rationalExtend F (UnramifiedClosure F) G (n : rationalPoints G) •
        C.apartmentMap (f x))
  (hfix : ∀ x : B.Apartment, B.sharpFixer {x} ≤
    (C.fixer (C.apartmentMap (f x))).comap
      (rationalExtend F (UnramifiedClosure F) G))

section RestrictedAction

local instance restrictedAction : MulAction (rationalPoints G) C.ReducedBuilding :=
  MulAction.compHom C.ReducedBuilding (rationalExtend F (UnramifiedClosure F) G)

private def scalarExtensionApartmentMap :
    B.Apartment →[normalizerPoints B.i] C.ReducedBuilding where
  toFun x := C.apartmentMap (f x)
  map_smul' := hN

/-- Extend the supplied apartment map through the existing source quotient,
using the original upstairs action restricted along actual scalar extension.
Normalizer compatibility and sharp-fixer comparison hold at every source point. -/
def quotientLift : B.ReducedBuilding → C.ReducedBuilding :=
  ApartmentQuotient.lift B.apartment.sharpFixerFamily
    (scalarExtensionApartmentMap B C f hN) hfix

@[simp]
theorem quotientLift_mk (g : rationalPoints G) (x : B.Apartment) :
    quotientLift B C f hN hfix
        (ApartmentQuotient.mk B.apartment.sharpFixerFamily (g, x)) =
      rationalExtend F (UnramifiedClosure F) G g • C.apartmentMap (f x) :=
  rfl

@[simp]
theorem quotientLift_apartment (x : B.Apartment) :
    quotientLift B C f hN hfix (B.apartmentMap x) = C.apartmentMap (f x) :=
  ApartmentQuotient.lift_apartment B.apartment.sharpFixerFamily
    (scalarExtensionApartmentMap B C f hN) hfix x

/-- Equivariance is expressed with the actual extension homomorphism and the
existing upstairs action, without exporting a new global action instance. -/
theorem quotientLift_smul (g : rationalPoints G) (q : B.ReducedBuilding) :
    quotientLift B C f hN hfix (g • q) =
      rationalExtend F (UnramifiedClosure F) G g • quotientLift B C f hN hfix q :=
  (ApartmentQuotient.lift B.apartment.sharpFixerFamily
    (scalarExtensionApartmentMap B C f hN) hfix).map_smul g q

/-- The source building axiom supplies common apartments, so injectivity on
the supplied upstairs apartment implies injectivity on the whole quotient. -/
theorem quotientLift_injective
    {R : B.PolysimplicialRealization} (hB : B.SatisfiesBuildingAxiom R)
    (hf : Function.Injective f) (hC : Function.Injective C.apartmentMap) :
    Function.Injective (quotientLift B C f hN hfix) := by
  apply ApartmentQuotient.lift_injective B.apartment.sharpFixerFamily
    (scalarExtensionApartmentMap B C f hN) hfix (hB.hasCommonApartments B)
  exact hC.comp hf

/-- The scalar-extension embedding of these supplied quotients. Construction
of the compatible apartment and root-filtration data remains a separate problem. -/
def quotientEmbedding
    {R : B.PolysimplicialRealization} (hB : B.SatisfiesBuildingAxiom R)
    (hf : Function.Injective f) (hC : Function.Injective C.apartmentMap) :
    B.ReducedBuilding ↪ C.ReducedBuilding where
  toFun := quotientLift B C f hN hfix
  inj' := quotientLift_injective B C f hN hfix hB hf hC

@[simp]
theorem quotientEmbedding_apply
    {R : B.PolysimplicialRealization} (hB : B.SatisfiesBuildingAxiom R)
    (hf : Function.Injective f) (hC : Function.Injective C.apartmentMap)
    (q : B.ReducedBuilding) :
    quotientEmbedding B C f hN hfix hB hf hC q = quotientLift B C f hN hfix q :=
  rfl

end RestrictedAction

/-- The apartment values and actual scalar-extension equivariance determine
the lift uniquely. -/
theorem quotientLift_unique
    (e : B.ReducedBuilding → C.ReducedBuilding)
    (he : ∀ (g : rationalPoints G) (q : B.ReducedBuilding),
      e (g • q) = rationalExtend F (UnramifiedClosure F) G g • e q)
    (ha : ∀ x : B.Apartment, e (B.apartmentMap x) = C.apartmentMap (f x)) :
    e = quotientLift B C f hN hfix := by
  funext q
  obtain ⟨g, x, rfl⟩ := B.exists_smul_apartmentMap q
  rw [he, ha, quotientLift_smul, quotientLift_apartment]

end Langlands.Geometry.Building.MaximalUnramified
