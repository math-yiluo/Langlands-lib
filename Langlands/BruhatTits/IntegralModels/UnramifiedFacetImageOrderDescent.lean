import Langlands.BruhatTits.IntegralModels.UnramifiedFacetImageOrder
import Langlands.BruhatTits.IntegralModels.FacetRootSignBaseChange
import Langlands.BruhatTits.IntegralModels.UnramifiedFacetSignDescent
import Langlands.GroupScheme.SubgroupFunctor.FpqcDescent
import Langlands.GroupScheme.Descent.GaloisInvariantParabolics

/-! # Descent of actual facet-image order through unramified coefficients -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj ValuativeRel
open Langlands.GroupScheme Langlands.Geometry.Building
open Langlands.LocalGalois.Separable

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1600000

namespace Langlands.BruhatTits.IntegralModels

namespace RelativeComponentModelHom

section Coefficients

variable {R K : Type u} [CommRing R] [IsDomain R] [Field K]
  [Algebra R K] [IsFractionRing R K]
  {G : GroupScheme (Spec (CommRingCat.of K))}
  (A L : Type u) [CommRing A] [IsDomain A] [Field L]
  [Algebra R A] [Algebra A L] [IsFractionRing A L]
  [Algebra K L] [Algebra R L] [IsScalarTower R A L] [IsScalarTower R K L]
  [IsLocalRing R] [IsLocalRing A] [IsLocalHom (algebraMap R A)]
  {source₁ source₂ target : RelativeComponentModelData R K G}
  (φ : RelativeComponentModelHom source₁ target)
  (ψ : RelativeComponentModelHom source₂ target)
  (Q : SpecialFibreQuotientData target)

local notation "b" =>
  algebraBaseMap (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField A)

/-- The actual quotient-image subgroup functor commutes with local
coefficient extension, on every scheme test. -/
theorem reductiveImage_range_baseChange :
    (SubgroupFunctor.range (φ.reductiveImageInclusion Q)).baseChange b =
      SubgroupFunctor.range
        ((φ.baseChange A L).reductiveImageInclusion (Q.baseChange A L)) := by
  rw [SubgroupFunctor.range_baseChange,
    ← φ.reductiveImageBaseChangeIso_hom_comp A L Q]
  exact SubgroupFunctor.range_iso_comp (φ.reductiveImageBaseChangeIso A L Q) _

/-- Inclusion of the original actual quotient images is equivalent to
inclusion after local coefficient extension. -/
theorem reductiveImage_le_iff_baseChange :
    SubgroupFunctor.range (φ.reductiveImageInclusion Q) ≤
        SubgroupFunctor.range (ψ.reductiveImageInclusion Q) ↔
      SubgroupFunctor.range
          ((φ.baseChange A L).reductiveImageInclusion (Q.baseChange A L)) ≤
        SubgroupFunctor.range
          ((ψ.baseChange A L).reductiveImageInclusion (Q.baseChange A L)) := by
  have hb := fieldExtension_fpqc (IsLocalRing.ResidueField R)
    (IsLocalRing.ResidueField A)
  let : Surjective b := hb.1
  let : Flat b := hb.2.1
  let : QuasiCompact b := hb.2.2
  have : Mono (ψ.reductiveImageInclusion Q).hom.hom :=
    inferInstanceAs (Mono (SchematicImage.inclusionOver _))
  rw [← φ.reductiveImage_range_baseChange A L Q,
    ← ψ.reductiveImage_range_baseChange A L Q]
  exact (SubgroupFunctor.baseChange_le_range_iff b
    (ψ.reductiveImageInclusion Q)).symm

/-- Equality of the original actual quotient images is equivalent to
equality after local coefficient extension. -/
theorem reductiveImage_eq_iff_baseChange :
    SubgroupFunctor.range (φ.reductiveImageInclusion Q) =
        SubgroupFunctor.range (ψ.reductiveImageInclusion Q) ↔
      SubgroupFunctor.range
          ((φ.baseChange A L).reductiveImageInclusion (Q.baseChange A L)) =
        SubgroupFunctor.range
          ((ψ.baseChange A L).reductiveImageInclusion (Q.baseChange A L)) := by
  rw [le_antisymm_iff, le_antisymm_iff,
    φ.reductiveImage_le_iff_baseChange A L ψ Q,
    ψ.reductiveImage_le_iff_baseChange A L φ Q]

/-- Parabolicity of the actual extended quotient image descends along
an algebraic residue-field extension. -/
theorem hasParabolicReductiveImage_of_baseChange
    [Algebra.IsAlgebraic (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField A)]
    (hφ : (φ.baseChange A L).HasParabolicReductiveImage (Q.baseChange A L)) :
    φ.HasParabolicReductiveImage Q := by
  have hbc : IsParabolicSubgroup
      ((GroupScheme.baseChange b).map (φ.reductiveImageInclusion Q)) := by
    rw [← φ.reductiveImageBaseChangeIso_hom_comp A L Q]
    exact hφ.iso_comp (φ.reductiveImageBaseChangeIso A L Q)
  exact hbc.of_baseChange_of_algebraicExtension
    (inferInstanceAs (IsClosedImmersion (φ.reductiveImageInclusion Q).hom.hom.left))

end Coefficients
end RelativeComponentModelHom

section Unramified

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  (B : ValuationBuildingData G)
  (C : MaximalUnramified.BuildingData F
    (GaloisPointComparison.baseChanged F (inertiaFixedField F) G))
  (E : UnramifiedZeroDatum F
    (GaloisPointComparison.baseChanged F (inertiaFixedField F) G))
  (e : B.ReducedBuilding → C.ReducedBuilding)
  (a : B.Apartment →ᵃ[ℝ] C.Apartment)
  (hD : B.SatisfiesApartmentAxioms)
  (hcommon : ∀ x : B.ReducedBuilding, B.HasCommonApartmentWith x)
  (hequiv : ∀ (g : rationalPoints G) (x : B.ReducedBuilding),
    e (g • x) = GaloisPointComparison.rationalExtend F (inertiaFixedField F) G g • e x)
  (hap : ∀ x : B.Apartment, e (B.apartmentMap x) = C.apartmentMap (a x))
  (hfac : ∀ x : B.Apartment,
    a ⁻¹' AffineRootSystem.facet C.affineRoots (a x) =
      AffineRootSystem.facet B.affineRoots x)
  {source₁ source₂ target : RelativeComponentModelData ↥𝒪[F] F G}
  (φ : RelativeComponentModelHom source₁ target)
  (ψ : RelativeComponentModelHom source₂ target)
  (Q : SpecialFibreQuotientData target)

private instance unramifiedImageDescent_affine :
    IsAffineHom (GaloisPointComparison.baseChanged F (inertiaFixedField F) G).X.hom := by
  change IsAffineHom
    (CategoryTheory.Limits.pullback.snd G.X.hom (GaloisPointComparison.baseMap F _))
  infer_instance

local instance imageOrderDescentIntegerAlgebra : Algebra ↥𝒪[F] (fixedFieldIntegers F) :=
  Valuation.HasExtension.instAlgebraInteger
    (vR := ValuativeRel.valuation F) (vA := fixedFieldValuation F)

local instance imageOrderDescentIntegerTower : IsScalarTower ↥𝒪[F] (fixedFieldIntegers F) (inertiaFixedField F) :=
  Valuation.HasExtension.instIsScalarTowerInteger
    (vR := ValuativeRel.valuation F) (vA := fixedFieldValuation F)

local instance imageOrderDescentIntegerLocal : IsLocalHom (algebraMap ↥𝒪[F] (fixedFieldIntegers F)) :=
  haveI : IsLocalHom (algebraMap F (inertiaFixedField F)) :=
    isLocalHom_of_exists_map_ne_one ⟨0, by simp⟩
  Valuation.HasExtension.instIsLocalHomValuationInteger
    (vR := ValuativeRel.valuation F) (vS := fixedFieldValuation F)

local instance imageOrderDescentHenselian : HenselianLocalRing (fixedFieldIntegers F) :=
  fixedFieldIntegersIsHenselian F

local instance imageOrderDescentResidueClosed : IsAlgClosed (IsLocalRing.ResidueField (fixedFieldIntegers F)) :=
  (fixedFieldResidueIsAlgClosure F).1

local instance imageOrderDescentResidueAlgebraic : Algebra.IsAlgebraic (IsLocalRing.ResidueField ↥𝒪[F])
    (IsLocalRing.ResidueField (fixedFieldIntegers F)) :=
  unramifiedResidue_isAlgebraic

local instance imageOrderDescentResidueSeparable : Algebra.IsSeparable (IsLocalRing.ResidueField ↥𝒪[F])
    (IsLocalRing.ResidueField (fixedFieldIntegers F)) :=
  unramifiedResidue_isSeparable

include hD hcommon hequiv hap hfac in
/-- Actual quotient-image inclusion over the original residue field is
exactly reverse downstairs incidence, under explicit upstairs image
parabolicity and target congruence containment. -/
theorem reductiveImage_le_iff_descendedFacetPrecedes_of_unramified
    (hno : MaximalUnramified.ZeroFacetNoInversionsStatement.{u})
    {Fc Fd : BuildingFacet B}
    (hsource₁ : source₁.neutral.baseChangeUnramified.integralPoints =
      E.zeroPoints ⊓ C.pointwiseFixer (e '' Fc.val))
    (hsource₂ : source₂.neutral.baseChangeUnramified.integralPoints =
      E.zeroPoints ⊓ C.pointwiseFixer (e '' Fd.val))
    (hker₁ : target.neutral.baseChangeUnramified.congruenceSubgroup ≤
      source₁.neutral.baseChangeUnramified.integralPoints)
    (hker₂ : target.neutral.baseChangeUnramified.congruenceSubgroup ≤
      source₂.neutral.baseChangeUnramified.integralPoints)
    (hQ : Q.IsReductiveQuotient)
    (hφ : (φ.baseChange (fixedFieldIntegers F) (inertiaFixedField F)).HasParabolicSpecialFibreImage)
    (hψ : (ψ.baseChange (fixedFieldIntegers F) (inertiaFixedField F)).HasParabolicSpecialFibreImage) :
    SubgroupFunctor.range (φ.reductiveImageInclusion Q) ≤
        SubgroupFunctor.range (ψ.reductiveImageInclusion Q) ↔
      FacetPrecedes B Fd Fc := by
  rw [φ.reductiveImage_le_iff_baseChange
    (fixedFieldIntegers F) (inertiaFixedField F) ψ Q]
  exact unramifiedReductiveImage_le_iff_descendedFacetPrecedes
    B E C (GaloisPointComparison.rationalExtend F (inertiaFixedField F) G) e a
    hD hcommon hequiv hap hfac
    (φ.baseChange (fixedFieldIntegers F) (inertiaFixedField F))
    (ψ.baseChange (fixedFieldIntegers F) (inertiaFixedField F))
    hno hsource₁ hsource₂ hker₁ hker₂
    (Q.baseChange (fixedFieldIntegers F) (inertiaFixedField F))
    (Q.isReductiveQuotient_baseChange _ _ hQ) hφ hψ

omit [IsAffineHom G.X.hom] in
/-- A parabolic actual special-fibre image over the maximal unramified
integers gives a parabolic actual quotient image over the original residue
field. -/
theorem hasParabolicReductiveImage_of_unramifiedSpecialFibre
    (hQ : Q.IsReductiveQuotient)
    (hφ : (φ.baseChange (fixedFieldIntegers F) (inertiaFixedField F)).HasParabolicSpecialFibreImage) :
    φ.HasParabolicReductiveImage Q := by
  apply φ.hasParabolicReductiveImage_of_baseChange
    (fixedFieldIntegers F) (inertiaFixedField F) Q
  exact ((φ.baseChange (fixedFieldIntegers F) (inertiaFixedField F)).parabolicReductiveImage_and_comap
      (Q.baseChange (fixedFieldIntegers F) (inertiaFixedField F))
      (Q.isReductiveQuotient_baseChange _ _ hQ) hφ).1

/-- The descended actual quotient-image order, conditional only on the
displayed no-inversions, characterization, congruence and parabolicity inputs. -/
def HasUnramifiedDescendedQuotientImageOrder : Prop :=
  MaximalUnramified.ZeroFacetNoInversionsStatement.{u} →
    ∀ (Fc Fd : BuildingFacet B),
      source₁.neutral.baseChangeUnramified.integralPoints =
        E.zeroPoints ⊓ C.pointwiseFixer (e '' Fc.val) →
      source₂.neutral.baseChangeUnramified.integralPoints =
        E.zeroPoints ⊓ C.pointwiseFixer (e '' Fd.val) →
      target.neutral.baseChangeUnramified.congruenceSubgroup ≤
        source₁.neutral.baseChangeUnramified.integralPoints →
      target.neutral.baseChangeUnramified.congruenceSubgroup ≤
        source₂.neutral.baseChangeUnramified.integralPoints →
      Q.IsReductiveQuotient →
      (φ.baseChange (fixedFieldIntegers F) (inertiaFixedField F)).HasParabolicSpecialFibreImage →
      (ψ.baseChange (fixedFieldIntegers F) (inertiaFixedField F)).HasParabolicSpecialFibreImage →
      φ.HasParabolicReductiveImage Q ∧ ψ.HasParabolicReductiveImage Q ∧
        (SubgroupFunctor.range (φ.reductiveImageInclusion Q) ≤
            SubgroupFunctor.range (ψ.reductiveImageInclusion Q) ↔
          FacetPrecedes B Fd Fc)

include hD hcommon hequiv hap hfac in
theorem hasUnramifiedDescendedQuotientImageOrder :
    HasUnramifiedDescendedQuotientImageOrder B C E e φ ψ Q := by
  intro hno Fc Fd hsource₁ hsource₂ hker₁ hker₂ hQ hφ hψ
  exact ⟨hasParabolicReductiveImage_of_unramifiedSpecialFibre φ Q hQ hφ,
    hasParabolicReductiveImage_of_unramifiedSpecialFibre ψ Q hQ hψ,
    reductiveImage_le_iff_descendedFacetPrecedes_of_unramified
      B C E e a hD hcommon hequiv hap hfac φ ψ Q hno
      hsource₁ hsource₂ hker₁ hker₂ hQ hφ hψ⟩

end Unramified
end Langlands.BruhatTits.IntegralModels
