import Langlands.BruhatTits.IntegralModels.UnramifiedNeutralModelDescent
import Langlands.BruhatTits.IntegralModels.UnramifiedNeutralRoots
import Langlands.Geometry.Building.UnramifiedFixedWallInvarianceReduction

/-! # Nonnegative restricted root depth gives lower neutral integrality -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped ValuativeRel CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.GroupScheme.GaloisPointComparison
open Langlands.LocalGalois.Separable Langlands.Geometry.Building

namespace Langlands.BruhatTits.IntegralModels

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]

private instance nonnegativeIntegralityExtendedAffine :
    IsAffineHom (baseChanged F (inertiaFixedField F) G).X.hom := by
  change IsAffineHom (CategoryTheory.Limits.pullback.snd G.X.hom
    (algebraBaseMap F (inertiaFixedField F)))
  infer_instance

variable
  (L : RelativeComponentModelData ↥𝒪[F] F G)
  (E : RelativeComponentModelData (fixedFieldIntegers F) (inertiaFixedField F)
    (baseChanged F (inertiaFixedField F) G))
  (e : UnramifiedComponentModelRecovery L E)

include e

/-- Exact neutral recovery descends every point whose scalar extension lies
in the upper sharp fixer. The full model, rather than a neutral image
equality, is the supplied fixer model. -/
theorem mem_neutral_integralPoints_of_extend_mem_sharpFixer
    (B : MaximalUnramified.BuildingData F
      (baseChanged F (inertiaFixedField F) G))
    (Ω : Set B.Apartment)
    (hfull : E.full.integralPoints =
      characterValuationKernel (MaximalUnramified.valuation F)
          (baseChanged F (inertiaFixedField F) G) ⊓
        B.pointwiseFixer (B.apartmentMap '' Ω))
    {g : rationalPoints G}
    (hg : rationalExtend F (inertiaFixedField F) G g ∈ B.sharpFixer Ω) :
    g ∈ L.neutral.integralPoints := by
  rw [e.neutral_integralPoints_eq_comap]
  exact unramifiedSharpFixer_le_neutral B E Ω hfull hg

variable [Smooth G.X.hom]
  {S T : CommGroupScheme (Spec (CommRingCat.of F))}
  {iS : S.toGrp ⟶ G} [Mono iS.hom.hom.left] {iT : T.toGrp ⟶ G}
  [Mono ((GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map iT).hom.hom.left]

variable
  (hGK : IsConnectedReductive (baseChanged F (inertiaFixedField F) G))
  (hiT : IsMaximalSplitTorus (T := ((CommGroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).obj T))
    ((GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map iT))
  (D : KPApartmentData (S := ((CommGroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).obj T))
    ((GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map iT)
    (IntegerValuation.order (MaximalUnramified.valuation F)))
  (C : CentralizerDatum (S := ((CommGroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).obj T))
    ((GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map iT))
  (hDC : IntegerValuation.IsOmegaCompatible (MaximalUnramified.valuation F) D C)
  (f : S ⟶ T) (hf : CommGroupScheme.groupHom f ≫ iT = iS)
  (hS : IsSplitTorus S.toGrp)
  (hopp : RelativeRoot.HasOppositeFactorPairs (T := ((CommGroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).obj T))
    ((GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map iT))
  (x : D.Apartment)
  (hfull : E.full.integralPoints =
    characterValuationKernel (MaximalUnramified.valuation F)
        (baseChanged F (inertiaFixedField F) G) ⊓
      D.pointwiseFixer (D.apartmentMap '' ({x} : Set D.Apartment)))

include hGK C hDC hf hfull

/-- A lower root point of nonnegative restricted depth is an actual integral
point of the recovered neutral model. No lower valuation or neutral fixer
equality is assumed. -/
theorem mem_neutral_integralPoints_of_nonnegative_restrictedDepth
    {a : characterLattice S} (ha : a ∈ relativeRoots iS)
    {g : rationalPoints G} (hg : g ∈ rootGroupPoints iS a)
    (h0 : 0 ≤ torusFieldRestrictedRootFunctionFamily
      (k := F) (K := inertiaFixedField F) hS hiT.isSplitSubtorus.1 hopp
      (D.isRootDatumValuation_of_mem x.mem)
      ((CommGroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map f) a g) :
    g ∈ L.neutral.integralPoints := by
  let B : MaximalUnramified.BuildingData F
      (baseChanged F (inertiaFixedField F) G) :=
    { isConnectedReductive := hGK
      S := ((CommGroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).obj T)
      i := (GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map iT
      isMaximalSplitTorus := hiT
      apartment := D
      centralizer := C
      isOmegaCompatible := hDC }
  exact mem_neutral_integralPoints_of_extend_mem_sharpFixer L E e B {x} hfull
    (D.rationalExtend_mem_sharpFixer_of_nonneg hf hS hiT.isSplitSubtorus.1
      hopp x ha hg h0)

/-- The actual integral section of the lower neutral model specified by a
root point of nonnegative restricted depth. -/
def neutralSectionOfNonnegativeRestrictedDepth
    {a : characterLattice S} (ha : a ∈ relativeRoots iS)
    {g : rationalPoints G} (hg : g ∈ rootGroupPoints iS a)
    (h0 : 0 ≤ torusFieldRestrictedRootFunctionFamily
      (k := F) (K := inertiaFixedField F) hS hiT.isSplitSubtorus.1 hopp
      (D.isRootDatumValuation_of_mem x.mem)
      ((CommGroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map f) a g) :
    L.neutral.integralSections :=
  Classical.choose (mem_neutral_integralPoints_of_nonnegative_restrictedDepth
    L E e hGK hiT D C hDC f hf hS hopp x hfull ha hg h0)

theorem neutralSectionOfNonnegativeRestrictedDepth_generic
    {a : characterLattice S} (ha : a ∈ relativeRoots iS)
    {g : rationalPoints G} (hg : g ∈ rootGroupPoints iS a)
    (h0 : 0 ≤ torusFieldRestrictedRootFunctionFamily
      (k := F) (K := inertiaFixedField F) hS hiT.isSplitSubtorus.1 hopp
      (D.isRootDatumValuation_of_mem x.mem)
      ((CommGroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map f) a g) :
    L.neutral.integralPointMap
      (neutralSectionOfNonnegativeRestrictedDepth L E e hGK hiT D C hDC
        f hf hS hopp x hfull ha hg h0) = g :=
  Classical.choose_spec (mem_neutral_integralPoints_of_nonnegative_restrictedDepth
    L E e hGK hiT D C hDC f hf hS hopp x hfull ha hg h0)

end Langlands.BruhatTits.IntegralModels
