import Langlands.Geometry.Building.UnramifiedRootTranslationPositivity
import Langlands.BruhatTits.IntegralModels.RadicalPreimageTransfer

/-! # Radical root points and nearby parabolic model comparisons -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Filter
open scoped CategoryTheory.MonObj Topology
open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace
open Langlands.GroupScheme.GaloisPointComparison
open Langlands.BruhatTits.IntegralModels

namespace Langlands.Geometry.Building

variable {R k K : Type u} [CommRing R] [IsDomain R] [IsLocalRing R]
  [Field k] [Algebra R k] [IsFractionRing R k] [Field K] [Algebra k K]
  {S T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  [Smooth G.X.hom] {jT : T.toGrp ⟶ G}

private instance radicalPositivityExtendedAffine :
    IsAffineHom (baseChanged k K G).X.hom := by
  change IsAffineHom (CategoryTheory.Limits.pullback.snd G.X.hom (algebraBaseMap k K))
  infer_instance

private instance radicalPositivityExtendedSmooth :
    Smooth (baseChanged k K G).X.hom := by
  change Smooth (CategoryTheory.Limits.pullback.snd G.X.hom (algebraBaseMap k K))
  infer_instance

variable [Mono ((GroupScheme.baseChange (algebraBaseMap k K)).map jT).hom.hom.left]
  {ω : Kˣ → ℝ}
  (D : KPApartmentData
    (S := (CommGroupScheme.baseChange (algebraBaseMap k K)).obj T)
    ((GroupScheme.baseChange (algebraBaseMap k K)).map jT) ω)
  (f : S ⟶ T) (hS : IsSplitTorus S.toGrp)
  (hT : IsSplitTorus ((CommGroupScheme.baseChange (algebraBaseMap k K)).obj T).toGrp)
  (hE : RelativeRoot.HasOppositeFactorPairs
    (T := (CommGroupScheme.baseChange (algebraBaseMap k K)).obj T)
    ((GroupScheme.baseChange (algebraBaseMap k K)).map jT))

namespace KPApartmentData

/-- Actual parabolic source models compare their integral root points with
nonnegative root values near each descended translation line. The source and
the model morphism may depend on the direction and the real parameter. -/
def ParabolicRootComparisonsNearDescentTranslations
    (iS : S.toGrp ⟶ G) (target : RelativeComponentModelData R k G)
    (x : D.Apartment) : Prop :=
  ∀ v : V S, ∀ᶠ t : ℝ in 𝓝 0,
    ∃ (source : RelativeComponentModelData R k G)
      (ρ : RelativeComponentModelHom source target),
      ρ.HasParabolicSpecialFibreImage ∧ ρ.HasParabolicReductionPreimage ∧
        ∀ a ∈ relativeRoots iS, ∀ g ∈ rootGroupPoints iS a,
          g ∈ source.neutral.integralPoints →
            0 ≤ torusFieldRestrictedRootFunctionFamily (k := k) (K := K)
              hS hT hE
              (D.isRootDatumValuation_of_mem
                (D.descentTranslate f hS x (t • v)).mem)
              ((CommGroupScheme.baseChange (algebraBaseMap k K)).map f) a g

/-- A root point reducing into the actual target radical has nonnegative
restricted value along each nearby descended translation. -/
theorem nonnegativeNearDescentTranslations_of_mem_positivePoints
    {iS : S.toGrp ⟶ G} {target : RelativeComponentModelData R k G}
    {x : D.Apartment}
    (hmodels : D.ParabolicRootComparisonsNearDescentTranslations f hS hT hE
      iS target x)
    (Q : SpecialFibreQuotientData target)
    (hrad : IsUnipotentRadical Q.radicalInclusion)
    {a : characterLattice S} (ha : a ∈ relativeRoots iS)
    {g : rationalPoints G} (hg : g ∈ rootGroupPoints iS a)
    (hgpos : g ∈ Q.positivePoints) :
    D.NonnegativeNearDescentTranslations f hS hT hE x a g := by
  intro v
  filter_upwards [hmodels v] with t ht
  obtain ⟨source, ρ, hpar, hpre, hcomp⟩ := ht
  exact hcomp a ha g hg
    (ρ.positivePoints_le_source_of_parabolicReductionPreimage Q hpar hpre hrad hgpos)

/-- Nearby actual parabolic models and one-way root comparisons force every
radical root point to have strictly positive restricted root value. -/
theorem strictPositive_of_mem_positivePoints_of_parabolicRootComparisons
    {iS : S.toGrp ⟶ G} {target : RelativeComponentModelData R k G}
    {x : D.Apartment}
    (hmodels : D.ParabolicRootComparisonsNearDescentTranslations f hS hT hE
      iS target x)
    (Q : SpecialFibreQuotientData target)
    (hrad : IsUnipotentRadical Q.radicalInclusion)
    {a : characterLattice S} (ha : a ∈ relativeRoots iS)
    {g : rationalPoints G} (hg : g ∈ rootGroupPoints iS a)
    (hgpos : g ∈ Q.positivePoints) :
    0 < torusFieldRestrictedRootFunctionFamily (k := k) (K := K)
      hS hT hE (D.isRootDatumValuation_of_mem x.mem)
      ((CommGroupScheme.baseChange (algebraBaseMap k K)).map f) a g :=
  (D.strictPositive_iff_nonnegativeNearDescentTranslations f hS hT hE
    x (mem_relativeRoots.mp ha).1 g).mpr
      (D.nonnegativeNearDescentTranslations_of_mem_positivePoints f hS hT hE
        hmodels Q hrad ha hg hgpos)

/-- A root point of restricted value zero lies outside the actual radical
preimage under the same nearby-model hypotheses. -/
theorem not_mem_positivePoints_of_eq_zero_of_parabolicRootComparisons
    {iS : S.toGrp ⟶ G} {target : RelativeComponentModelData R k G}
    {x : D.Apartment}
    (hmodels : D.ParabolicRootComparisonsNearDescentTranslations f hS hT hE
      iS target x)
    (Q : SpecialFibreQuotientData target)
    (hrad : IsUnipotentRadical Q.radicalInclusion)
    {a : characterLattice S} (ha : a ∈ relativeRoots iS)
    {g : rationalPoints G} (hg : g ∈ rootGroupPoints iS a)
    (hzero : torusFieldRestrictedRootFunctionFamily (k := k) (K := K)
      hS hT hE (D.isRootDatumValuation_of_mem x.mem)
      ((CommGroupScheme.baseChange (algebraBaseMap k K)).map f) a g = 0) :
    g ∉ Q.positivePoints := by
  intro hgpos
  exact (not_lt_of_ge hzero.le)
    (D.strictPositive_of_mem_positivePoints_of_parabolicRootComparisons f hS hT hE
      hmodels Q hrad ha hg hgpos)

end KPApartmentData

end Langlands.Geometry.Building
