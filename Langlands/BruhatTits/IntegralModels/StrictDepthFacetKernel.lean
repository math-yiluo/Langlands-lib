import Langlands.BruhatTits.IntegralModels.IntegralFacetReflectionCriterion
import Langlands.BruhatTits.IntegralModels.IntegralOppositeFactorsStatement
import Langlands.BruhatTits.IntegralModels.DepthZeroReduction
import Langlands.GroupScheme.Rational.RootFactorPairTransport
import Langlands.GroupScheme.Rational.CrossTorusLieTransport

/-! # Strict-depth sections and the facet reduction kernel -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj ValuativeRel
open Langlands.GroupScheme Langlands.GroupScheme.GaloisPointComparison
open Langlands.Geometry.Building Langlands.LocalGalois.Separable

namespace Langlands.BruhatTits.IntegralModels

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  (P : ParahoricBuildingData G)

/-- Integral sections whose generic points lie in the conjugated strict-depth
root subgroup. -/
def strictDepthIntegralSections (g : rationalPoints G)
    (D : RelativeComponentModelData ↥𝒪[F] F G)
    (a : relativeRoots P.i) (ψ : P.Apartment →ᵃ[ℝ] ℝ) :
    Subgroup D.neutral.integralSections :=
  ((P.apartment.affineRootGroupPlus a ψ).map
    (rationalPoints.map (G.innerIso g).hom)).comap D.neutral.integralPointMap

private instance extensionAffineHom :
    IsAffineHom (baseChanged F (inertiaFixedField F) G).X.hom := by
  change IsAffineHom
    (CategoryTheory.Limits.pullback.snd G.X.hom (baseMap F (inertiaFixedField F)))
  infer_instance

variable
  (C : MaximalUnramified.BuildingData F (baseChanged F (inertiaFixedField F) G))
  (e : P.ReducedBuilding → C.ReducedBuilding) (hinj : Function.Injective e)
  (he : ∀ (g : rationalPoints G) (z : P.ReducedBuilding),
    e (g • z) = rationalExtend F (inertiaFixedField F) G g • e z)
  (E : UnramifiedZeroDatum F (baseChanged F (inertiaFixedField F) G))
  (g : rationalPoints G) (Fa : Set P.Apartment)
  (D : RelativeComponentModelData ↥𝒪[F] F G)
  (hD : D.neutral.baseChangeUnramified.integralPoints =
    E.zeroPoints ⊓ C.pointwiseFixer
      (e '' (P.translatedApartmentMap g '' Fa)))
  (hA : P.SatisfiesApartmentAxioms) (hR : P.HasRootReflections)
  {a : relativeRoots P.i} {ψ : P.Apartment →ᵃ[ℝ] ℝ}
  (hlin : ψ.linear = rootForm P.i a)
  {y : P.Apartment} (hy : y ∈ Fa) (hzero : ψ y = 0)

include hinj he hD hA hR hlin hy hzero

/-- A nonidentity strict-depth point at a zero of the affine functional cannot
have an integral actual reflection. -/
theorem conjugated_reflection_not_integral_of_strictDepth
    {x : rationalPoints G} (hx : x ∈ P.apartment.affineRootGroupPlus a ψ)
    (hx1 : x ≠ 1) {p : rationalPoints G × rationalPoints G}
    (hp : RelativeRoot.IsOppositeFactorPair P.i a.val x p) :
    rationalPoints.map (G.innerIso g).hom (P.reflectionElement hp) ∉
      D.neutral.integralPoints := by
  intro hint
  obtain ⟨hxroot, hlt⟩ :=
    (P.apartment.mem_affineRootGroupPlus_iff hlin y).mp hx
  have hfixed :=
    (conjugated_reflection_mem_integralPoints_iff P C e hinj he E g Fa D hD hA hR
      hxroot hx1 hp).mp hint y hy
  rw [← P.toValuationBuildingData.coe_reflectionFunctional_apply hxroot hx1 y,
    hzero, hfixed] at hlt
  exact (lt_irrefl _ hlt)

/-- Conditional on the integral opposite-factor theorem, every integral
strict-depth point at a facet zero reduces into the supplied radical. -/
theorem conjugated_strictDepth_mem_positivePoints
    (hopp : IntegralOppositeFactorsStatement.{u})
    (T : IntegralTorusData D P.S (P.i ≫ (G.innerIso g).hom))
    (hT : T.IsClosedSplit) (Q : SpecialFibreQuotientData D)
    (hQ : Q.IsReductiveQuotient)
    {x : rationalPoints G} (hx : x ∈ P.apartment.affineRootGroupPlus a ψ)
    (hint : rationalPoints.map (G.innerIso g).hom x ∈ D.neutral.integralPoints) :
    rationalPoints.map (G.innerIso g).hom x ∈ Q.positivePoints := by
  classical
  by_cases hx1 : x = 1
  · rw [hx1, map_one]
    exact Q.positivePoints.one_mem
  have hxroot := ((P.apartment.mem_affineRootGroupPlus_iff hlin y).mp hx).1
  obtain ⟨p, hp⟩ := P.hasOppositeFactorPairs a a.property x hxroot hx1
  by_contra hpos
  have hpair := hp.map (G.innerIso g).hom rfl
  have hxroot' : rationalPoints.map (G.innerIso g).hom x ∈
      rootGroupPoints (P.i ≫ (G.innerIso g).hom) a.val :=
    RelativeRoot.comp_mem_subgroup P.i a.val (G.innerIso g).hom hxroot
  have ha' : a.val ∈ relativeRoots (P.i ≫ (G.innerIso g).hom) := by
    have ht := (roots_mem_of_transport_iff (Iso.refl P.S) (G.innerIso g)
      (j := P.i ≫ (G.innerIso g).hom)
      (by change _ = 𝟙 _ ≫ _; rw [Category.id_comp]) a.val).mpr a.property
    simpa only [relativeRoots, characterLattice.congr_apply, Iso.refl_inv,
      Category.id_comp] using ht
  have hx1' : rationalPoints.map (G.innerIso g).hom x ≠ 1 := by
    intro h
    apply hx1
    apply (cancel_mono (G.innerIso g).hom.hom.hom).mp
    change rationalPoints.map (G.innerIso g).hom x =
      rationalPoints.map (G.innerIso g).hom 1
    simpa only [map_one] using h
  have hfactors :=
    (hopp F G P.isConnectedReductive P.S (P.i ≫ (G.innerIso g).hom)
      (P.isMaximalSplitTorus.comp_iso (G.innerIso g)) D T Q hT hQ
      a.val ha' _ hxroot' hx1' hint _ hpair.1 _ hpair.2.1 hpair.2.2).mpr hpos
  apply conjugated_reflection_not_integral_of_strictDepth P C e hinj he E g Fa D hD
    hA hR hlin hy hzero hx hx1 hp
  change rationalPoints.map (G.innerIso g).hom (p.1 * x * p.2) ∈ _
  rw [map_mul, map_mul]
  exact D.neutral.integralPoints.mul_mem
    (D.neutral.integralPoints.mul_mem hfactors.1 hint) hfactors.2

/-- Conditional on integral opposite factors, all integral strict-depth
sections at a facet zero lie in the actual quotient-reduction kernel. -/
theorem strictDepthIntegralSections_le_reductiveReduction_ker
    (hopp : IntegralOppositeFactorsStatement.{u})
    (T : IntegralTorusData D P.S (P.i ≫ (G.innerIso g).hom))
    (hT : T.IsClosedSplit) (Q : SpecialFibreQuotientData D)
    (hQ : Q.IsReductiveQuotient) :
    strictDepthIntegralSections P g D a ψ ≤ Q.reductiveReduction.ker := by
  intro z hz
  obtain ⟨x, hx, hxeq⟩ := hz
  have hpos := conjugated_strictDepth_mem_positivePoints P C e hinj he E g Fa D hD
    hA hR hlin hy hzero hopp T hT Q hQ hx (hxeq.symm ▸ ⟨z, rfl⟩)
  rw [hxeq, SpecialFibreQuotientData.positivePoints,
    Subgroup.mem_map_iff_mem D.neutral.integralPointMap_injective] at hpos
  rw [← Q.ker_reductiveReduction hQ.2.1] at hpos
  exact hpos

end Langlands.BruhatTits.IntegralModels
