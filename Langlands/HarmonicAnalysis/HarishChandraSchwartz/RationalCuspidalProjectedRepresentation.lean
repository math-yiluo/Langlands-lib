import Langlands.HarmonicAnalysis.HarishChandraSchwartz.SchwartzProjectedRepresentation
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalCuspidalCentralStatements

/-! # The actual projected cuspidal right-translation representation -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology Langlands.Plancherel
open Langlands.Aubert.General

namespace Langlands.HarishChandraSchwartz

attribute [local instance] rationalWeightsIsAffine rationalWeightsTopology
  rationalWeightsTopologicalGroup rationalWeightsT2Field rationalWeightsLocallyCompact
  rationalWeightsMeasurableSpace rationalWeightsBorelSpace

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom]
  {S T : CommGroupScheme (Spec (CommRingCat.of F))}
  {i : S.toGrp ⟶ G} {ν : cocharacterLattice S}
  {K : OpenSubgroup (rationalPoints G)}
  (hKc : IsCompact (K : Set (rationalPoints G)))
  (hPK : IsIwasawaPair (standardParabolicPoints i ν ∅) K.toSubgroup)
  {N : ℕ} [Nonempty (Fin N)] (ρ : MatrixRepresentation G (Fin N))

private theorem rationalProjected_translationStable :
    IsTranslationStable (rationalTranslationWeights K.isOpen hKc hPK ρ)
      (rationalCuspidalSubmodule hKc hPK ρ) := by
  intro g₁ g₂ f hf I hI muU hmuU
  exact (hf I hI muU hmuU).translate g₁ g₂

variable (s : T.toGrp ⟶ G) (hs : IsSplitComponent s)
  (muA : Measure (rationalPoints.map s).range) (χ : (rationalPoints.map s).range →* ℂˣ)

/-- Right translation on the literal central-image span of `°C(H \ G)`. -/
def rationalCuspidalProjectedLeftSubrepresentation (H : Subgroup (rationalPoints G)) :
    Subrepresentation (Whittaker.rightTranslation ℂ (rationalPoints G)) :=
  projectedLeftSubrepresentation (rationalTranslationWeights K.isOpen hKc hPK ρ)
    (rationalCuspidalSubmodule hKc hPK ρ) (rationalProjected_translationStable hKc hPK ρ)
    hs.isCentralSplitTorus.isCentral.range_le_center muA χ H

@[simp] theorem rationalCuspidalProjectedLeftSubrepresentation_toSubmodule
    (H : Subgroup (rationalPoints G)) :
    (rationalCuspidalProjectedLeftSubrepresentation hKc hPK ρ s hs muA χ H).toSubmodule =
      rationalCuspidalCentralLeftLevelSpan hKc hPK ρ muA χ H := rfl

variable (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
  (hν : IsGenericCocharacter i ν) (hρ : IsClosedSubgroup ρ)
  [muA.IsHaarMeasure] (hχ : Continuous χ) (hu : IsUnitaryCharacter χ)

include hG hi hν hρ hχ hu hs

private theorem rationalProjected_converges
    (hconv : RationalSchwartzCentralConvergenceStatement.{u}) :
    CentralIntegralConvergesOn (rationalCuspidalSubmodule hKc hPK ρ) muA χ :=
  fun f _ x => hconv F G hG S i hi ν hν K hKc hPK N ρ hρ T s hs muA χ hχ hu
    f (Submodule.mem_top) x

/-- Every vector of the actual projected left-level representation is an actual
raw central integral of a cuspidal Schwartz function at that left level. -/
theorem rationalCuspidalProjectedLeftSubrepresentation_mem_image
    (hconv : RationalSchwartzCentralConvergenceStatement.{u})
    (H : Subgroup (rationalPoints G))
    (f : (rationalCuspidalProjectedLeftSubrepresentation hKc hPK ρ s hs muA χ H).toSubmodule) :
    (f : rationalPoints G → ℂ) ∈ rationalCuspidalCentralLeftLevelImage hKc hPK ρ muA χ H := by
  let : Nonempty (CompactOpenSubgroup (rationalPoints G)) := ⟨⟨K, hKc⟩⟩
  exact projectedLeftSubrepresentation_mem_image
    (rationalTranslationWeights K.isOpen hKc hPK ρ)
    (rationalCuspidalSubmodule hKc hPK ρ) (rationalProjected_translationStable hKc hPK ρ)
    hs.isCentralSplitTorus.isCentral.range_le_center muA χ
    (rationalProjected_converges hKc hPK ρ s hs muA χ hG hi hν hρ hχ hu hconv) H f

/-- The actual projected cuspidal right-translation representation is smooth. -/
theorem isSmooth_rationalCuspidalProjectedLeftSubrepresentation
    (hconv : RationalSchwartzCentralConvergenceStatement.{u})
    (H : Subgroup (rationalPoints G)) :
    IsSmooth
      (rationalCuspidalProjectedLeftSubrepresentation hKc hPK ρ s hs muA χ H).toRepresentation := by
  let : Nonempty (CompactOpenSubgroup (rationalPoints G)) := ⟨⟨K, hKc⟩⟩
  exact isSmooth_projectedLeftSubrepresentation
    (rationalTranslationWeights K.isOpen hKc hPK ρ)
    (rationalCuspidalSubmodule hKc hPK ρ) (rationalProjected_translationStable hKc hPK ρ)
    hs.isCentralSplitTorus.isCentral.range_le_center muA χ
    (rationalProjected_converges hKc hPK ρ s hs muA χ hG hi hν hρ hχ hu hconv) H

/-- VIII.4.1 and central convergence give admissibility of the actual projected
cuspidal representation with prescribed compact open left level. -/
theorem RationalCuspidalCentralProjectionFiniteStatement.rightTranslationAdmissible
    (hfinite : RationalCuspidalCentralProjectionFiniteStatement.{u})
    (hconv : RationalSchwartzCentralConvergenceStatement.{u})
    (H : OpenSubgroup (rationalPoints G)) (hH : IsCompact (H : Set (rationalPoints G))) :
    IsAdmissible
      (rationalCuspidalProjectedLeftSubrepresentation hKc hPK ρ s hs muA χ
        H.toSubgroup).toRepresentation := by
  let : Nonempty (CompactOpenSubgroup (rationalPoints G)) := ⟨⟨K, hKc⟩⟩
  apply isAdmissible_projectedLeftSubrepresentation
    (rationalTranslationWeights K.isOpen hKc hPK ρ)
    (rationalCuspidalSubmodule hKc hPK ρ) (rationalProjected_translationStable hKc hPK ρ)
    hs.isCentralSplitTorus.isCentral.range_le_center muA χ
    (rationalProjected_converges hKc hPK ρ s hs muA χ hG hi hν hρ hχ hu hconv) H hH
  intro J hJ
  exact (hfinite F G hG S i hi ν hν K hKc hPK N ρ hρ T s hs muA χ hχ hu J hJ).2

end Langlands.HarishChandraSchwartz
