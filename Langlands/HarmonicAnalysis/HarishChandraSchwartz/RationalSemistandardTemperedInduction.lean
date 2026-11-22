import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalSemistandardOrbitSections
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalXiChangeMinimal
import Langlands.Representation.Exponents.ArbitraryParabolicLeviPoints

/-! # Tempered induction on the actual semistandard index -/

noncomputable section

universe u uV

open AlgebraicGeometry CategoryTheory
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.Plancherel Langlands.Aubert.General
open Langlands.Aubert.General.RepresentedParabolic (subgroupCongrContinuous)

namespace Langlands.HarishChandraSchwartz.RationalSemistandard

attribute [local instance] rationalWeightsIsAffine rationalWeightsTopology
  rationalWeightsTopologicalGroup rationalWeightsT2Field rationalWeightsLocallyCompact
  rationalWeightsMeasurableSpace rationalWeightsBorelSpace rationalInducedSecondCountable
  rationalInducedT2 rationalInducedNonarchimedean

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom]
  {S : CommGroupScheme (Spec (CommRingCat.of F))} {i : S.toGrp ⟶ G}
  (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
  {ν ξ : cocharacterLattice S} (hξ : IsGenericCocharacter i ξ)
  {J : Set (characterLattice S)} (hJ : J ⊆ simpleRelativeRoots i ξ)
  (p : SemistandardSpectralIndex i)
  (hp : p = SemistandardSpectralIndex.ofStandard hG hi ξ hξ J hJ)
  {K : OpenSubgroup (rationalPoints G)}
  (hKc : IsCompact (K : Set (rationalPoints G)))
  (hPK : IsIwasawaPair (standardParabolicPoints i ν ∅) K.toSubgroup)
  (hMK : IsIwasawaPair ((standardParabolicPoints i ξ ∅).subgroupOf (standardLeviPoints i ξ J))
    (K.toSubgroup.subgroupOf (standardLeviPoints i ξ J)))
  {N : ℕ} [Nonempty (Fin N)] (ρ : MatrixRepresentation G (Fin N))
  (A : SmoothRep.{0, u, uV} ℂ (levi p))

/-- III.2.3 for the actual semistandard triple with the same matrix height
and the Levi Xi of a chamber in which the triple is standard. -/
def SemistandardTemperedInductionStatement : Prop :=
  IsGenericCocharacter i ν → IsClosedSubgroup ρ →
    K.toSubgroup ≤ rationalHeightSubgroup (F := F) ρ → A.IsAdmissible →
    HasTemperedCoefficients
      (rationalLeviXi hKc hMK ∘ subgroupCongrContinuous (congrArg levi hp))
      (fun x => rationalHeight (F := F) ρ (x : rationalPoints G)) A.representation →
    HasTemperedCoefficients (rationalXi hKc hPK) (rationalHeight (F := F) ρ)
      ((normalizedInductionFunctor (decomposition p) (isClosed_radical p)).obj A).representation

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
/-- Change the minimal parabolic at the same compact, apply the published
standard theorem and return to the original ambient spherical weight. -/
theorem semistandardTemperedInduction :
    SemistandardTemperedInductionStatement hG hi hξ hJ p hp hKc hPK hMK ρ A := by
  intro hν hρ hKρ hA hT
  subst p
  classical
  let : Fintype (RationalPointFamily.SimpleRoot i ξ) :=
    (hi.isSplitSubtorus.1.finite_simpleRelativeRoots i ξ).fintype
  let I : Finset (RationalPointFamily.SimpleRoot i ξ) :=
    Finset.univ.filter (fun α => (α : characterLattice S) ∈ J)
  have hI : RationalPointFamily.rootSet i ξ I = J := by
    ext α
    constructor
    · rintro ⟨β, hβ, rfl⟩
      exact (Finset.mem_filter.mp hβ).2
    · intro hα
      exact ⟨⟨α, hJ hα⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hα⟩, rfl⟩
  have hPKξ := IsIwasawaPair.rationalChangeMinimal hG hi hν hξ hPK
  have ht := rationalHasTemperedCoefficients_normalizedInduction ρ hG hi hξ hJ I hI
    K hKc hPKξ hMK hρ hKρ A hA hT
  rw [funext (rationalXi_changeMinimal hG hi hν hξ K.isOpen hKc hPK hPKξ)] at ht
  exact ht

end Langlands.HarishChandraSchwartz.RationalSemistandard
