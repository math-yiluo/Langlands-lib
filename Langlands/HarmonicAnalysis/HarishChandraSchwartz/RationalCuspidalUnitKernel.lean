import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalCuspidalUnit
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalCuspidalCentralKernelPairing
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalCuspidalConjugationStatement

/-! # The cuspidal unit `°e` and the hypotheses of the local kernel step of Proposition VIII.4.1

The predicate `IsRationalCuspidalUnit` (properties of `°e` stated for the degree-zero laws) and
the structure `IsRationalCuspidalLevelKernel` (properties of `°e` stated for the kernel step) list
the same five properties. This module proves that they are equivalent and bundles the six named
degree-zero laws of a complex-linear operator `P` on the actual rational Schwartz space as
`IsRationalDegreeZeroOperator`. For such `P` and every compact open subgroup `H`, `°e = P(1_H)`
satisfies `IsRationalCuspidalLevelKernel`. The module also reads the VIII.3.2 integrability form
`RationalLevelKernelConjugationIntegrable` at a cuspidal `E`, in particular at `°e`, off the
Library's closed statement `RationalCuspidalConjugationIntegrabilityStatement`. These are the two
premises on `°e` of the local kernel step.
-/
noncomputable section

universe u

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj ComplexConjugate
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology Langlands.Plancherel
open Langlands.Aubert.General Langlands.QuotientIntegration Langlands.BruhatTits.SpecialCompact

namespace Langlands.HarishChandraSchwartz

attribute [local instance] rationalWeightsIsAffine rationalWeightsTopology
  rationalWeightsTopologicalGroup rationalWeightsT2Field rationalWeightsLocallyCompact
  rationalWeightsMeasurableSpace rationalWeightsBorelSpace

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {S T : CommGroupScheme (Spec (CommRingCat.of F))}
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom]
  {i : S.toGrp ⟶ G} {ν : cocharacterLattice S} {s : T.toGrp ⟶ G}
  {K : OpenSubgroup (rationalPoints G)}
  (hKc : IsCompact (K : Set (rationalPoints G)))
  (hPK : IsIwasawaPair (standardParabolicPoints i ν ∅) (K : Subgroup (rationalPoints G)))
  {N : ℕ} [Nonempty (Fin N)] (ρ : MatrixRepresentation G (Fin N))

/-- The two interfaces for `°e` agree: `IsRationalCuspidalUnit` for the underlying subgroup of an
open subgroup `H` is equivalent to `IsRationalCuspidalLevelKernel` for `H`. -/
theorem isRationalCuspidalUnit_iff_isRationalCuspidalLevelKernel
    (μG : Measure (rationalPoints G)) (H : OpenSubgroup (rationalPoints G))
    (E : RationalSchwartzSpace hKc hPK ρ) :
    IsRationalCuspidalUnit hKc hPK ρ μG H.toSubgroup E ↔
      IsRationalCuspidalLevelKernel hKc hPK ρ μG H E := by
  constructor
  · rintro ⟨hlevel, hconj, hinv, hsupp, hconv⟩
    exact
      { mem_level := hlevel
        conj_eq := hconj
        inv_eq := hinv
        eq_zero_of_not_mem := fun x hx => by
          by_contra h
          exact hx (hsupp x h)
        convolution_eq := fun φ hφ x => hconv φ hφ x }
  · intro hE
    exact ⟨hE.mem_level, hE.conj_eq, hE.inv_eq,
      fun x hx => by
        by_contra h
        exact hx (hE.eq_zero_of_not_mem x h),
      fun φ hφ x => hE.convolution_eq φ hφ x⟩

/-- `IsRationalCuspidalUnit` gives the hypothesis `IsRationalCuspidalLevelKernel` of the local
kernel step. -/
theorem IsRationalCuspidalUnit.isRationalCuspidalLevelKernel
    {μG : Measure (rationalPoints G)} {H : OpenSubgroup (rationalPoints G)}
    {E : RationalSchwartzSpace hKc hPK ρ}
    (hE : IsRationalCuspidalUnit hKc hPK ρ μG H.toSubgroup E) :
    IsRationalCuspidalLevelKernel hKc hPK ρ μG H E :=
  (isRationalCuspidalUnit_iff_isRationalCuspidalLevelKernel hKc hPK ρ μG H E).mp hE

/-- **The degree-zero laws, bundled.** A complex-linear operator `P` on the actual rational
Schwartz space satisfies the six named laws of `RationalCuspidalUnit`: range in `°C(G)`
(Lemma VIII.2.1), two-sided translation equivariance (the "relation évidente" of the proof of
Proposition VIII.4.1), commutation with conjugation, with `f ↦ fˇ` and with unitary unramified
twists (Remark VIII.2.2), and the left convolution identity of Lemma VIII.2.3 for `μG`. -/
def IsRationalDegreeZeroOperator (μG : Measure (rationalPoints G))
    (P : RationalSchwartzSpace hKc hPK ρ →ₗ[ℂ] RationalSchwartzSpace hKc hPK ρ) : Prop :=
  RationalDegreeZeroRangeLaw hKc hPK ρ P ∧ RationalDegreeZeroTranslationLaw hKc hPK ρ P ∧
    RationalDegreeZeroConjLaw hKc hPK ρ P ∧ RationalDegreeZeroCheckLaw hKc hPK ρ P ∧
    RationalDegreeZeroTwistLaw hKc hPK ρ P ∧ RationalDegreeZeroLeftConvolutionLaw hKc hPK ρ P μG

/-- For an operator with the degree-zero laws and a Haar measure `μG`, `°e = P(1_H)` satisfies
`IsRationalCuspidalUnit` for every compact open subgroup `H`. -/
theorem IsRationalDegreeZeroOperator.isRationalCuspidalUnit
    {μG : Measure (rationalPoints G)} [μG.IsHaarMeasure]
    {P : RationalSchwartzSpace hKc hPK ρ →ₗ[ℂ] RationalSchwartzSpace hKc hPK ρ}
    (hP : IsRationalDegreeZeroOperator hKc hPK ρ μG P)
    (H : CompactOpenSubgroup (rationalPoints G)) :
    IsRationalCuspidalUnit hKc hPK ρ μG H.toSubgroup
      (P (rationalSubgroupIndicator hKc hPK ρ μG H)) :=
  isRationalCuspidalUnit_of_degreeZeroLaws hKc hPK ρ μG H hP.1 hP.2.1 hP.2.2.1 hP.2.2.2.1
    hP.2.2.2.2.1 hP.2.2.2.2.2

/-- For an operator with the degree-zero laws and a Haar measure `μG`, `°e = P(1_H)` satisfies
the hypothesis `IsRationalCuspidalLevelKernel` of the local kernel step. -/
theorem IsRationalDegreeZeroOperator.isRationalCuspidalLevelKernel
    {μG : Measure (rationalPoints G)} [μG.IsHaarMeasure]
    {P : RationalSchwartzSpace hKc hPK ρ →ₗ[ℂ] RationalSchwartzSpace hKc hPK ρ}
    (hP : IsRationalDegreeZeroOperator hKc hPK ρ μG P)
    (H : CompactOpenSubgroup (rationalPoints G)) :
    IsRationalCuspidalLevelKernel hKc hPK ρ μG H.1
      (P (rationalSubgroupIndicator hKc hPK ρ μG H)) :=
  (hP.isRationalCuspidalUnit hKc hPK ρ H).isRationalCuspidalLevelKernel hKc hPK ρ

/-- **The VIII.3.2 integrability form at a cuspidal `E`, from the closed Corollary VIII.3.2.**
Its second conjunct, at `f₁ = E`, for every compatible quotient measure. The structural data are
those of `RationalCuspidalConjugationIntegrabilityStatement`. -/
theorem RationalCuspidalConjugationIntegrabilityStatement.levelKernelConjugationIntegrable
    (h32 : RationalCuspidalConjugationIntegrabilityStatement.{u})
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i) (hν : IsGenericCocharacter i ν)
    {K0 : Subgroup (rationalPoints G)} (hK0 : SimultaneousStandardBasisAt i ν K0)
    (hρ : IsClosedSubgroup ρ) (hs : IsSplitComponent s)
    (muA : Measure (rationalPoints.map s).range) [muA.IsHaarMeasure]
    (μG : Measure (rationalPoints G)) [hμG : μG.IsHaarMeasure]
    {E : RationalSchwartzSpace hKc hPK ρ} (hE : E ∈ rationalCuspidalSubmodule hKc hPK ρ) :
    RationalLevelKernelConjugationIntegrable hKc hPK ρ hs muA μG E := by
  intro _ _ _ muQ hQ f₂
  exact (h32 F G hG S i hi ν hν K0 hK0 K hKc hPK N ρ hρ T s hs μG hμG muA muQ hQ).2 E hE f₂

/-- **The VIII.3.2 integrability form at `°e`.** For an operator with the degree-zero laws, a Haar
measure `μG` and a compact open subgroup `H`, the closed Corollary VIII.3.2 gives
`RationalLevelKernelConjugationIntegrable` at `°e = P(1_H)`, which is cuspidal by the range law. -/
theorem IsRationalDegreeZeroOperator.levelKernelConjugationIntegrable
    (h32 : RationalCuspidalConjugationIntegrabilityStatement.{u})
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i) (hν : IsGenericCocharacter i ν)
    {K0 : Subgroup (rationalPoints G)} (hK0 : SimultaneousStandardBasisAt i ν K0)
    (hρ : IsClosedSubgroup ρ) (hs : IsSplitComponent s)
    (muA : Measure (rationalPoints.map s).range) [muA.IsHaarMeasure]
    {μG : Measure (rationalPoints G)} [μG.IsHaarMeasure]
    {P : RationalSchwartzSpace hKc hPK ρ →ₗ[ℂ] RationalSchwartzSpace hKc hPK ρ}
    (hP : IsRationalDegreeZeroOperator hKc hPK ρ μG P)
    (H : CompactOpenSubgroup (rationalPoints G)) :
    RationalLevelKernelConjugationIntegrable hKc hPK ρ hs muA μG
      (P (rationalSubgroupIndicator hKc hPK ρ μG H)) :=
  h32.levelKernelConjugationIntegrable hKc hPK ρ hG hi hν hK0 hρ hs muA μG (hP.1 _)

end Langlands.HarishChandraSchwartz
