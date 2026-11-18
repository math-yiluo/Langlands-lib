import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalSemistandardFourierThetaSupport
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalStrictlyLowerRankProperLeviFiniteness

/-! # The actual proper Fourier truncation in Waldspurger VIII.2 -/

noncomputable section

universe u uV

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj NNReal
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology
open Langlands.Aubert.General Langlands.Plancherel

namespace Langlands.HarishChandraSchwartz

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {S : CommGroupScheme (Spec (CommRingCat.of F))}
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom] {i : S.toGrp ⟶ G}

attribute [local instance] rationalWeightsIsAffine rationalWeightsTopology
  rationalWeightsTopologicalGroup rationalWeightsT2Field rationalWeightsLocallyCompact
  rationalWeightsMeasurableSpace rationalWeightsBorelSpace rationalInducedSecondCountable
  rationalInducedT2 rationalInducedNonarchimedean

open RationalSemistandard

variable {nu : cocharacterLattice S}
  (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
  (hnu : IsGenericCocharacter i nu)
  {K : OpenSubgroup (rationalPoints G)} (hKc : IsCompact (K : Set (rationalPoints G)))
  (hPK : IsIwasawaPair (standardParabolicPoints i nu ∅) (K : Subgroup (rationalPoints G)))
  {N : ℕ} [Nonempty (Fin N)] (rho : MatrixRepresentation G (Fin N))
  {muG : Measure (rationalPoints G)} [muG.IsMulLeftInvariant] [muG.IsMulRightInvariant]
  (hsw : SquareIntegrableWeight muG (rationalXi hKc hPK) (rationalHeight (F := F) rho))

local instance properFourierCompactOpen : Nonempty (CompactOpenSubgroup (rationalPoints G)) :=
  ⟨Langlands.BruhatTits.rationalPointCompactOpenSubgroup F G⟩

variable {T : SemistandardSpectralIndex i → CommGroupScheme (Spec (CommRingCat.of F))}
  (a : ∀ p, (T p).toGrp ⟶ (chosenLeviModel p).scheme)
  (ha : ∀ p, IsSplitComponent (a p))
  [∀ p, ((chosenLeviModel p).splitCenter (a p)).Normal]
  [∀ p, MeasurableSpace (levi p ⧸ (chosenLeviModel p).splitCenter (a p))]
  [∀ p, BorelSpace (levi p ⧸ (chosenLeviModel p).splitCenter (a p))]
  (muM : ∀ p, Measure (levi p ⧸ (chosenLeviModel p).splitCenter (a p)))
  [∀ p, (muM p).IsHaarMeasure] [∀ p, (muM p).IsInvInvariant]
  (d : ∀ p : SemistandardSpectralIndex i, CompactData p)
  (hdelta : ∀ p : SemistandardSpectralIndex i, ModularNormalization p)
  (hT : ∀ (p : SemistandardSpectralIndex i)
    (A : IrreducibleAdmissibleRep.{0, u, uV} (k := ℂ) (G := levi p)),
    IsSquareIntegrableModCentralSubgroup ((chosenLeviModel p).splitCenter (a p))
      ((chosenLeviModel p).splitCenter_le_center (a p) (ha p)) A.obj.representation (muM p) →
    HasTemperedCoefficients (rationalXi hKc hPK) (rationalHeight (F := F) rho)
      ((normalizedInductionFunctor (decomposition p) (isClosed_radical p)).obj A.obj).representation)

/-- The linear family in VIII.2 before restriction to finitely supported
smooth sections. It composes the actual Fourier family with the proper cutoff. -/
def rationalSemistandardProperFourier :
    RationalSchwartzSpace hKc hPK rho →ₗ[ℂ] RationalSemistandardThetaSections.{u, uV} a ha muM :=
  (rationalSemistandardThetaProperPart.{u, uV} a ha muM).comp
    (rationalSemistandardFourierFamily hG hi hnu hKc hPK rho hsw a ha muM d hdelta hT)

theorem rationalSemistandardProperFourier_apply_of_isProper
    (f : RationalSchwartzSpace hKc hPK rho) {t : RationalSemistandardTheta.{u, uV} a ha muM}
    (ht : t.1.IsProper) :
    rationalSemistandardProperFourier hG hi hnu hKc hPK rho hsw a ha muM d hdelta hT f t =
      rationalSemistandardFourierFamily hG hi hnu hKc hPK rho hsw a ha muM d hdelta hT f t :=
  rationalSemistandardThetaProperPart_apply_of_mem ht _

theorem rationalSemistandardProperFourier_apply_of_parabolic_eq_top
    (f : RationalSchwartzSpace hKc hPK rho) {t : RationalSemistandardTheta.{u, uV} a ha muM}
    (ht : t.1.parabolic = ⊤) :
    rationalSemistandardProperFourier hG hi hnu hKc hPK rho hsw a ha muM d hdelta hT f t = 0 :=
  rationalSemistandardThetaProperPart_apply_of_mem_group ht _

/-- The support of the truncation is the proper part of the actual Fourier
support. -/
theorem rationalSemistandardProperFourier_support (f : RationalSchwartzSpace hKc hPK rho) :
    rationalSemistandardThetaSupport.{u, uV} a ha muM
        (rationalSemistandardProperFourier hG hi hnu hKc hPK rho hsw a ha muM d hdelta hT f) =
      rationalSemistandardThetaSupport.{u, uV} a ha muM
        (rationalSemistandardFourierFamily hG hi hnu hKc hPK rho hsw a ha muM d hdelta hT f) ∩
        rationalSemistandardThetaProper.{u, uV} a ha muM :=
  rationalSemistandardThetaSupport_properPart a ha muM _

/-- The truncation vanishes exactly when the actual Fourier family vanishes
at every proper index. -/
theorem rationalSemistandardProperFourier_eq_zero_iff (f : RationalSchwartzSpace hKc hPK rho) :
    rationalSemistandardProperFourier hG hi hnu hKc hPK rho hsw a ha muM d hdelta hT f = 0 ↔
      ∀ t : RationalSemistandardTheta.{u, uV} a ha muM, t.1.IsProper →
        rationalSemistandardFourierFamily hG hi hnu hKc hPK rho hsw a ha muM d hdelta hT f t = 0 := by
  constructor
  · intro h t ht
    rw [← rationalSemistandardProperFourier_apply_of_isProper hG hi hnu hKc hPK rho hsw
      a ha muM d hdelta hT f ht, h, Pi.zero_apply]
  · intro h
    funext t
    by_cases ht : t.1.IsProper
    · rw [rationalSemistandardProperFourier_apply_of_isProper hG hi hnu hKc hPK rho hsw
        a ha muM d hdelta hT f ht, h t ht, Pi.zero_apply]
    · exact rationalSemistandardProperFourier_apply_of_parabolic_eq_top hG hi hnu hKc hPK rho hsw
        a ha muM d hdelta hT f ((t.1.not_isProper_iff).mp ht)

open Classical in
/-- Changing the representative of the actual unitary orbit retains the
Fourier section at a proper index and transports zero to zero at a group index. -/
theorem rationalSemistandardProperFourier_baseChange
    (t : RationalSemistandardTheta.{u, uV} a ha muM)
    (pi' : IrreducibleAdmissibleRep.{0, u, uV} (k := ℂ) (G := levi t.1))
    (hsq' : IsSquareIntegrableModCentralSubgroup ((chosenLeviModel t.1).splitCenter (a t.1))
      ((chosenLeviModel t.1).splitCenter_le_center (a t.1) (ha t.1)) pi'.obj.representation (muM t.1))
    (hO : (Quotient.mk _ (discreteSeriesClass ((chosenLeviModel t.1).splitCenter (a t.1))
      ((chosenLeviModel t.1).splitCenter_le_center (a t.1) (ha t.1)) (muM t.1) pi' hsq') :
      OrbitClass (chosenLeviModel t.1) (a t.1) (ha t.1) (muM t.1)) = t.2)
    (f : RationalSchwartzSpace hKc hPK rho) :
    orbitSectionsBaseEquiv (chosenLeviModel t.1) (a t.1) (ha t.1) (muM t.1) t.2 pi' hsq' hO
        (rationalSemistandardProperFourier hG hi hnu hKc hPK rho hsw a ha muM d hdelta hT f t) =
      if t.1.IsProper then
        rationalSemistandardFourierOrbit hG hi hnu hKc hPK rho hsw
          t.1 (chosenLeviModel t.1) (d t.1) (hdelta t.1) pi'
          ((chosenLeviModel t.1).splitCenter (a t.1))
          ((chosenLeviModel t.1).splitCenter_le_center (a t.1) (ha t.1)) (muM t.1) hsq'
          (fun A => hT t.1 A.val (unitaryOrbitRepresentative_isDiscreteSeries _ pi' _ _ _ hsq' A)) f
      else 0 := by
  split_ifs with ht
  · rw [rationalSemistandardProperFourier_apply_of_isProper hG hi hnu hKc hPK rho hsw
      a ha muM d hdelta hT f ht]
    exact rationalSemistandardFourierFamily_baseChange hG hi hnu hKc hPK rho hsw
      a ha muM d hdelta hT t pi' hsq' hO f
  · rw [rationalSemistandardProperFourier_apply_of_parabolic_eq_top hG hi hnu hKc hPK rho hsw
      a ha muM d hdelta hT f ((t.1.not_isProper_iff).mp ht), map_zero]

/-- The actual inducing equivalences, including self-twists, still give
coherence in every component after truncation. -/
theorem rationalSemistandardProperFourier_coherent [muG.IsInvInvariant]
    (f : RationalSchwartzSpace hKc hPK rho) (t : RationalSemistandardTheta.{u, uV} a ha muM) :
    rationalSemistandardProperFourier hG hi hnu hKc hPK rho hsw a ha muM d hdelta hT f t ∈
      coherentProductInducedOrbitSections (chosenLeviModel t.1).normCharacters
        (orbitRepresentative (chosenLeviModel t.1) (a t.1) (ha t.1) (muM t.1) t.2)
        (decomposition t.1) (isClosed_radical t.1) := by
  by_cases ht : t.1.IsProper
  · rw [rationalSemistandardProperFourier_apply_of_isProper hG hi hnu hKc hPK rho hsw
      a ha muM d hdelta hT f ht]
    exact rationalSemistandardFourierFamily_coherent hG hi hnu hKc hPK rho hsw
      a ha muM d hdelta hT f t
  · rw [rationalSemistandardProperFourier_apply_of_parabolic_eq_top hG hi hnu hKc hPK rho hsw
      a ha muM d hdelta hT f ((t.1.not_isProper_iff).mp ht)]
    exact Submodule.zero_mem _

/-- The raw truncation is equivariant for the actual `G × G` actions.
Translation acts within each index, so it preserves both cutoff branches. -/
theorem rationalSemistandardProperFourier_translate (g1 g2 : rationalPoints G)
    (f : RationalSchwartzSpace hKc hPK rho) :
    rationalSemistandardProperFourier hG hi hnu hKc hPK rho hsw a ha muM d hdelta hT
        (Space.translate (rationalTranslationWeights K.isOpen hKc hPK rho) g1 g2 f) =
      rationalSemistandardFourierProductRepresentation a ha muM (g1, g2)
        (rationalSemistandardProperFourier hG hi hnu hKc hPK rho hsw a ha muM d hdelta hT f) := by
  change rationalSemistandardThetaProperPart a ha muM
      (rationalSemistandardFourierFamily hG hi hnu hKc hPK rho hsw a ha muM d hdelta hT _) =
    rationalSemistandardFourierProductRepresentation a ha muM (g1, g2)
      (rationalSemistandardThetaProperPart a ha muM
        (rationalSemistandardFourierFamily hG hi hnu hKc hPK rho hsw a ha muM d hdelta hT f))
  rw [rationalSemistandardFourierFamily_translate]
  funext t
  change rationalSemistandardThetaProperPart a ha muM
      (rationalSemistandardFourierProductRepresentation a ha muM (g1, g2) _) t =
    productInducedOrbitRepresentation (decomposition t.1) (isClosed_radical t.1)
      (chosenLeviModel t.1).normCharacters
      (orbitRepresentative (chosenLeviModel t.1) (a t.1) (ha t.1) (muM t.1) t.2) (g1, g2)
      (rationalSemistandardThetaProperPart a ha muM _ t)
  by_cases ht : t ∈ rationalSemistandardThetaProper.{u, uV} a ha muM
  · rw [rationalSemistandardThetaProperPart_apply_of_mem ht,
      rationalSemistandardThetaProperPart_apply_of_mem ht]
    rfl
  · rw [rationalSemistandardThetaProperPart_apply_of_not_mem ht,
      rationalSemistandardThetaProperPart_apply_of_not_mem ht, map_zero]

/-- In relative semisimple rank zero the proper Fourier truncation is zero,
conditional on the actual proper-Levi rank comparison. -/
theorem rationalSemistandardProperFourier_eq_zero_of_rank_zero
    (hrank : SemistandardProperLeviRankStatement.{u}) (hzero : relativeRootRank i = 0) :
    rationalSemistandardProperFourier hG hi hnu hKc hPK rho hsw a ha muM d hdelta hT = 0 := by
  apply LinearMap.ext
  intro f
  funext t
  exact rationalSemistandardProperFourier_apply_of_parabolic_eq_top hG hi hnu hKc hPK rho hsw
    a ha muM d hdelta hT f (semistandardParabolic_eq_top_of_rank_zero hrank hG hi hzero t.1)

/-! ## Support and smoothness from the lower-rank finiteness input -/

/-- Specialize the lower-rank input to the proper Levis, then use the actual
Fourier support comparison and the proper version of VIII.1.3. -/
theorem rationalProperSemistandardFourierFiniteSupport_of_strictlyLowerRank
    (hrank : SemistandardProperLeviRankStatement.{u})
    (hgeo : Finite (SemistandardSpectralIndex i))
    (hcomp : RationalProperSemistandardNormalLevelFixedComparison.{u, uV} (i := i) K)
    (hfin : RationalStrictlyLowerRankOrbitFinitenessStatement.{u, uV} (relativeRootRank i)) :
    RationalProperSemistandardFourierFiniteSupportStatement hG hi hnu hKc hPK rho hsw
      a ha muM d hdelta hT :=
  rationalProperSemistandardFourierFiniteSupport_of_fixedFinite hG hi hnu hKc hPK rho hsw
    a ha muM d hdelta hT
    (finite_rationalProperSemistandardThetaFixed a ha muM K hKc hgeo hcomp
      (properLeviOrbitFiniteness_of_strictlyLowerRank hrank hG hi hfin))

/-- The actual truncation has finite support under the strictly lower-rank
VIII.1.2 input, with rank comparison and proper normal-level comparison
explicit. -/
def RationalStrictlyLowerRankProperFourierFiniteSupportStatement : Prop :=
  SemistandardProperLeviRankStatement.{u} →
    Finite (SemistandardSpectralIndex i) →
    RationalProperSemistandardNormalLevelFixedComparison.{u, uV} (i := i) K →
    RationalStrictlyLowerRankOrbitFinitenessStatement.{u, uV} (relativeRootRank i) →
    ∀ f : RationalSchwartzSpace hKc hPK rho,
      (rationalSemistandardThetaSupport.{u, uV} a ha muM
        (rationalSemistandardProperFourier hG hi hnu hKc hPK rho hsw a ha muM d hdelta hT f)).Finite

theorem rationalStrictlyLowerRankProperFourierFiniteSupport :
    RationalStrictlyLowerRankProperFourierFiniteSupportStatement hG hi hnu hKc hPK rho hsw
      a ha muM d hdelta hT := by
  intro hrank hgeo hcomp hfin f
  rw [rationalSemistandardProperFourier_support]
  exact rationalProperSemistandardFourierFiniteSupport_of_strictlyLowerRank hG hi hnu hKc hPK rho hsw
    a ha muM d hdelta hT hrank hgeo hcomp hfin f

section Smooth

local instance properFourierParabolicLC (p : SemistandardSpectralIndex i) :
    LocallyCompactSpace (parabolic p) :=
  (isClosed_parabolic p).locallyCompactSpace

variable (hrank : SemistandardProperLeviRankStatement.{u})
  (hgeo : Finite (SemistandardSpectralIndex i))
  (hcomp : RationalProperSemistandardNormalLevelFixedComparison.{u, uV} (i := i) K)
  (hfin : RationalStrictlyLowerRankOrbitFinitenessStatement.{u, uV} (relativeRootRank i))
  (hS : RationalSemistandardFourierFamilySmoothnessStatement hG hi hnu hKc hPK rho hsw
    a ha muM d hdelta hT)
  (hin : ∀ t : RationalSemistandardTheta.{u, uV} a ha muM,
    ∃ (muL : Measure (levi t.1)) (muU : Measure (radical t.1)) (XiM sigmaM : levi t.1 → ℝ),
      RationalSemistandardFourierAnalyticInputs (muG := muG) hKc hPK rho
        t.1 (chosenLeviModel t.1) (d t.1)
        (orbitRepresentative (chosenLeviModel t.1) (a t.1) (ha t.1) (muM t.1) t.2)
        muL muU XiM sigmaM)

/-- The actual truncation as a finitely supported smooth family, using full
component smoothness and proper-only support from smaller ranks. -/
def rationalSemistandardProperFourierSmooth :
    RationalSchwartzSpace hKc hPK rho →ₗ[ℂ] rationalSemistandardThetaSmoothSections.{u, uV} a ha muM d :=
  rationalSemistandardFourierThetaProperSmoothFamily hG hi hnu hKc hPK rho hsw a ha muM d hdelta hT
    (fun f t _ => rationalSemistandardFourierFamily_mem_componentSpace_of_smoothness
      hG hi hnu hKc hPK rho hsw a ha muM d hdelta hT hS hin f t)
    (rationalProperSemistandardFourierFiniteSupport_of_strictlyLowerRank hG hi hnu hKc hPK rho hsw
      a ha muM d hdelta hT hrank hgeo hcomp hfin)

@[simp] theorem rationalSemistandardProperFourierSmooth_val (f : RationalSchwartzSpace hKc hPK rho) :
    (rationalSemistandardProperFourierSmooth hG hi hnu hKc hPK rho hsw a ha muM d hdelta hT
      hrank hgeo hcomp hfin hS hin f).val =
      rationalSemistandardProperFourier hG hi hnu hKc hPK rho hsw a ha muM d hdelta hT f := rfl

end Smooth

end Langlands.HarishChandraSchwartz
