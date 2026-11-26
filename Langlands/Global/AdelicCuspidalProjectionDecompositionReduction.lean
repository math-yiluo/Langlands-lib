import Langlands.Global.AdelicIntertwiningWeakContinuationReduction
import Langlands.Global.AdelicCuspidalProjectionDecompositionReductionStatement
import Langlands.Global.AdelicStandardConstantTerm
import Langlands.GroupScheme.Rational.SplitRankTransport
import Langlands.GroupScheme.Rational.RelativeRoots
import Langlands.Global.AdelicRepresentationHeightPropernessProof
import Langlands.Automorphic.JointAdmissibilityCenter

/-! # Reduction of the cuspidal projection decomposition -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj

set_option autoImplicit false

namespace Langlands.Global.StandardParabolicFamily

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions AdelicGroupPoints

variable {F : Type u} [Field F] [NumberField F]
  {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  (fam : StandardParabolicFamily F G)

local notation "Index" => StandardIndex F G fam.i fam.ν

private theorem leviPairingIntegrand_sub (Q : Index) (f h : AdelicGroupPoints F G → ℂ)
    (g : AdelicGroupPoints F G) (t : AdelicGroupPoints F (fam.M Q) → ℂ) :
    fam.leviPairingIntegrand Q (f - h) g t =
      fam.leviPairingIntegrand Q f g t - fam.leviPairingIntegrand Q h g t := by
  funext x
  simp only [leviPairingIntegrand, Pi.sub_apply, sub_mul]

/-- The difference of two cuspidal projections of one function lies in the fibrewise
cuspidal annihilator. -/
private theorem sub_mem_cuspidalAnnihilator_of_isCuspidalProjection {N d : ℕ}
    {hsmooth : SmoothOfRelativeDimension d G.X.hom}
    {Kinf : Subgroup (InfiniteAdelicGroupPoints F G)} {rho : MatrixRepresentation G (Fin N)}
    {Q : Index} {φ ψ ψ' : AdelicGroupPoints F G → ℂ}
    (h : fam.IsCuspidalProjection hsmooth Kinf rho Q φ ψ)
    (h' : fam.IsCuspidalProjection hsmooth Kinf rho Q φ ψ') :
    fam.InCuspidalAnnihilator Kinf rho Q (ψ' - ψ) := by
  intro t ht g
  obtain ⟨-, hI, heq⟩ := h.2.2 t ht g
  obtain ⟨-, hI', heq'⟩ := h'.2.2 t ht g
  rw [fam.leviPairingIntegrand_sub]
  refine ⟨hI'.sub hI, ?_⟩
  unfold leviPairing
  rw [fam.leviPairingIntegrand_sub]
  simp only [Pi.sub_apply]
  rw [integral_sub hI' hI]
  change fam.leviPairing Q ψ' g t - fam.leviPairing Q ψ g t = 0
  rw [← heq, ← heq', sub_self]

/-- A compact serving the minimal standard parabolic serves every standard parabolic. -/
private theorem isIwasawaCompact_of_minimal {K : Subgroup (AdelicGroupPoints F G)}
    (hK : IsIwasawaCompact (fam.p ⟨∅, Set.empty_subset _⟩) K) (R : Index) :
    IsIwasawaCompact (fam.p R) K := by
  have hle : SubgroupFunctor.range (fam.p ⟨∅, Set.empty_subset _⟩) ≤
      SubgroupFunctor.range (fam.p R) :=
    (fam.le_iff_range_le _ R).mp (Set.empty_subset _)
  have : Mono (fam.p R).hom.hom.left := (fam.isCompatible R).parabolic.isClosedSubgroup.mono
  have hcomp := SubgroupFunctor.rangeFactor_comp (fam.p ⟨∅, Set.empty_subset _⟩) (fam.p R) hle
  exact IsIwasawaCompact.of_comp _ (by rw [hcomp]; exact hK)


/-- For a positive-size embedding, the vanishing criterion makes cuspidal projections unique. -/
private theorem eq_of_isCuspidalProjection_of_pos (hvan : ParabolicCuspidalVanishingStatement.{u})
    {K : Subgroup (AdelicGroupPoints F G)} (hK : IsMaximalCompactSubgroup F G K)
    (hKmin : IsIwasawaCompact (fam.p ⟨∅, Set.empty_subset _⟩) K)
    {N d : ℕ} {rho : MatrixRepresentation G (Fin N)} (hN : 0 < N) (hrho : IsClosedSubgroup rho)
    {hsmooth : SmoothOfRelativeDimension d G.X.hom} {Q : Index}
    {φ ψ ψ' : AdelicGroupPoints F G → ℂ}
    (h : fam.IsCuspidalProjection hsmooth (K.comap (ofInfinite F G).toMonoidHom) rho Q φ ψ)
    (h' : fam.IsCuspidalProjection hsmooth (K.comap (ofInfinite F G).toMonoidHom) rho Q φ ψ') :
    ψ' = ψ := by
  set Kinf := K.comap (ofInfinite F G).toMonoidHom
  have hauto : fam.IsAutomorphicOn hsmooth Kinf rho Q (ψ' - ψ) :=
    (automorphicFunctionsOn (parabolicQuotientSubgroup F (fam.p Q) (fam.iU Q) (fam.l Q))
      Kinf rho hsmooth (adelicDifferentialCommutator_of_smooth F G hsmooth)).sub_mem h'.1 h.1
  have hcusp : fam.IsCuspidalAlong Q (ψ' - ψ) :=
    fam.isCuspidalAlong_sub hsmooth Kinf rho Q h'.1 h.1 h'.2.1 h.2.1
  have h0 := hvan F G fam K hK (fam.isIwasawaCompact_of_minimal hKmin) rho hN hrho Q (ψ' - ψ)
    ⟨hauto.1, hauto.2.1.1, hauto.2.2.2.2⟩ (by
      intro R hRQ
      rcases eq_or_lt_of_le hRQ with rfl | hlt
      · rw [fam.constantTerm_eq_self_of_automorphicOn R hauto]
        exact fam.sub_mem_cuspidalAnnihilator_of_isCuspidalProjection h h'
      · rw [hcusp R hlt]
        exact (fam.cuspidalAnnihilator Kinf rho R).zero_mem)
  exact sub_eq_zero.mp h0


section RankZero

open scoped Classical in
omit [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom] in
/-- On a group with a single adelic point, constant functions are automorphic. -/
private theorem isAutomorphicFunctionOn_one_of_subsingleton
    {H : GroupScheme (Spec (CommRingCat.of F))} [IsAffine H.X.left]
    [hH : Subsingleton (AdelicGroupPoints F H)] {d : ℕ}
    (hsmooth : SmoothOfRelativeDimension d H.X.hom) (hcalc : AdelicDifferentialCommutator F H hsmooth)
    (Γ : Subgroup (AdelicGroupPoints F H)) (Kinf : Subgroup (InfiniteAdelicGroupPoints F H))
    {N : ℕ} (rho : MatrixRepresentation H (Fin N)) :
    IsAutomorphicFunctionOn F H hsmooth hcalc Γ Kinf rho (fun _ => 1) := by
  have hinf : Subsingleton (InfiniteAdelicGroupPoints F H) :=
    ⟨fun a b => by
      have := Subsingleton.elim (ofInfinite F H a) (ofInfinite F H b)
      simpa using congrArg (infinite F H) this⟩
  refine ⟨fun _ _ _ => rfl, ⟨continuous_const, fun b => ?_, ⟨⊤, isOpen_univ, fun _ _ _ => rfl⟩⟩,
    ?_, ?_, ⟨1, one_pos, 0, fun g => by simp⟩⟩
  · exact H.isPlotSmooth_const _ _ 1
  · apply FiniteDimensional.span_of_finite
    exact (Set.finite_singleton (fun _ : AdelicGroupPoints F H => (1 : ℂ))).subset
      (by rintro _ ⟨k, rfl⟩; rfl)
  · have : Finite (InfiniteAdelicGroupPoints F H) := Finite.of_subsingleton
    have hW : FiniteDimensional ℂ (InfinitePlotSmoothFunctions F H) :=
      FiniteDimensional.finiteDimensional_submodule (InfinitePlotSmoothFunctions F H)
    let v : InfinitePlotSmoothFunctions F H := ⟨fun _ => 1, H.isPlotSmooth_const _ _ 1⟩
    obtain ⟨I, hI, hann⟩ := exists_cofiniteIdeal_annihilates_of_finite_centralOrbit
      (InfiniteAdelicGroupPoints.plotSmoothCenterAction F H hsmooth hcalc) v
      (FiniteDimensional.finiteDimensional_submodule _)
    exact ⟨I, hI, fun z hz b h => hann z hz⟩

/-- If the embedding has size zero, the constant function is cuspidal on every standard Levi:
every parabolic subgroup of the Levi is the whole Levi. -/
private theorem isLeviCuspidal_one_of_rank_zero (rho : MatrixRepresentation G (Fin 0))
    (hrho : IsClosedSubgroup rho) (J : Index) :
    fam.IsLeviCuspidal J (fun _ => 1) := by
  intro P' U' p' r _ _ _ _ hne
  exfalso
  apply hne
  have hcl : IsClosedSubgroup (fam.l J ≫ fam.p J ≫ rho) :=
    ((fam.isCompatible J).levi.isClosedSubgroup.comp
      (fam.isCompatible J).parabolic.isClosedSubgroup).comp hrho
  have hmono : Mono (fam.l J ≫ fam.p J ≫ rho).hom.hom := by
    have : IsClosedImmersion (fam.l J ≫ fam.p J ≫ rho).hom.hom.left := hcl
    exact Over.mono_of_mono_left _
  apply SubgroupFunctor.ext
  intro T
  refine eq_top_iff.mpr fun x _ => ?_
  have hx : x = 1 := by
    apply (cancel_mono (fam.l J ≫ fam.p J ≫ rho).hom.hom).mp
    apply (GeneralLinear.pointsEquiv (Fin 0) (CommRingCat.of F) T).injective
    exact Units.ext (Matrix.ext fun i => Fin.elim0 i)
  rw [hx]
  exact ((SubgroupFunctor.range p').carrier T).one_mem

/-- If the embedding has size zero, cuspidal projections are unique: the constant test
function on the single-point Levi detects the value at the single adelic point. -/
private theorem eq_of_isCuspidalProjection_of_rank_zero {d : ℕ}
    {rho : MatrixRepresentation G (Fin 0)} (hrho : IsClosedSubgroup rho)
    {hsmooth : SmoothOfRelativeDimension d G.X.hom}
    {Kinf : Subgroup (InfiniteAdelicGroupPoints F G)}
    {Q : Index} {φ ψ ψ' : AdelicGroupPoints F G → ℂ}
    (h : fam.IsCuspidalProjection hsmooth Kinf rho Q φ ψ)
    (h' : fam.IsCuspidalProjection hsmooth Kinf rho Q φ ψ') :
    ψ' = ψ := by
  have hG : Subsingleton (AdelicGroupPoints F G) :=
    Langlands.Global.subsingleton_adelicGroupPoints_of_rank_zero' rho hrho
  have hcl : IsClosedSubgroup (fam.l Q ≫ fam.p Q ≫ rho) :=
    ((fam.isCompatible Q).levi.isClosedSubgroup.comp
      (fam.isCompatible Q).parabolic.isClosedSubgroup).comp hrho
  have hM : Subsingleton (AdelicGroupPoints F (fam.M Q)) :=
    Langlands.Global.subsingleton_adelicGroupPoints_of_rank_zero' _ hcl
  have ht : fam.IsLeviCuspForm Kinf rho Q (fun _ => 1) :=
    ⟨isAutomorphicFunctionOn_one_of_subsingleton _ _ _ _ _,
      fam.isLeviCuspidal_one_of_rank_zero rho hrho Q⟩
  funext g
  obtain ⟨hI, h0⟩ := fam.sub_mem_cuspidalAnnihilator_of_isCuspidalProjection h h' _ ht g
  have hconst : fam.leviPairingIntegrand Q (ψ' - ψ) g (fun _ => 1) = fun _ => ψ' g - ψ g := by
    funext x
    simp only [leviPairingIntegrand, map_one, mul_one, Pi.sub_apply]
    rw [Subsingleton.elim (_ * g) g]
  rw [hconst] at hI
  unfold leviPairing at h0
  rw [hconst, integral_const, smul_eq_zero] at h0
  by_contra hne
  have hne' : ψ' g - ψ g ≠ 0 := sub_ne_zero.mpr hne
  have hfin : IsFiniteMeasure (normOneRationalQuotientHaarMeasure F (fam.M Q)) :=
    (integrable_const_iff.mp hI).resolve_left hne'
  have : NeZero (normOneRationalQuotientHaarMeasure F (fam.M Q)) :=
    ⟨normOneRationalQuotientHaarMeasure_ne_zero F (fam.M Q)⟩
  rcases h0 with h0 | h0
  · exact (measureReal_univ_pos.ne' h0).elim
  · exact hne' h0

end RankZero

end Langlands.Global.StandardParabolicFamily

namespace Langlands.Global

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions AdelicGroupPoints

/-- The four inputs prove the cuspidal projection decomposition. -/
theorem cuspidalProjectionDecompositionReduction :
    CuspidalProjectionDecompositionReductionStatement.{u} := by
  intro hCT hEx hVan hDec F _ _ G _ _ _ fam K hK hKmin hKlevi N d rho hsmooth hrho Kinf P Q hQP φ hφ
  have hφQ := hCT F G fam Kinf rho hsmooth hrho P Q hQP φ hφ
  obtain ⟨ψ, hψ⟩ := hEx F G fam K hK hKmin hKlevi rho hsmooth hrho Q _ hφQ
  refine ⟨ψ, hψ, fun ψ' hψ' => ?_, ?_⟩
  · rcases Nat.eq_zero_or_pos N with rfl | hN
    · exact fam.eq_of_isCuspidalProjection_of_rank_zero hrho hψ hψ'
    · exact fam.eq_of_isCuspidalProjection_of_pos hVan hK hKmin hN hrho hψ hψ'
  · obtain ⟨s, c, hsum, hc⟩ := hDec F G fam K hK hKmin hKlevi rho hsmooth hrho Q ψ hψ.1
    exact ⟨s, c, ⟨hsum, fun lam hlam => (hc lam hlam).1,
      fun lam hlam => (hc lam hlam).2.2 hψ.2.1, fun lam hlam => (hc lam hlam).2.1⟩⟩

end Langlands.Global
