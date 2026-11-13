import Langlands.Geometry.Building.KPTorusCharacterFiltration
import Langlands.Geometry.Building.KPMoyPrasadDoubleRootStatement
import Langlands.Geometry.Building.TorusValuationBuildingConstruction
import Langlands.Geometry.Building.KPCentralizerZeroCompactOpenProof
import Langlands.GroupScheme.Torus.FiniteGaloisSplittingProof
import Langlands.LocalField.FiniteExtension

/-! # Double-root-friendly centralizer filtrations for actual tori -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open Langlands.GroupScheme Langlands.LocalField
open Langlands.GroupScheme.GaloisPointComparison
open Langlands.AlgebraicGeometry.PointTopology
open scoped CategoryTheory.MonObj NNReal commutatorElement

set_option backward.isDefEq.respectTransparency false

namespace Langlands.Geometry.Building.ParahoricBuildingData

section Algebra

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {T : CommGroupScheme (Spec (CommRingCat.of F))} [IsAffineHom T.toGrp.X.hom]
  (P : ParahoricBuildingData T.toGrp)
  (L : Type u) [Field L] [Algebra F L]
  (ω : AddValuation L (WithTop ℝ))

private instance ambientAffine : IsAffine T.X.left :=
  isAffine_of_isAffineHom T.toGrp.X.hom

private theorem centralizer_map_injective :
    Function.Injective (rationalPoints.map P.centralizer.j) := by
  let : Mono P.centralizer.j.hom.hom := P.centralizer.isRepresentedBy.1
  intro x y hxy
  exact (cancel_mono P.centralizer.j.hom.hom).mp hxy

/-- Keep the actual centralizer-zero subgroup at zero, and at positive depth
impose the ambient torus's geometric-character congruences. -/
def torusCentralizerCongruence (r : ℝ≥0) :
    Subgroup (rationalPoints P.centralizer.Z) :=
  if r = 0 then P.centralizerZero else
    P.centralizerZero ⊓ (extendedCharacterCongruence F L ω T.toGrp r).comap
      (rationalPoints.map P.centralizer.j)

@[simp] theorem torusCentralizerCongruence_zero :
    P.torusCentralizerCongruence L ω 0 = P.centralizerZero := by
  simp [torusCentralizerCongruence]

theorem torusCentralizerCongruence_antitone :
    Antitone (P.torusCentralizerCongruence L ω) := by
  intro r s hrs
  by_cases hr : r = 0
  · subst r
    rw [torusCentralizerCongruence_zero]
    by_cases hs : s = 0
    · simp only [hs, torusCentralizerCongruence_zero, le_refl]
    · simp only [torusCentralizerCongruence, ite_eq_right hs]
      exact inf_le_left
  · have hs : s ≠ 0 := fun hs => hr
      (le_antisymm (hs ▸ hrs) (zero_le : (0 : ℝ≥0) ≤ r))
    simp only [torusCentralizerCongruence, ite_eq_right hr, ite_eq_right hs]
    exact inf_le_inf_left _ (Subgroup.comap_mono
      (extendedCharacterCongruence_antitone F L ω T.toGrp hrs))

theorem iInf_torusCentralizerCongruence_eq_bot
    (hL : IsSplitTorus (baseChanged F L T.toGrp)) :
    ⨅ r : ℝ≥0, P.torusCentralizerCongruence L ω r = ⊥ := by
  apply le_antisymm _ bot_le
  intro z hz
  apply Subgroup.mem_bot.mpr
  apply centralizer_map_injective P
  rw [map_one]
  have hbot : rationalPoints.map P.centralizer.j z ∈
      ⨅ r : ℝ≥0, extendedCharacterCongruence F L ω T.toGrp r := by
    simp only [Subgroup.mem_iInf] at hz ⊢
    intro r
    have hr : r + 1 ≠ 0 := ne_of_gt (by positivity)
    have hz' := hz (r + 1)
    simp only [torusCentralizerCongruence, ite_eq_right hr,
      Subgroup.mem_inf, Subgroup.mem_comap] at hz'
    exact extendedCharacterCongruence_antitone F L ω T.toGrp
      (le_add_of_nonneg_right zero_le) hz'.2
  rw [iInf_extendedCharacterCongruence_eq_bot F L ω T hL] at hbot
  exact Subgroup.mem_bot.mp hbot

/-- An actual separated centralizer filtration for the torus, with no
replacement of the supplied zero datum. -/
def torusCentralizerFiltration
    (hL : IsSplitTorus (baseChanged F L T.toGrp)) : P.CentralizerFiltration where
  filtration := P.torusCentralizerCongruence L ω
  filtration_zero := P.torusCentralizerCongruence_zero L ω
  antitone := P.torusCentralizerCongruence_antitone L ω
  separated := P.iInf_torusCentralizerCongruence_eq_bot L ω hL

private theorem roots_empty : relativeRoots P.i = ∅ := by
  have : Smooth T.toGrp.X.hom := P.isConnectedReductive.smooth
  exact ValuationBuildingData.relativeRoots_eq_empty_of_commutative
    P.i P.isMaximalSplitTorus.1

/-- The algebraic filtration axioms hold: root clauses are vacuous,
conjugation in the ambient torus is trivial, and the centralizer is commutative. -/
theorem torusCentralizerFiltration_axioms
    (hL : IsSplitTorus (baseChanged F L T.toGrp)) :
    (P.torusCentralizerFiltration L ω hL).SatisfiesFiltrationAxioms := by
  have he : IsEmpty (relativeRoots P.i) := Set.isEmpty_coe_sort.mpr (roots_empty P)
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x a
    exact he.false a |>.elim
  · intro n hn r
    have hc : (MulAut.conj n).toMonoidHom = MonoidHom.id _ := by
      ext g
      simp [MulAut.conj_apply]
    rw [hc, Subgroup.map_id]
  · intro r s
    apply Subgroup.commutator_le.mpr
    intro z hz w hw
    have hc : ⁅z, w⁆ = 1 := by
      apply centralizer_map_injective P
      rw [map_commutatorElement, map_one]
      simp [commutatorElement_def]
    rw [hc]
    exact Subgroup.one_mem _
  · intro x a
    exact he.false a |>.elim

/-- Every mixed-double-root clause is vacuous for an actual torus. -/
theorem torusCentralizerFiltration_doubleRootFriendly
    (hL : IsSplitTorus (baseChanged F L T.toGrp)) :
    (P.torusCentralizerFiltration L ω hL).IsDoubleRootCommutatorFriendly := by
  intro x a
  have he : IsEmpty (relativeRoots P.i) := Set.isEmpty_coe_sort.mpr (roots_empty P)
  exact he.false a |>.elim

end Algebra

section Topology

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {T : CommGroupScheme (Spec (CommRingCat.of F))} [IsAffineHom T.toGrp.X.hom]
  (P : ParahoricBuildingData T.toGrp)
  (L : Type u) [NormedField L] [Algebra F L] [IsUltrametricDist L]

private instance centralizerAffine : IsAffine P.centralizer.Z.X.left := by
  have : IsClosedImmersion P.centralizer.j.hom.hom.left := P.centralizer.isClosedSubgroup
  exact isAffine_of_isAffineHom P.centralizer.j.hom.hom.left

local instance ambientPointTopology : TopologicalSpace (rationalPoints T.toGrp) :=
  rationalPointTopology F T.X

local instance centralizerPointTopology : TopologicalSpace (rationalPoints P.centralizer.Z) :=
  rationalPointTopology F P.centralizer.Z.X

/-- Logarithmic congruences give an open filtration, using the published
unconditional openness of the actual centralizer-zero subgroup. -/
theorem torusCentralizerFiltration_isOpen
    (hL : IsSplitTorus (baseChanged F L T.toGrp))
    (hcont : Continuous (algebraMap F L)) (c : ℝ) (hc : 0 < c) :
    (P.torusCentralizerFiltration L
      (logAdditiveValuation (NormedField.valuation (K := L)) c hc) hL).IsOpenFiltration := by
  let := (rationalCharacterLattice L (baseChanged F L T.toGrp)
    hL.isConnectedReductive).2
  change ∀ r : ℝ≥0, IsOpen (P.torusCentralizerCongruence L
    (logAdditiveValuation (NormedField.valuation (K := L)) c hc) r :
      Set (rationalPoints P.centralizer.Z))
  intro r
  have hzero := (P.centralizerZeroCompactOpen).2
  by_cases hr : r = 0
  · simpa only [hr, torusCentralizerCongruence_zero] using hzero
  · have hmap : (rationalPoints.map P.centralizer.j :
        rationalPoints P.centralizer.Z → rationalPoints T.toGrp) =
        (fun p => p ≫ P.centralizer.j.hom.hom) := by
      funext p
      exact rationalPoints.map_apply P.centralizer.j p
    have hcong := (isOpen_extendedCharacterCongruence_log F L T.toGrp hcont c hc r).preimage
      (continuous_rationalPointMap F P.centralizer.j.hom.hom)
    simpa only [torusCentralizerCongruence, ite_eq_right hr, Subgroup.coe_inf,
      Subgroup.coe_comap, hmap] using hzero.inter hcong

end Topology

section Existence

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {T : CommGroupScheme (Spec (CommRingCat.of F))} [IsAffineHom T.toGrp.X.hom]
  (P : ParahoricBuildingData T.toGrp)

/-- The full existence conclusion holds for every actual torus and every
supplied parahoric datum, with no supplied filtration or splitting field. -/
theorem exists_doubleRootFriendly_filtration_of_torus (hT : IsTorus T.toGrp) :
    ∃ Zf : P.CentralizerFiltration, Zf.SatisfiesFiltrationAxioms ∧ Zf.IsOpenFiltration ∧
      Zf.IsDoubleRootCommutatorFriendly := by
  obtain ⟨L, hfield, halgebra, hfinite, _, hL⟩ := torusFiniteGaloisSplitting F T.toGrp hT
  let := hfield
  let := halgebra
  let := hfinite
  let := LocalGalois.localNormedField F
  let := FiniteExtension.normedField F L
  let := FiniteExtension.normedAlgebra F L
  let := FiniteExtension.ultrametric F L
  let ω := logAdditiveValuation (NormedField.valuation (K := L)) 1 (by norm_num)
  exact ⟨P.torusCentralizerFiltration L ω hL,
    P.torusCentralizerFiltration_axioms L ω hL,
    P.torusCentralizerFiltration_isOpen L hL (continuous_algebraMap F L) 1 (by norm_num),
    P.torusCentralizerFiltration_doubleRootFriendly L ω hL⟩

end Existence

end Langlands.Geometry.Building.ParahoricBuildingData
