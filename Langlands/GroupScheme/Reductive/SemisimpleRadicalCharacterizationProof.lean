import Langlands.GroupScheme.Reductive.SemisimpleRadicalCharacterizationStatement
import Langlands.GroupScheme.Reductive.CentralTorusSemisimpleQuotientReduction
import Langlands.GroupScheme.Rational.ReductiveGeometricSolvableRadicalExistsProof
import Langlands.GroupScheme.Rational.AlgClosedNormalSolvableTorusProof
import Langlands.GroupScheme.CentralIsogeny.AlmostSimpleTransfer
import Langlands.GroupScheme.Reductive.FiniteCenterBaseChange

/-! # Semisimplicity characterized by the solvable radical -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]

/-- Unipotent subgroups are solvable, so triviality of the solvable radical
implies triviality of the unipotent radical for affine field groups. -/
theorem HasTrivialSolvableRadical.hasTrivialUnipotentRadical
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
    (hG : HasTrivialSolvableRadical G) : HasTrivialUnipotentRadical G := by
  intro H j hj hs hc hu hn
  have : IsAffineHom H.X.hom := hj.isAffineHom
  have : Smooth H.X.hom := hs
  exact hG H j hj hs hc
    (isSolvableGroupScheme_of_isSolvable_points (isSolvable_points_of_isUnipotent hu _)) hn

/-- The geometric solvable radical of a semisimple group is central, and its
map into the finite scheme-theoretic centre is trivial. Hence every smooth
connected solvable normal closed subgroup is trivial. -/
theorem IsSemisimple.hasTrivialSolvableRadical
    {G : GroupScheme (Spec (CommRingCat.of k))} (hG : IsSemisimple G) :
    HasTrivialSolvableRadical G := by
  have : IsAffineHom G.X.hom := hG.isConnectedReductive.isAffineHom
  obtain ⟨R, r, hr⟩ :=
    reductiveGeometricSolvableRadicalExists k G hG.isConnectedReductive
  have : IsAffineHom R.X.hom := hr.1.isClosedSubgroup.isAffineHom
  have : Smooth R.X.hom := hr.1.smooth
  have : ConnectedSpace R.X.left := hr.1.connectedSpace
  have hcentral : IsCentral r :=
    (hr.isTorus_and_isCentral_of_structural
      algClosedReductiveNormalSolvableTorus hG.isConnectedReductive).2
  have hzero : SubgroupFunctor.range r = ⊥ :=
    (SubgroupFunctor.range_eq_bot_iff_hom_eq_one r).mpr
      (hcentral.eq_one_of_hasFiniteCenter hG.hasFiniteCenter)
  intro H j hj hs hc hsol hn
  have hle := hr.1.greatest H j hj hs hc hsol hn
  rw [hzero] at hle
  apply SubgroupFunctor.ext
  intro T
  exact le_bot_iff.mp (hle T)

set_option maxHeartbeats 1200000 in
/-- **Semisimplicity through the solvable radical** (Milne 6.44 and 19.10),
for all fields and all universes, using the full scheme-theoretic centre. -/
theorem semisimpleRadicalCharacterization :
    SemisimpleRadicalCharacterizationStatement.{u} := by
  intro k _ G hs ha hc
  have : Smooth G.X.hom := hs
  have : IsAffineHom G.X.hom := ha
  let b := toAlgebraicClosure k
  let Gbar := (GroupScheme.baseChange b).obj G
  have : Smooth Gbar.X.hom := by
    change Smooth (pullback.snd G.X.hom b)
    infer_instance
  have : IsAffineHom Gbar.X.hom := by
    change IsAffineHom (pullback.snd G.X.hom b)
    infer_instance
  have hgeometric : IsSemisimple G ↔ HasTrivialSolvableRadical Gbar := by
    constructor
    · intro hG
      have hGbar : IsSemisimple Gbar :=
        ⟨hG.isConnectedReductive.baseChange_toAlgebraicClosure,
          hG.hasFiniteCenter.baseChange b⟩
      exact hGbar.hasTrivialSolvableRadical
    · intro hbar
      exact ⟨⟨hs, ha, hc, hbar.hasTrivialUnipotentRadical⟩,
        hbar.hasFiniteCenter.of_fieldExtension (K := AlgebraicClosure k) inferInstance⟩
  refine ⟨hgeometric, fun hG => ⟨fun h => h.hasTrivialSolvableRadical, ?_⟩⟩
  intro hrad
  apply hgeometric.mpr
  obtain ⟨R, r, hr⟩ := reductiveGeometricSolvableRadicalExists k G hG
  have hzero : SubgroupFunctor.range r = ⊥ :=
    hrad R r hr.1.isClosedSubgroup hr.1.smooth hr.1.connectedSpace
      hr.1.isSolvableGroupScheme hr.1.isNormal
  have hzeroBar : SubgroupFunctor.range ((GroupScheme.baseChange b).map r) = ⊥ := by
    rw [SubgroupFunctor.range_baseChangeHom, hzero, SubgroupFunctor.bot_baseChange]
  intro H j hj hsm hconn hsol hn
  have hle := hr.2.greatest H j hj hsm hconn hsol hn
  rw [hzeroBar] at hle
  apply SubgroupFunctor.ext
  intro T
  exact le_bot_iff.mp (hle T)

end Langlands.GroupScheme
