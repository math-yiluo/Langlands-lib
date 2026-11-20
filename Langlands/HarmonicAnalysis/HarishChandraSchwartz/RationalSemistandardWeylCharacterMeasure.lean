import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalSemistandardOrbitConjugation
import Mathlib.MeasureTheory.Measure.Haar.Unique

/-! # Conjugation of the source character Haar measure -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj ENNReal
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology
open Langlands.Aubert.General Langlands.Plancherel

namespace Langlands.HarishChandraSchwartz.RationalSemistandard.SourceMeasure

attribute [local instance] rationalWeightsIsAffine rationalWeightsTopology
  rationalWeightsTopologicalGroup rationalWeightsT2Field rationalWeightsLocallyCompact
  rationalWeightsMeasurableSpace rationalWeightsBorelSpace rationalInducedSecondCountable
  rationalInducedT2 rationalInducedNonarchimedean modelAffineHom modelAffine modelTopology

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {S : CommGroupScheme (Spec (CommRingCat.of F))}
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom] {i : S.toGrp ⟶ G}
  {p q : SemistandardSpectralIndex i} {g : rationalPoints G}
  (hc : Association.ConjugatesLevi g p q) (m : LeviModel p) (n : LeviModel q)
  {A B : CommGroupScheme (Spec (CommRingCat.of F))} [IsAffine A.X.left] [IsAffine B.X.left]
  (a : A.toGrp ⟶ m.scheme) (ha : IsSplitComponent a)
  (b : B.toGrp ⟶ n.scheme) (hb : IsSplitComponent b)

omit [LocallyOfFiniteType G.X.hom] in
private theorem mem_restrictionKernel_map (χ : unitaryUnramifiedCharacters m.normCharacters) :
    χ ∈ (rationalUnitaryUnramifiedCharacterRestrict a).toMonoidHom.ker.map
      (unitaryCharacterHomeomorph m).toMonoidHom ↔
      ∀ x ∈ m.splitCenter a, χ.val x = 1 := by
  let e := unitaryCharacterHomeomorph m
  obtain ⟨ψ, rfl⟩ := e.surjective χ
  refine (Subgroup.mem_map_iff_mem (f := e.toMulEquiv.toMonoidHom) (x := ψ)
    e.injective).trans ?_
  rw [mem_rationalUnitaryUnramifiedCharacterRestrict_ker]
  constructor
  · rintro h _ ⟨_, ⟨x, rfl⟩, rfl⟩
    change ψ.val (m.pointHomeomorph.symm (m.pointHomeomorph (rationalPoints.map a x))) = 1
    rw [m.pointHomeomorph.symm_apply_apply]
    exact h x
  · intro h x
    have hx := h (m.pointHomeomorph (rationalPoints.map a x)) ⟨_, ⟨x, rfl⟩, rfl⟩
    change ψ.val (m.pointHomeomorph.symm (m.pointHomeomorph (rationalPoints.map a x))) = 1 at hx
    rwa [m.pointHomeomorph.symm_apply_apply] at hx

include hc ha hb in
/-- Actual Levi conjugation identifies the kernels of split-component restriction. -/
def restrictionKernelConjugation :
    (rationalUnitaryUnramifiedCharacterRestrict a).toMonoidHom.ker ≃*
      (rationalUnitaryUnramifiedCharacterRestrict b).toMonoidHom.ker := by
  let e := Association.unitaryCharacterConjugation hc m n
  let eL := Association.leviPointConjugation hc
  let K := (rationalUnitaryUnramifiedCharacterRestrict a).toMonoidHom.ker
  let J := (rationalUnitaryUnramifiedCharacterRestrict b).toMonoidHom.ker
  let Ka := K.map (unitaryCharacterHomeomorph m).toMonoidHom
  let Jb := J.map (unitaryCharacterHomeomorph n).toMonoidHom
  have he : Ka.map e.toMonoidHom = Jb := by
    ext χ
    obtain ⟨ψ, rfl⟩ := e.surjective χ
    refine (Subgroup.mem_map_iff_mem (f := e.toMulEquiv.toMonoidHom) (K := Ka) (x := ψ)
      e.injective).trans ?_
    rw [mem_restrictionKernel_map m a, mem_restrictionKernel_map n b]
    change (∀ x ∈ m.splitCenter a, ψ.val x = 1) ↔
      ∀ y ∈ n.splitCenter b, (e ψ).val y = 1
    rw [← Association.splitCenter_map_leviPointConjugation hc m n a ha b hb]
    constructor
    · rintro h _ ⟨x, hx, rfl⟩
      change ψ.val (eL.symm (eL x)) = 1
      rw [eL.symm_apply_apply]
      exact h x hx
    · intro h x hx
      have hy := h (eL x) ⟨x, hx, rfl⟩
      change ψ.val (eL.symm (eL x)) = 1 at hy
      rwa [eL.symm_apply_apply] at hy
  let ea := K.equivMapOfInjective (unitaryCharacterHomeomorph m).toMonoidHom
    (unitaryCharacterHomeomorph m).injective
  let eb := J.equivMapOfInjective (unitaryCharacterHomeomorph n).toMonoidHom
    (unitaryCharacterHomeomorph n).injective
  let ei := Ka.equivMapOfInjective e.toMonoidHom e.injective
  exact ea.trans (ei.trans ((MulEquiv.subgroupCongr he).trans eb.symm))

include hc ha hb in
/-- Literal split-center conjugation preserves the cardinality of the actual
unitary restriction kernel, hence the absolute I.1 character mass. -/
theorem restrictionKernel_card_conjugate :
    Nat.card (rationalUnitaryUnramifiedCharacterRestrict a).toMonoidHom.ker =
      Nat.card (rationalUnitaryUnramifiedCharacterRestrict b).toMonoidHom.ker :=
  Nat.card_congr (restrictionKernelConjugation hc m n a ha b hb).toEquiv

/-- The source-scaled character measures correspond under actual Levi
conjugation. The scale is the full restriction-kernel cardinality. -/
theorem unitaryCharacterHaar_map_conjugation
    (hindex : (RenardCartan.splitValuationImage a).FiniteIndex)
    (hindex' : (RenardCartan.splitValuationImage b).FiniteIndex) :
    Measure.map (Association.unitaryCharacterConjugation hc m n)
      (unitaryCharacterHaar m a ha hindex) = unitaryCharacterHaar n b hb hindex' := by
  let e := Association.unitaryCharacterConjugation hc m n
  let : CompactSpace (unitaryUnramifiedCharacters n.normCharacters) :=
    n.unitaryCoordinates.symm.toHomeomorph.compactSpace
  have hmass : unitaryCharacterHaar m a ha hindex Set.univ =
      unitaryCharacterHaar n b hb hindex' Set.univ := by
    rw [unitaryCharacterHaar_univ, unitaryCharacterHaar_univ,
      restrictionKernel_card_conjugate hc m n a ha b hb]
  exact (MonoidHom.measurePreserving (f := e.toMonoidHom) e.continuous e.surjective hmass).map_eq

end Langlands.HarishChandraSchwartz.RationalSemistandard.SourceMeasure
