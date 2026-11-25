import Langlands.GroupScheme.Reductive.AdjointExteriorRootWeights
import Langlands.GroupScheme.Reductive.AdjointWeightBasis
import Langlands.GroupScheme.Reductive.ExteriorWeightBasis
import Langlands.GroupScheme.Reductive.StarAction

/-! # Ground-field exterior representations with a maximal simple weight -/

set_option backward.isDefEq.respectTransparency false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

variable {k K : Type u} [Field k] [Field K] [Algebra k K]
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]

local notation "G_K" => Functor.obj (GroupScheme.baseChange (algebraBaseMap k K)) G

private local instance : IsAffineHom (G_K).X.hom := by
  change IsAffineHom (Limits.pullback.snd G.X.hom (algebraBaseMap k K))
  infer_instance

namespace SplitPinning

/-- An actual ground-field representation with a specified maximal weight of multiplicity
one for the split pinning after scalar extension. -/
structure GroundMaximalWeightRepresentation (p : SplitPinning (k := K) G_K)
    (ν : characterLattice p.torus) where
  m : ℕ
  representation : MatrixRepresentation G (Fin (m + 1))
  multiplicity_one : Module.finrank K
    (p.representationWeightSpace (representation.baseChange (algebraBaseMap k K)) ν) = 1
  maximal : ∀ μ, p.representationWeightSpace
    (representation.baseChange (algebraBaseMap k K)) μ ≠ ⊥ →
      μ - ν ∈ p.positiveRootMonoid → μ = ν

variable [LocallyOfFiniteType G.X.hom]

set_option maxHeartbeats 1600000 in
/-- The adjoint exterior representation omitting the selected simple roots. -/
def groundAdjointExterior (p : SplitPinning (k := K) G_K) [Fintype p.rootIndex]
    (O : Finset p.base.support) :
    GroundMaximalWeightRepresentation p
      (IntegralWeylVector.positiveRootSum p.rootDatum p.base - ∑ a ∈ O, p.rootDatum.root a) := by
  classical
  let n := Module.finrank k (Additive (lieKernel G k))
  let c : Lie.FiniteCoordinates G n := Lie.finiteCoordinates G
  let ρ := Lie.adjointRepresentation c
  let basisExists := p.exists_adjointBaseChangeWeightBasis c
  let b := basisExists.choose
  let weightsExist := basisExists.choose_spec
  let w := weightsExist.choose
  let embeddingExists := weightsExist.choose_spec
  let r := embeddingExists.choose
  have hb := embeddingExists.choose_spec.1
  have hr := embeddingExists.choose_spec.2.1
  have hzero := embeddingExists.choose_spec.2.2
  let j := (Finset.univ.filter p.base.IsPos).card - O.card
  let S := p.positiveRootComplementIndices r O
  have hS : S.card = j := p.positiveRootComplementIndices_card r O
  let I := Set.powersetCard (Fin n) j
  let s₀ : I := ⟨S, hS⟩
  letI : Nonempty I := ⟨s₀⟩
  let m := Fintype.card I - 1
  have hm : Fintype.card I = m + 1 := by
    have hpos : 0 < Fintype.card I := Fintype.card_pos
    dsimp [m]
    omega
  let e := Fintype.equivFinOfCardEq hm
  let τ := (Chevalley.exteriorRepresentation n j (CommRingCat.of k) ρ).reindex e
  let τK := τ.baseChange (algebraBaseMap k K)
  let B := MatrixRepresentation.reindexedExteriorBasis b e
  let W (i : Fin (m + 1)) := ∑ a ∈ (e.symm i).val, w a
  have hB (i : Fin (m + 1)) : B i ∈ p.representationWeightSpace τK (W i) :=
    p.reindexedExteriorBasis_mem_representationWeightSpace ρ b w hb e i
  let ν := IntegralWeylVector.positiveRootSum p.rootDatum p.base -
    ∑ a ∈ O, p.rootDatum.root a
  have hsum : ∑ a ∈ S, w a = ν := p.sum_positiveRootComplementIndices r O w hr
  have hν : W (e s₀) = ν := by
    change ∑ a ∈ (e.symm (e s₀)).val, w a = ν
    rw [e.symm_apply_apply]
    exact hsum
  have hindex (i : Fin (m + 1)) (hi : W i - ν ∈ p.positiveRootMonoid) : i = e s₀ := by
    apply e.symm.injective
    rw [e.symm_apply_apply]
    apply Subtype.ext
    by_contra hne
    apply p.sub_sum_not_mem_positiveRootMonoid r O w hr hzero (e.symm i).val
      ((e.symm i).property.trans hS.symm) hne
    rw [hsum]
    exact hi
  refine ⟨m, τ, ?_, ?_⟩
  · change Module.finrank K (p.representationWeightSpace τK ν) = 1
    rw [p.finrank_representationWeightSpace_eq_card τK B W hB ν]
    apply Fintype.card_eq_one_iff.mpr
    refine ⟨⟨e s₀, hν⟩, fun i => Subtype.ext (hindex i.val ?_)⟩
    rw [i.property, sub_self]
    exact p.positiveRootMonoid.zero_mem
  · intro μ hμ hdiff
    change p.representationWeightSpace τK μ ≠ ⊥ at hμ
    have hnz : Module.finrank K (p.representationWeightSpace τK μ) ≠ 0 :=
      fun h => hμ (Submodule.finrank_eq_zero.mp h)
    rw [p.finrank_representationWeightSpace_eq_card τK B W hB μ] at hnz
    obtain ⟨i⟩ := Fintype.card_pos_iff.mp (Nat.pos_of_ne_zero hnz)
    have hi : W i.val - ν ∈ p.positiveRootMonoid := by
      rw [i.property]
      exact hdiff
    exact i.property.symm.trans ((congrArg W (hindex i.val hi)).trans hν)

end SplitPinning

namespace GaloisPinningData

variable [LocallyOfFiniteType G.X.hom]
  (d : GaloisPinningData k K G) [Fintype d.toSplitPinning.rootIndex]

/-- Each positive-root sum with a finite set of simple roots removed is a maximal
multiplicity-one weight of a representation defined over the ground field. -/
theorem exists_groundRepresentation_positiveRootSum_sub_simpleRoots
    (O : Finset d.toSplitPinning.base.support) :
    ∃ (m : ℕ) (ρ : MatrixRepresentation G (Fin (m + 1))),
      let ν := IntegralWeylVector.positiveRootSum
        d.toSplitPinning.rootDatum d.toSplitPinning.base - ∑ a ∈ O, d.toSplitPinning.rootDatum.root a
      let ρK := ρ.baseChange (algebraBaseMap k K)
      Module.finrank K (d.toSplitPinning.representationWeightSpace ρK ν) = 1 ∧
        ∀ μ, d.toSplitPinning.representationWeightSpace ρK μ ≠ ⊥ →
          μ - ν ∈ d.toSplitPinning.positiveRootMonoid → μ = ν := by
  let E := d.toSplitPinning.groundAdjointExterior O
  exact ⟨E.m, E.representation, E.multiplicity_one, E.maximal⟩

end GaloisPinningData

end Langlands.GroupScheme
