import Langlands.GroupScheme.Quaternionic.IsometryTorusWeights
import Langlands.GroupScheme.Quaternionic.HyperbolicTorus
import Langlands.GroupScheme.Rational.SingleWeightRepresentation

/-! # Split rank at quaternionic quadratic Witt index one -/

noncomputable section
universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped Matrix CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme.Quaternionic.FirstKindInvolution

variable {K D : Type u} [Field K] [Infinite K] [DivisionRing D] [Algebra K D]
  [FiniteDimensional K D] (σ : FirstKindInvolution K D)
  {n : Type} [Fintype n] [DecidableEq n]

/-- Any mono split-torus map into the actual isometry group has at most one factor at Witt index one. -/
theorem card_le_one_of_mono_isometryTorus (q : σ.QuadraticForms n)
    (hq : σ.quadraticWittIndex q = 1)
    (I : Type u) [Fintype I] [DecidableEq I]
    (i : splitTorus (Spec (CommRingCat.of K)) I ⟶ σ.isometryGroup q)
    [Mono i.hom.hom] : Nat.card I ≤ 1 := by
  let ρ := i ≫ σ.isometryRegularRepresentation q
  have : IsClosedImmersion (σ.isometryGroupι q).hom.hom.left :=
    σ.isClosedSubgroup_isometryGroupι q
  have : Mono (σ.isometryGroupι q).hom.hom.left :=
    SurjectiveOnStalks.mono_of_injective
      (IsClosedImmersion.isClosedEmbedding (σ.isometryGroupι q).hom.hom.left).injective
  have : Mono (σ.isometryGroupι q).hom.hom :=
    Over.mono_of_mono_left ((σ.isometryGroupι q).hom.hom)
  have : Mono ρ.hom.hom := by
    change Mono (i.hom.hom ≫ (σ.isometryGroupι q).hom.hom ≫
      (FiniteAlgebraUnits.rightRegularHom (Module.finBasis K (Matrix n n D))).hom.hom)
    infer_instance
  obtain ⟨B, w, hw⟩ := GeneralLinear.CocharacterDiagonal.exists_diagonalizingMatrix I ρ
  have hweight (j : Fin (Module.finrank K (Matrix n n D))) :
      scalarWeightSpace (σ.torusRowAction I q i) (splitTorus.rationalMonomial I (w j)) ≠ ⊥ := by
    apply σ.scalarWeightSpace_ne_bot_of_regular_eigenvector I q i (w j)
      ((B : Matrix _ _ K).col j) (GeneralLinear.CocharacterDiagonal.column_ne_zero B j)
    intro t
    apply GeneralLinear.CocharacterDiagonal.column_weight_of_diagonalization I ρ B w ?_ j t
    intro s
    simpa only [Algebra.algebraMap_self, Matrix.GeneralLinearGroup.map_id, MonoidHom.id_apply] using hw K s
  obtain ⟨m, hm⟩ := σ.exists_weight_trichotomy I q hq (σ.torusRowAction I q i)
    (fun t z => σ.quadraticValue_isometryRowAction q _ z) w hweight
  exact GeneralLinear.CocharacterDiagonal.card_le_one_of_weight_trichotomy I ρ B w m hm hw

/-- The full isometry group has split rank at most one at quadratic Witt index one. -/
theorem splitRank_isometryGroup_le_one (q : σ.QuadraticForms n)
    (hq : σ.quadraticWittIndex q = 1) : splitRank (σ.isometryGroup q) ≤ 1 := by
  refine iSup_le fun I => iSup_le fun _ => iSup_le fun i => iSup_le fun hi => ?_
  let := Fintype.ofFinite I
  let := Classical.decEq I
  have : IsClosedImmersion i.hom.hom.left := hi
  have : Mono i.hom.hom := Over.mono_of_mono_left _
  exact_mod_cast σ.card_le_one_of_mono_isometryTorus q hq I i

/-- The connected isometry group has split rank at most one at quadratic Witt index one. -/
theorem splitRank_connectedIsometryGroup_le_one (q : σ.QuadraticForms n)
    [Smooth (σ.isometryGroup q).X.hom] (hq : σ.quadraticWittIndex q = 1) :
    splitRank (σ.connectedIsometryGroup q) ≤ 1 := by
  exact (splitRank_le_of_isClosedSubgroup (identityComponentι (σ.isometryGroup q))
    (IdentityComponent.isClosedSubgroup_identityComponentι (σ.isometryGroup q))).trans
      (σ.splitRank_isometryGroup_le_one q hq)

/-- A smooth isometry group of a nondegenerate form of Witt index one has connected split rank one. -/
theorem splitRank_connectedIsometryGroup_eq_one (q : σ.QuadraticForms n)
    [Smooth (σ.isometryGroup q).X.hom] (hq : σ.IsNondegenerateQuadratic q)
    (hi : σ.quadraticWittIndex q = 1) : splitRank (σ.connectedIsometryGroup q) = 1 := by
  apply le_antisymm (σ.splitRank_connectedIsometryGroup_le_one q hi)
  apply σ.one_le_splitRank_connectedIsometryGroup_of_quadraticWittIndex_pos q hq
  omega

/-- The full smooth isometry group has the same rank-one conclusion. -/
theorem splitRank_isometryGroup_eq_one (q : σ.QuadraticForms n)
    [Smooth (σ.isometryGroup q).X.hom] (hq : σ.IsNondegenerateQuadratic q)
    (hi : σ.quadraticWittIndex q = 1) : splitRank (σ.isometryGroup q) = 1 := by
  apply le_antisymm (σ.splitRank_isometryGroup_le_one q hi)
  rw [← σ.splitRank_connectedIsometryGroup_eq_one q hq hi]
  exact splitRank_le_of_isClosedSubgroup (identityComponentι (σ.isometryGroup q))
    (IdentityComponent.isClosedSubgroup_identityComponentι (σ.isometryGroup q))

end Langlands.GroupScheme.Quaternionic.FirstKindInvolution

namespace Langlands.GroupScheme.Quaternionic

/-- The rank conclusion for any smooth isometry group of a nondegenerate form of Witt index one. -/
def WittIndexOneSplitRankStatement : Prop :=
  ∀ (K D : Type u) [Field K] [Infinite K] [DivisionRing D] [Algebra K D]
    [FiniteDimensional K D] (σ : FirstKindInvolution K D)
    (n : Type) [Fintype n] [DecidableEq n] (q : σ.QuadraticForms n)
    [Smooth (σ.isometryGroup q).X.hom],
    σ.IsNondegenerateQuadratic q → σ.quadraticWittIndex q = 1 →
      splitRank (σ.connectedIsometryGroup q) = 1 ∧ splitRank (σ.isometryGroup q) = 1

/-- The preceding upper obstruction and hyperbolic lower bound prove the rank statement. -/
theorem wittIndexOneSplitRankStatement : WittIndexOneSplitRankStatement.{u} := by
  intro K D _ _ _ _ _ σ n _ _ q _ hq hi
  exact ⟨σ.splitRank_connectedIsometryGroup_eq_one q hq hi,
    σ.splitRank_isometryGroup_eq_one q hq hi⟩

end Langlands.GroupScheme.Quaternionic
