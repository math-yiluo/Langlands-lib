import Langlands.GroupScheme.Rational.BruhatCellDimensionStatement
import Langlands.GroupScheme.Dynamic.CommonTorusIntersectionDeterminants
import Langlands.GroupScheme.Rational.CyclicRootFunctorComparisonProof
import Langlands.GroupScheme.Rational.DynamicPositiveSemigroup
import Langlands.GroupScheme.Rational.NormalizedPositiveDescent
import Langlands.GroupScheme.Rational.SemigroupIntersectionIdentityComponent
import Langlands.GroupScheme.Rational.DominantChamberMove
import Langlands.GroupScheme.Rational.RelativeTitsNondegeneracy
import Langlands.GroupScheme.Rational.SubgroupProductGeometry
import Langlands.GroupScheme.Lie.SubgroupCellDimension
import Langlands.LinearAlgebra.SubmoduleFinrank

/-! # The weighted dimension of the actual Bruhat intersection -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj BigOperators

namespace Langlands.GroupScheme

open Langlands.GroupScheme.Dynamic RelativeRoot

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 800000 in
/-- The adjoint weight span of the characters positive on both `ν` and `ξ`
has finrank the sum of the weight-space finranks over the relative roots
positive on both cocharacters. -/
private theorem finrank_common_positive_weights
    {k : Type u} [Field k] {G : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
    {T : CommGroupScheme (Spec (CommRingCat.of k))} (hT : IsSplitTorus T.toGrp)
    (i : T.toGrp ⟶ G) (ν ξ : cocharacterLattice T) :
    Module.finrank k (adjointSemigroupWeightSpan i (positiveSemigroup ν ⊓ positiveSemigroup ξ)) =
      ∑ᶠ α ∈ {α : characterLattice T | α ∈ relativeRoots i ∧
        0 < latticePairing T α ν ∧ 0 < latticePairing T α ξ},
        Module.finrank k (weightSpace i α) := by
  classical
  let roots := {α : characterLattice T | α ∈ relativeRoots i ∧
    0 < latticePairing T α ν ∧ 0 < latticePairing T α ξ}
  have hFinite : roots.Finite := (hT.finite_relativeRoots i).subset fun _ h => h.1
  have hSpan : adjointSemigroupWeightSpan i (positiveSemigroup ν ⊓ positiveSemigroup ξ) =
      ⨆ α ∈ hFinite.toFinset, weightSpace i α := by
    unfold adjointSemigroupWeightSpan
    apply le_antisymm
    · refine iSup_le fun α => ?_
      have hSign : 0 < latticePairing T α.val ν ∧ 0 < latticePairing T α.val ξ :=
        α.property
      by_cases hWeight : weightSpace i α.val = ⊥
      · rw [hWeight]
        exact bot_le
      · have hNonzero : α.val ≠ 0 := by
          intro h
          simpa [h] using hSign.1
        have hα : α.val ∈ hFinite.toFinset := hFinite.mem_toFinset.mpr
          ⟨⟨hNonzero, hWeight⟩, hSign⟩
        exact le_iSup₂_of_le α.val hα le_rfl
    · refine iSup₂_le fun α hα => ?_
      exact le_iSup (fun β : ↥(positiveSemigroup ν ⊓ positiveSemigroup ξ) => weightSpace i β.val)
        ⟨α, (hFinite.mem_toFinset.mp hα).2⟩
  have := Lie.finiteDimensional_lieKernel G
  change _ = ∑ᶠ α ∈ roots, Module.finrank k (weightSpace i α)
  rw [hSpan, finsum_mem_eq_finite_toFinset_sum _ hFinite]
  exact Langlands.Plancherel.finrank_biSup_eq_sum
    (isInternal_weightSpace_of_isSplitTorus k G T hT i).submodule_iSupIndep hFinite.toFinset

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 800000 in
/-- The unipotent factor `U(ν) ∩ n U(-ν) n⁻¹` of a rational Bruhat cell is
smooth of relative dimension the sum of the adjoint weight-space dimensions of
the positive relative roots that the inverse Weyl element makes negative. Its
Lie module has exactly the common positive weights of `ν` and of the
conjugated inverse cocharacter. -/
theorem rationalBruhatCellDimension : RationalBruhatCellDimensionStatement.{u} := by
  intro k _ G hG T i hi ν
  let : IsAffineHom G.X.hom := hG.isAffineHom
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  let : Smooth G.X.hom := hG.smooth
  let : Mono i.hom.hom.left := hi.isSplitSubtorus.mono
  dsimp only
  intro _ n
  let χ := CommGroupScheme.groupHom ν ≫ i
  let χminus := CommGroupScheme.groupHom (Gm.powerHom (Spec (CommRingCat.of k)) (-1)) ≫ χ
  let ξ := cocharacterAut (normalizingAut i n) (-ν)
  let ψ := CommGroupScheme.groupHom ξ ≫ i
  let e := G.innerIso n.val
  have hξ : ψ = χminus ≫ e.hom := by
    change CommGroupScheme.groupHom (cocharacterAut (normalizingAut i n) (-ν)) ≫ i = _
    rw [groupHom_cocharacterAut_comp, groupHom_neg_comp_eq_oppositeCocharacter]
    rfl
  let u := Affine.unipotentHom χ
  let v := Affine.unipotentHom χminus
  let w := v ≫ e.hom
  let C := subgroupIntersection w u
  let j := subgroupIntersectionHom w u
  have hwc : IsClosedSubgroup w := (Affine.isClosedSubgroup_unipotentHom χminus).comp_iso e
  have huc := Affine.isClosedSubgroup_unipotentHom χ
  have hc : IsClosedSubgroup j := isClosedSubgroup_subgroupIntersectionHom hwc huc
  let : IsAffineHom C.X.hom := hc.isAffineHom
  have hw : (unipotent ψ).IsRepresentedBy w := by
    rw [hξ, unipotent_eq_comap_of_iso (χminus ≫ e.hom) e.symm, Iso.symm_hom, comp_hom_comp_inv]
    exact (Affine.isRepresentedBy_unipotentHom χminus).comp_iso e
  have hu := Affine.isRepresentedBy_unipotentHom χ
  have hj : (unipotent ψ ⊓ unipotent χ).IsRepresentedBy j := by
    rw [← hw.2, ← hu.2]
    exact isRepresentedBy_subgroupIntersectionHom hwc huc
  have hT := hi.isSplitSubtorus.1
  let b := AutomorphicAction.conjugation i
  have hPos := dynamicUnipotentSemigroupComparison_of_semigroupRealization
    semigroupRealization G T hT i ν
  have hOpp := dynamicUnipotentSemigroupComparison_of_semigroupRealization
    semigroupRealization G T hT i ξ
  let : Smooth (Affine.unipotentScheme χminus).X.hom :=
    (dynamicSmooth k G χminus _ v).2.2 (Affine.isRepresentedBy_unipotentHom χminus)
  let : Smooth C.X.hom :=
    smooth_subgroupIntersection_semigroup b hT (positiveSemigroup ξ) (positiveSemigroup ν) w u
      (hOpp ▸ hw) (hPos ▸ hu) hwc huc
  let a := (unipotentIntersectionTorusAction i ξ ν hj).restrict (CommGroupScheme.groupHom ν)
  have heq : a.IsEquivariant (AutomorphicAction.cocharacterAction χ) j := by
    rw [AutomorphicAction.cocharacterAction_eq_conjugation]
    change a.IsEquivariant (AutomorphicAction.conjugation (CommGroupScheme.groupHom ν ≫ i)) j
    rw [← AutomorphicAction.restrict_conjugation i (CommGroupScheme.groupHom ν)]
    exact AutomorphicAction.IsEquivariant.restrict
      (unipotentIntersectionTorusAction_isEquivariant i ξ ν hj) (CommGroupScheme.groupHom ν)
  have hContract : a.unipotent = ⊤ := by
    rw [heq.unipotent_eq_comap_of_isClosedSubgroup hc, AutomorphicAction.cocharacterAction_unipotent]
    apply SubgroupFunctor.ext
    intro X
    apply Subgroup.ext
    intro x
    change x ≫ j.hom.hom ∈ (unipotent χ).carrier X ↔ True
    exact iff_true_intro (hj.pointsEquiv X x).property.2
  let : ConnectedSpace C.X.left :=
    AutomorphicAction.Affine.connectedSpace_of_isRepresentedBy_unipotent a
      (hContract.symm ▸ SubgroupFunctor.top_isRepresentedBy_id C)
  have hWeights : tangentSubmodule (unipotent ψ ⊓ unipotent χ) =
      adjointSemigroupWeightSpan i (positiveSemigroup ν ⊓ positiveSemigroup ξ) := by
    rw [inf_comm, hPos, hOpp, ← semigroupWeightSpan_conjugation]
    exact (hasLieImage_iff_tangentSubmodule_eq _ _).mp
      (hasLieImage_semigroupSubgroup_inf (AutomorphicAction.conjugation i) hT _ _)
  have hDim : Lie.dimension C =
      ∑ᶠ α ∈ {α : characterLattice T | α ∈ relativeRoots i ∧
        0 < latticePairing T α ν ∧ 0 < latticePairing T α ξ},
        Module.finrank k (weightSpace i α) := by
    rw [Lie.dimension, ← finrank_tangentSubmodule_eq_of_isRepresentedBy _ j hj, hWeights]
    exact finrank_common_positive_weights hT i ν ξ
  have hPair (α : characterLattice T) :
      0 < latticePairing T α ξ ↔ latticePairing T (weylAction i n⁻¹ α) ν < 0 := by
    change 0 < latticePairing T α (cocharacterAut (normalizingAut i n) (-ν)) ↔ _
    rw [latticePairing_cocharacterAut_normalizingAut,
      map_neg (latticePairing T (weylAction i n⁻¹ α)) ν, neg_pos]
  simp only [hPair] at hDim
  rw [← hDim]
  exact SubgroupProductOrbit.smoothOfRelativeDimension_lie_dimension C

end Langlands.GroupScheme
