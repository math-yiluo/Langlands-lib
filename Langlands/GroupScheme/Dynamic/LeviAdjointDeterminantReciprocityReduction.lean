import Langlands.GroupScheme.Dynamic.LeviAdjointDeterminantReciprocityStatement
import Langlands.GroupScheme.Dynamic.AdjointDeterminantTorusRestrictionProof
import Langlands.GroupScheme.Dynamic.WeightExclusion
import Langlands.GroupScheme.Dynamic.RepresentedStructure
import Langlands.GroupScheme.Dynamic.ParabolicLieCriterion
import Langlands.GroupScheme.Dynamic.CentralizerReductiveStatement
import Langlands.GroupScheme.Rational.ActionWeightFunctoriality
import Langlands.GroupScheme.Rational.ActionWeightComparisonProof
import Langlands.GroupScheme.Rational.RootReflectionExistenceStatement
import Langlands.GroupScheme.Rational.CentralSplitTorusCharacterStatement
import Langlands.GroupScheme.Rational.MaximalSplitTorusSubgroup
import Langlands.GroupScheme.Rational.SplitTorusFactorization

/-! # Opposite adjoint determinants on a dynamic Levi, from structural inputs -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false

namespace Langlands.GroupScheme

/-! ### Symmetry of root multiplicities -/

section Multiplicity

variable {k : Type u} [Field k] {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  {i : T.toGrp ⟶ G} [Mono i.hom.hom.left]

/-- A rational point normalizing `i` preserves the dimensions of the adjoint weight spaces. -/
theorem finrank_weightSpace_weylAction (n : normalizerPoints i) (χ : characterLattice T) :
    Module.finrank k (weightSpace i (weylAction i n χ)) =
      Module.finrank k (weightSpace i χ) := by
  have hinj : Function.Injective
      (basePointAdjoint (n : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X)) := by
    intro X Y hXY
    have h := congrArg
      (basePointAdjoint (n : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X)⁻¹) hXY
    rwa [← Module.End.mul_apply, ← Module.End.mul_apply, basePointAdjoint_inv_mul,
      Module.End.one_apply, Module.End.one_apply] at h
  rw [← map_weightSpace_weylAction n χ]
  exact (Submodule.equivMapOfInjective _ hinj (weightSpace i χ)).finrank_eq.symm

/-- Given integral reflection data, the weight spaces of `χ` and `-χ` have the same
dimension. -/
theorem RelativeRootReflectionData.finrank_weightSpace_neg (D : RelativeRootReflectionData i)
    (χ : characterLattice T) :
    Module.finrank k (weightSpace i (-χ)) = Module.finrank k (weightSpace i χ) := by
  have hroot : ∀ α : characterLattice T, α ∈ relativeRoots i →
      Module.finrank k (weightSpace i (-α)) = Module.finrank k (weightSpace i α) := by
    intro α hα
    have h : weylAction i (D.representative ⟨α, hα⟩) α = -α := by
      rw [D.action, show latticePairing T α (D.coroot ⟨α, hα⟩) = 2 from D.pair_self ⟨α, hα⟩]
      change α - (2 : ℤ) • α = -α
      abel
    rw [← h]
    exact finrank_weightSpace_weylAction _ α
  by_cases hχ : χ ∈ relativeRoots i
  · exact hroot χ hχ
  by_cases hχ' : -χ ∈ relativeRoots i
  · have h := hroot (-χ) hχ'
    rw [neg_neg] at h
    exact h.symm
  have hbot : ∀ α : characterLattice T, α ∉ relativeRoots i → α ≠ 0 → weightSpace i α = ⊥ := by
    intro α hα h0
    by_contra hb
    exact hα ⟨h0, hb⟩
  by_cases h0 : χ = 0
  · rw [h0, neg_zero]
  rw [hbot χ hχ h0, hbot (-χ) hχ' (neg_ne_zero.mpr h0)]

omit [Mono i.hom.hom.left] in
variable (i) in
/-- The character `∑_{⟨α, ζ⟩ > 0} (dim 𝔤_α) • α` of `T`: the weights of `T` on the Lie algebra
of `G` that are positive on `ζ`, each counted with the dimension of its weight space. -/
def positiveWeightCharacter (ζ : cocharacterLattice T) : rationalCharacters T.toGrp :=
  ∑ᶠ α : characterLattice T,
    (if 0 < latticePairing T α ζ then Module.finrank k (weightSpace i α) else 0) •
      (rationalCharacters.equivCharacterLattice T).symm α

/-- Given integral reflection data, the positive-weight characters of `ζ` and `-ζ` are
opposite. -/
theorem RelativeRootReflectionData.positiveWeightCharacter_neg (D : RelativeRootReflectionData i)
    (ζ : cocharacterLattice T) :
    positiveWeightCharacter i (-ζ) = -positiveWeightCharacter i ζ := by
  unfold positiveWeightCharacter
  rw [← finsum_comp_equiv (Equiv.neg (characterLattice T)), ← finsum_neg_distrib]
  apply finsum_congr
  intro α
  simp only [Equiv.neg_apply, map_neg, LinearMap.neg_apply, neg_neg, smul_neg]
  rw [show (Equiv.neg (characterLattice T)) α = -α from rfl, D.finrank_weightSpace_neg]

end Multiplicity

/-! ### Torus weights on the Lie algebra of a dynamic unipotent subgroup -/

section LieUnipotent

variable {k : Type u} [Field k] {G : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  {T : CommGroupScheme (Spec (CommRingCat.of k))} (hT : IsSplitTorus T.toGrp)
  (i : T.toGrp ⟶ G) (ζ : cocharacterLattice T)
  {Z U : GroupScheme (Spec (CommRingCat.of k))} {iZ : Z ⟶ G} {iU : U ⟶ G}
  (hZ : (Dynamic.centralizer (CommGroupScheme.groupHom ζ ≫ i)).IsRepresentedBy iZ)
  (hU : (Dynamic.unipotent (CommGroupScheme.groupHom ζ ≫ i)).IsRepresentedBy iU)
  [IsAffineHom U.X.hom] (j : T.toGrp ⟶ Z) (hj : j ≫ iZ = i)

omit [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom] [IsAffineHom U.X.hom] in
include hj in
/-- Through `j : T ⟶ Z(ζ)`, the torus acts on `U(ζ)` by conjugation in `G` along `i`. -/
theorem centralizerAdjointAction_restrict_isEquivariant :
    ((Dynamic.centralizerAdjointAction hZ hU).restrict j).IsEquivariant
      (AutomorphicAction.conjugation i) iU := by
  intro V h g
  rw [AutomorphicAction.restrict_act, Dynamic.centralizerAdjointAction_act_comp,
    AutomorphicAction.conjugation_act, Category.assoc, ← Grp.comp_hom_hom, hj]

include hT hU in
/-- The image of `Lie U(ζ)` in `Lie G` is the sum of the weight spaces of the characters of `T`
positive on `ζ`. -/
theorem range_targetMapLinear_unipotent :
    LinearMap.range (Lie.targetMapLinear iU k) =
      ⨆ (χ : characterLattice T) (_ : 0 < latticePairing T χ ζ), weightSpace i χ := by
  have : Mono iU.hom.hom := hU.1
  rw [← RelativeRoot.tangentSubmodule_range iU, hU.2,
    ← iSup_nat_succ_weightSpace_cocharacter hT ζ i]
  ext X
  rw [RelativeRoot.mem_tangentSubmodule]
  exact (dynamicLie k G (CommGroupScheme.groupHom ζ ≫ i) X.toMul).2.2

set_option maxHeartbeats 400000 in
include hT hj in
/-- The weight space of `α` in `Lie U(ζ)` maps onto the adjoint weight space of `α` when
`⟨α, ζ⟩ > 0`, and is zero otherwise. -/
theorem map_lieWeightSpace_centralizerAdjointAction (α : characterLattice T) :
    ((Dynamic.centralizerAdjointAction hZ hU).lieWeightSpace j α).map
        (Lie.targetMapLinear iU k) =
      if 0 < latticePairing T α ζ then weightSpace i α else ⊥ := by
  have : Mono iU.hom.hom := hU.1
  have hf : ((Dynamic.centralizerAdjointAction hZ hU).restrict j).IsEquivariant
      (AutomorphicAction.conjugation i) iU :=
    centralizerAdjointAction_restrict_isEquivariant i ζ hZ hU j hj
  have h1 : (Dynamic.centralizerAdjointAction hZ hU).lieWeightSpace j α =
      RelativeRoot.actionWeightSpace ((Dynamic.centralizerAdjointAction hZ hU).restrict j) α := by
    rw [RelativeRoot.actionWeightSpace_eq_lieWeightSpace,
      AutomorphicAction.lieWeightSpace_restrict, Category.id_comp]
  rw [h1, hf.map_actionWeightSpace_eq_inf_range, RelativeRoot.actionWeightSpace_conjugation,
    range_targetMapLinear_unipotent hT i ζ hU]
  split_ifs with hα
  · exact inf_eq_left.mpr (le_iSup₂_of_le α hα le_rfl)
  · have hd := weightSpace_disjoint_iSup (p := fun χ => 0 < latticePairing T χ ζ) hT i hα
    rw [← disjoint_iff]
    exact hd

include hT hj in
/-- The dimension of the weight space of `α` in `Lie U(ζ)`. -/
theorem finrank_lieWeightSpace_centralizerAdjointAction (α : characterLattice T) :
    Module.finrank k ((Dynamic.centralizerAdjointAction hZ hU).lieWeightSpace j α) =
      if 0 < latticePairing T α ζ then Module.finrank k (weightSpace i α) else 0 := by
  have : Mono iU.hom.hom := hU.1
  have hinj := Lie.targetMapLinear_injective iU k
  rw [(Submodule.equivMapOfInjective _ hinj _).finrank_eq,
    map_lieWeightSpace_centralizerAdjointAction hT i ζ hZ hU j hj α]
  by_cases hα : 0 < latticePairing T α ζ
  · rw [ite_eq_left hα, ite_eq_left hα]
  · rw [ite_eq_right hα, ite_eq_right hα, finrank_bot]

include hT hj in
/-- The determinant character of `Lie U(ζ)` restricted along `j : T ⟶ Z(ζ)` is the
positive-weight character of `ζ`. -/
theorem characterRestrict_centralizerAdjointDeterminant [IsAffine Z.X.left] {d : ℕ}
    (c : Lie.FiniteCoordinates U d) :
    characterRestrict j ((Dynamic.centralizerAdjointAction hZ hU).determinantCharacter c) =
      positiveWeightCharacter i ζ := by
  rw [(Dynamic.centralizerAdjointAction hZ hU).determinantCharacter_restrict_eq_rootSum c hT j,
    finsum_mem_def, positiveWeightCharacter]
  apply finsum_congr
  intro α
  rw [← finrank_lieWeightSpace_centralizerAdjointAction hT i ζ hZ hU j hj α]
  by_cases hmem : α ∈ (Dynamic.centralizerAdjointAction hZ hU).lieRoots j
  · rw [Set.indicator_of_mem hmem]
  · rw [Set.indicator_of_notMem hmem]
    rw [AutomorphicAction.mem_lieRoots, not_and_or, not_not, not_not] at hmem
    rcases hmem with h0 | hb
    · rw [h0, map_zero, smul_zero]
    · rw [hb, finrank_bot, zero_smul]

end LieUnipotent

/-! ### The reduction -/

/-- Reflection data for the relative roots of a maximal split torus, detection of nonzero
rational characters by central split tori, and connected reductivity of dynamic centralizers
imply that the opposite adjoint determinant characters on a dynamic Levi add to zero. -/
theorem leviAdjointDeterminantReciprocity_of_structure
    (hRefl : RelativeRootReflectionExistenceStatement.{u})
    (hCST : CentralSplitTorusCharacterStatement.{u})
    (hRed : DynamicCentralizerReductiveStatement.{u}) :
    Dynamic.LeviAdjointDeterminantReciprocityStatement.{u} := by
  intro k _ G hG T i hi ζ Z U V iZ iU iV hZ hZ' hU hV _ _ _ d e c c'
  have : IsAffineHom G.X.hom := hG.isAffineHom
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  have : Smooth G.X.hom := hG.smooth
  have : Mono i.hom.hom.left := hi.isSplitSubtorus.mono
  have hT : IsSplitTorus T.toGrp := hi.1.1
  have hZc : IsClosedSubgroup iZ :=
    Dynamic.Affine.isClosedSubgroup_of_isRepresentedBy_centralizer _ hZ
  have hZred : IsConnectedReductive Z := hRed k G hG _ Z iZ hZc hZ
  have : IsAffineHom Z.X.hom := hZred.isAffineHom
  obtain ⟨j, -, hj⟩ := hi.exists_lift hZ hZc (range_le_centralizer_groupHom_comp i ζ)
  obtain ⟨D, -⟩ := hRefl k G hG T i hi
  have hψ : characterRestrict j
      ((Dynamic.centralizerAdjointAction hZ hU).determinantCharacter c +
        (Dynamic.centralizerAdjointAction hZ' hV).determinantCharacter c') = 0 := by
    rw [map_add, characterRestrict_centralizerAdjointDeterminant hT i ζ hZ hU j hj c,
      characterRestrict_centralizerAdjointDeterminant hT i (-ζ) hZ' hV j hj c',
      D.positiveWeightCharacter_neg, add_neg_cancel]
  by_contra hne
  obtain ⟨A, a, ha, hres⟩ := hCST k Z hZred _ hne
  obtain ⟨g, hg⟩ := ha.exists_factor_of_isMaximalSplitTorus hZc (t := j) (by rwa [hj])
  apply hres
  rw [← hg, characterRestrict_comp, AddMonoidHom.comp_apply, hψ, map_zero]

end Langlands.GroupScheme
