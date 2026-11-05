import Langlands.Representation.CuspidalSupport.RationalNormKernelEscapingBasis

/-! # Corrected fundamental generators in the actual rational norm kernel -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Topology Filter
open scoped CategoryTheory.MonObj BigOperators

namespace Langlands.GroupScheme.SplitTorusValuation

variable (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]

/-- The canonical order-one uniformizer has field powers converging to zero. -/
theorem tendsto_uniformizerUnit_pow_zero :
    Tendsto (fun n : ℕ => (uniformizerUnit F : F) ^ n) atTop (𝓝 0) := by
  let := IsTopologicalAddGroup.rightUniformSpace F
  have := isUniformAddGroup_of_addCommGroup (G := F)
  apply Valued.tendsto_zero_pow_of_v_lt_one
  rw [IsValuativeTopology.v_eq_valuation, ← (ValuativeRel.valuation F).vlt_one_iff,
    ← FML.ord_lt_ord_iff F 1]
  simp

end Langlands.GroupScheme.SplitTorusValuation

namespace Langlands.Aubert.General.RationalPointFamily

open GroupScheme
open Langlands.AlgebraicGeometry.PointTopology
open BruhatTits.DynamicUnipotentContainment

set_option backward.isDefEq.respectTransparency false

section Cocharacters

variable {F : Type u} [Field F]
    {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
    {T : CommGroupScheme (Spec (CommRingCat.of F))}
    (i : T.toGrp ⟶ G) (ν : cocharacterLattice T) [Fintype (SimpleRoot i ν)]

/-- The maximal proper standard face omitting the specified actual simple root. -/
def fundamentalRootFace (α : SimpleRoot i ν) : Finset (SimpleRoot i ν) := by
  classical
  exact Finset.univ.erase α

@[simp] theorem mem_fundamentalRootFace (α β : SimpleRoot i ν) :
    β ∈ fundamentalRootFace i ν α ↔ β ≠ α := by
  classical
  simp [fundamentalRootFace]

/-- One positive integral direction for each simple root, with every ambient
rational character annihilating each direction. -/
structure NormKernelFundamentalCocharacters where
  cocharacter : SimpleRoot i ν → cocharacterLattice T
  standard : ∀ α, IsStandardCocharacter i ν
    (rootSet i ν (fundamentalRootFace i ν α)) (cocharacter α)
  annihilates : ∀ α (χ : rationalCharacters G),
    latticePairing T (torusCharacterRestrict i χ) (cocharacter α) = 0

variable {i ν} (d : NormKernelFundamentalCocharacters i ν)

/-- A fundamental direction pairs to zero with every other simple root. -/
theorem NormKernelFundamentalCocharacters.pair_eq_zero (α β : SimpleRoot i ν)
    (h : β ≠ α) :
    latticePairing T β.val (d.cocharacter α) = 0 :=
  (d.standard α).2.1 β.val
    ((val_mem_rootSet i ν _ β).mpr ((mem_fundamentalRootFace i ν α β).mpr h))

/-- The diagonal simple-root pairing is strictly positive. -/
theorem NormKernelFundamentalCocharacters.pair_pos (α : SimpleRoot i ν) :
    0 < latticePairing T α.val (d.cocharacter α) := by
  apply (d.standard α).2.2 α.val α.property
  intro h
  exact ((mem_fundamentalRootFace i ν α α).mp
    ((val_mem_rootSet i ν _ α).mp h)) rfl

/-- The integral lattice map underlying the positive orthant. -/
def NormKernelFundamentalCocharacters.orthantCocharacter :
    (SimpleRoot i ν → ℕ) →+ cocharacterLattice T where
  toFun n := ∑ α, n α • d.cocharacter α
  map_zero' := by simp
  map_add' n m := by simp [add_nsmul, Finset.sum_add_distrib]

/-- Each simple-root coordinate is its positive diagonal weight times the
corresponding orthant exponent. -/
theorem NormKernelFundamentalCocharacters.pair_orthantCocharacter
    (n : SimpleRoot i ν → ℕ) (α : SimpleRoot i ν) :
    latticePairing T α.val (d.orthantCocharacter n) =
      (n α : ℤ) * latticePairing T α.val (d.cocharacter α) := by
  classical
  change latticePairing T α.val (∑ β, n β • d.cocharacter β) = _
  rw [map_sum]
  simp only [map_nsmul]
  rw [Finset.sum_eq_single α]
  · exact nsmul_eq_mul _ _
  · intro β _ hβα
    rw [d.pair_eq_zero β α hβα.symm, smul_zero]
  · simp

/-- All ambient rational characters vanish on the whole orthant lattice. -/
theorem NormKernelFundamentalCocharacters.annihilates_orthantCocharacter
    (n : SimpleRoot i ν → ℕ) (χ : rationalCharacters G) :
    latticePairing T (torusCharacterRestrict i χ) (d.orthantCocharacter n) = 0 := by
  change latticePairing T (torusCharacterRestrict i χ) (∑ α, n α • d.cocharacter α) = 0
  simp [map_sum, d.annihilates]

/-- The orthant lattice has no nontrivial identifications. -/
theorem NormKernelFundamentalCocharacters.orthantCocharacter_injective :
    Function.Injective d.orthantCocharacter := by
  intro n m h
  funext α
  have hp := congrArg (latticePairing T α.val) h
  rw [d.pair_orthantCocharacter, d.pair_orthantCocharacter] at hp
  have hz := mul_right_cancel₀ (ne_of_gt (d.pair_pos α)) hp
  exact_mod_cast hz

/-- The structural standard-cocharacter premise constructs these directions by
integral Weyl correction, including when the simple-root type is empty. -/
theorem nonempty_normKernelFundamentalCocharacters
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (hν : IsGenericCocharacter i ν) (hStandard : StandardCocharacterStatement.{u}) :
    haveI := hi.isSplitSubtorus.mono
    HasRelativeRootSystem i → Nonempty (NormKernelFundamentalCocharacters i ν) := by
  have := hi.isSplitSubtorus.mono
  intro hRoots
  let := relativeWeylGroupFintype i hRoots
  have hs (α : SimpleRoot i ν) : ∃ ζ, IsStandardCocharacter i ν
      (rootSet i ν (fundamentalRootFace i ν α)) ζ :=
    (hStandard F G hG T i hi ν hν _ (rootSet_subset i ν _)).1
  refine ⟨⟨fun α => normKernelCocharacter i (hs α).choose, ?_, ?_⟩⟩
  · intro α
    exact (hs α).choose_spec.normKernelCocharacter i hi.isSplitSubtorus.1
      (fun _ hβ => hRoots.exists_isRelativeReflection hβ)
  · intro α χ
    exact latticePairing_normKernelCocharacter_restrict i (hs α).choose χ

end Cocharacters

section Points

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
    {T : CommGroupScheme (Spec (CommRingCat.of F))}
    {i : T.toGrp ⟶ G} {ν : cocharacterLattice T} [Fintype (SimpleRoot i ν)]
    (d : NormKernelFundamentalCocharacters i ν)

/-- Uniformizer evaluation of any orthant lattice point is in the actual kernel. -/
theorem NormKernelFundamentalCocharacters.orthant_mem_normKernel
    (n : SimpleRoot i ν → ℕ) :
    rationalPoints.map i (CocharacterUniformizer.latticeSection F T
      (.ofAdd (d.orthantCocharacter n))) ∈ Plancherel.rationalCommonNormKernel G := by
  rw [Plancherel.mem_rationalCommonNormKernel]
  intro χ
  change Plancherel.fieldNormUnits F (rationalCharacterEval χ
    (rationalPoints.map i (CocharacterUniformizer.cocharacterPoints F T
      (d.orthantCocharacter n) (SplitTorusValuation.uniformizerUnit F)))) = 1
  rw [rationalCharacterEval_map_cocharacterPoints,
    d.annihilates_orthantCocharacter, zpow_zero, map_one]

/-- The actual norm-kernel-valued positive orthant, evaluating every direction at
the same canonical field uniformizer. -/
def NormKernelFundamentalCocharacters.orthantHom :
    Multiplicative (SimpleRoot i ν → ℕ) →* Plancherel.rationalCommonNormKernel G :=
  (((rationalPoints.map i).comp (CocharacterUniformizer.latticeSection F T)).comp
    (AddMonoidHom.toMultiplicative d.orthantCocharacter)).codRestrict _
      (fun n => d.orthant_mem_normKernel n.toAdd)

@[simp] theorem NormKernelFundamentalCocharacters.orthantHom_val
    (n : SimpleRoot i ν → ℕ) :
    (d.orthantHom (.ofAdd n)).val =
      rationalPoints.map i (CocharacterUniformizer.latticeSection F T
        (.ofAdd (d.orthantCocharacter n))) := rfl

/-- Uniformizer evaluation retains every orthant exponent in the actual group. -/
theorem NormKernelFundamentalCocharacters.orthantHom_injective
    (hi : IsMaximalSplitTorus i) : Function.Injective d.orthantHom := by
  have := hi.isSplitSubtorus.mono
  have : Mono i.hom.hom := Over.mono_of_mono_left _
  intro n m h
  apply Multiplicative.toAdd.injective
  funext α
  have hv := congrArg Subtype.val h
  change rationalPoints.map i (CocharacterUniformizer.latticeSection F T
    (.ofAdd (d.orthantCocharacter n.toAdd))) =
      rationalPoints.map i (CocharacterUniformizer.latticeSection F T
        (.ofAdd (d.orthantCocharacter m.toAdd))) at hv
  have ht := (cancel_mono i.hom.hom).mp hv
  have hp := congrArg (fun a =>
    (Plancherel.rationalCharacterValuation T.toGrp a).toAdd
      ((rationalCharacters.equivCharacterLattice T).symm α.val)) ht
  rw [CocharacterUniformizer.rationalCharacterValuation_latticeSection,
    CocharacterUniformizer.rationalCharacterValuation_latticeSection,
    d.pair_orthantCocharacter, d.pair_orthantCocharacter] at hp
  exact_mod_cast mul_right_cancel₀ (ne_of_gt (d.pair_pos α)) hp

/-- Every orthant point belongs to each actual standard Levi in the ambient group. -/
theorem NormKernelFundamentalCocharacters.orthantHom_mem_levi
    (n : Multiplicative (SimpleRoot i ν → ℕ)) (I : Finset (SimpleRoot i ν)) :
    (d.orthantHom n).val ∈ levi i ν I := by
  apply torusPoints_le_levi i ν I
  exact (mem_torusPoints i _).mpr ⟨_, rfl⟩

/-- All actual norm-kernel points of this orthant commute. -/
theorem NormKernelFundamentalCocharacters.orthantHom_commute
    (n m : Multiplicative (SimpleRoot i ν → ℕ)) :
    Commute (d.orthantHom n) (d.orthantHom m) :=
  (show Commute n m from mul_comm _ _).map d.orthantHom

/-- The actual positive generator for the specified simple-root coordinate. -/
def NormKernelFundamentalCocharacters.generator (α : SimpleRoot i ν) :
    Plancherel.rationalCommonNormKernel G := by
  classical
  exact d.orthantHom (.ofAdd (Pi.single α 1))

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
@[simp] theorem NormKernelFundamentalCocharacters.orthantCocharacter_single
    [DecidableEq (SimpleRoot i ν)] (α : SimpleRoot i ν) (r : ℕ) :
    d.orthantCocharacter (Pi.single α r) = r • d.cocharacter α := by
  classical
  simp [orthantCocharacter]

/-- A coordinate ray is exactly the positive power sequence of its generator. -/
theorem NormKernelFundamentalCocharacters.orthantHom_single
    [DecidableEq (SimpleRoot i ν)] (α : SimpleRoot i ν) (r : ℕ) :
    d.orthantHom (.ofAdd (Pi.single α r)) = d.generator α ^ r := by
  classical
  have hs : Pi.single α r = r • (Pi.single α 1 : SimpleRoot i ν → ℕ) := by
    ext β
    by_cases h : β = α <;> simp [h]
  rw [hs, ofAdd_nsmul, map_pow]
  unfold generator
  congr 3
  ext β
  by_cases h : β = α <;> simp [h]

/-- Each generator is the specified corrected cocharacter at that same uniformizer. -/
theorem NormKernelFundamentalCocharacters.generator_val (α : SimpleRoot i ν) :
    (d.generator α).val =
      cocharPoint (CommGroupScheme.groupHom (d.cocharacter α) ≫ i)
        (SplitTorusValuation.uniformizerUnit F) := by
  classical
  change rationalPoints.map i (CocharacterUniformizer.latticeSection F T
    (.ofAdd (d.orthantCocharacter (Pi.single α 1)))) = _
  rw [d.orthantCocharacter_single, one_smul, cocharPoint_comp_eq_map_cocharacterPoints]
  rfl

/-- The actual positive generators commute inside the norm kernel. -/
theorem NormKernelFundamentalCocharacters.generator_commute (α β : SimpleRoot i ν) :
    Commute (d.generator α) (d.generator β) := by
  classical
  exact d.orthantHom_commute _ _

end Points

section EscapingBases

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
    {T : CommGroupScheme (Spec (CommRingCat.of F))}
    {i : T.toGrp ⟶ G} {ν : cocharacterLattice T} [Fintype (SimpleRoot i ν)]
    (d : NormKernelFundamentalCocharacters i ν)

local instance positiveGeneratorPointTopology : TopologicalSpace (RationalPoint F G.X) :=
  pointTopology

/-- Each specified generator escapes every compact set of the actual kernel. -/
theorem NormKernelFundamentalCocharacters.generator_escapes
    (hi : IsMaximalSplitTorus i) (α : SimpleRoot i ν) :
    CompactCoefficient.EscapesCompactSets (fun r : ℕ => d.generator α ^ r) := by
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  have : IsClosedImmersion i.hom.hom.left := hi.isSplitSubtorus.2
  have : IsAffine T.X.left := isAffine_of_isAffineHom i.hom.hom.left
  have : T2Space F := Langlands.BruhatTits.localField_t2Space F
  apply CompactCoefficient.EscapesCompactSets.of_continuous
    (f := (Subtype.val : Plancherel.rationalCommonNormKernel G → RationalPoint F G.X))
    (hf := continuous_subtype_val)
  intro C hC
  have h := eventually_cocharPoint_pow_notMem i (d.cocharacter α)
    (SplitTorusValuation.uniformizerUnit F)
    (SplitTorusValuation.tendsto_uniformizerUnit_pow_zero F) α.val (d.pair_pos α) C hC
  simpa only [← d.generator_val, Function.comp_apply, Subgroup.coe_pow] using h

/-- The opposite bases use the specified corrected generator, with the canonical
uniformizer shared by all directions. -/
theorem NormKernelFundamentalCocharacters.generator_oppositeIwahoriBasis
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    [LocallyCompactSpace (RationalPoint F G.X)]
    [NonarchimedeanGroup (RationalPoint F G.X)] [T2Space (RationalPoint F G.X)]
    (hν : IsGenericCocharacter i ν) (hStandard : StandardCocharacterStatement.{u})
    (α : SimpleRoot i ν)
    (hU : IsClosed (unipotent i ν (fundamentalRootFace i ν α) :
      Set (RationalPoint F G.X))) :
    (∀ m ∈ levi i ν (fundamentalRootFace i ν α),
      m * (d.generator α).val = (d.generator α).val * m) ∧
    Jacquet.HasOppositeIwahoriContractionBasis
      (unipotent i ν (fundamentalRootFace i ν α))
      (levi i ν (fundamentalRootFace i ν α))
      (oppositeUnipotent i (d.cocharacter α)) (d.generator α).val := by
  rw [d.generator_val]
  exact oppositeIwahoriBasis_of_cocharPoint F G hG T i hi ν hν hStandard
    (fundamentalRootFace i ν α) hU (d.cocharacter α) (d.standard α)
    (SplitTorusValuation.uniformizerUnit F)
    (SplitTorusValuation.tendsto_uniformizerUnit_pow_zero F)

/-- Actual escaping opposite-basis data for a specified coordinate ray. -/
def NormKernelFundamentalCocharacters.escapingData
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    [LocallyCompactSpace (RationalPoint F G.X)]
    [NonarchimedeanGroup (RationalPoint F G.X)] [T2Space (RationalPoint F G.X)]
    (hν : IsGenericCocharacter i ν) (hStandard : StandardCocharacterStatement.{u})
    (α : SimpleRoot i ν)
    (hU : IsClosed (unipotent i ν (fundamentalRootFace i ν α) :
      Set (RationalPoint F G.X))) :
    NormKernelEscapingOppositeIwahoriData i ν (fundamentalRootFace i ν α) where
  cocharacter := d.cocharacter α
  element := d.generator α
  standard := d.standard α
  commute := (d.generator_oppositeIwahoriBasis hG hi hν hStandard α hU).1
  basis := (d.generator_oppositeIwahoriBasis hG hi hν hStandard α hU).2
  escapes := d.generator_escapes hi α

end EscapingBases

end Langlands.Aubert.General.RationalPointFamily
