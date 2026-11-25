import Langlands.HarmonicAnalysis.Bicharacter.SelfDual
import Mathlib.MeasureTheory.Constructions.SubmoduleQuotient
import Mathlib.MeasureTheory.Measure.Haar.Unique

/-!
# Quotients and subspaces of a finite-dimensional space over a topological field

Let `V` be a vector space over a topological field `F` with its module topology and `K` a
subspace.

* `exists_continuous_section`: the quotient map `V → V ⧸ K` has a continuous linear section;
  hence the quotient σ-algebra on `V ⧸ K` is its Borel σ-algebra (`borelSpace_quotient`).
* `isModuleTopology_submodule`: the subspace topology of a subspace is its module topology.
* `isCompact_preimage_of_injective`: the preimage of a compact set under an injective linear map
  to a Hausdorff space with the module topology is compact.
* `exists_map_eq_smul`: over a nonarchimedean local field, the image of a Haar measure under a
  linear isomorphism of finite-dimensional spaces is a positive multiple of any Haar measure on the
  target.
-/

noncomputable section

open MeasureTheory MeasureTheory.Measure
open scoped NNReal

namespace Langlands.HarmonicAnalysis

section Topology

variable {F : Type*} [Field F] [TopologicalSpace F]
  {V : Type*} [AddCommGroup V] [Module F V] [TopologicalSpace V] [IsModuleTopology F V]

/-- A linear map from a space with the module topology is continuous. -/
theorem continuous_of_linearMap' {V' : Type*} [AddCommGroup V'] [Module F V'] [TopologicalSpace V']
    [IsModuleTopology F V'] (f : V →ₗ[F] V') : Continuous f := by
  have := IsModuleTopology.toContinuousAdd F V'
  have := IsModuleTopology.toContinuousSMul F V'
  exact IsModuleTopology.continuous_of_linearMap f

/-- The quotient map of a subspace has a continuous linear section. -/
theorem exists_continuous_section (K : Submodule F V) :
    ∃ s : V ⧸ K →ₗ[F] V, K.mkQ ∘ₗ s = LinearMap.id ∧ Continuous s := by
  obtain ⟨s, hs⟩ := K.mkQ.exists_rightInverse_of_surjective (Submodule.range_mkQ K)
  exact ⟨s, hs, continuous_of_linearMap' s⟩

/-- **The quotient σ-algebra of `V ⧸ K` is the Borel σ-algebra** of the quotient topology. -/
theorem borelSpace_quotient [MeasurableSpace V] [BorelSpace V] (K : Submodule F V) :
    BorelSpace (V ⧸ K) := by
  obtain ⟨s, hs, hsc⟩ := exists_continuous_section K
  have hmk : Continuous (K.mkQ : V → V ⧸ K) := continuous_of_linearMap' K.mkQ
  refine ⟨le_antisymm ?_ ?_⟩
  · -- a measurable set `S` of the quotient is `s⁻¹ (mk⁻¹ S)`, a Borel set
    intro S hS
    have hS' : MeasurableSet ((K.mkQ : V → V ⧸ K) ⁻¹' S) := hS
    have hse : S = (s : V ⧸ K → V) ⁻¹' ((K.mkQ : V → V ⧸ K) ⁻¹' S) := by
      ext q
      simp only [Set.mem_preimage]
      rw [show K.mkQ (s q) = q from LinearMap.congr_fun hs q]
    rw [hse]
    let _ : MeasurableSpace (V ⧸ K) := borel (V ⧸ K)
    have : BorelSpace (V ⧸ K) := ⟨rfl⟩
    exact (hsc.measurable hS')
  · -- an open set of the quotient has an open, hence Borel, preimage
    refine MeasurableSpace.generateFrom_le fun S hS => ?_
    change MeasurableSet ((K.mkQ : V → V ⧸ K) ⁻¹' S)
    exact (hS.preimage hmk).measurableSet

/-- The quotient σ-algebra of `V ⧸ K` is Borel (instance form of `borelSpace_quotient`). -/
instance instBorelSpaceQuotient [MeasurableSpace V] [BorelSpace V] (K : Submodule F V) :
    BorelSpace (V ⧸ K) :=
  borelSpace_quotient K

/-- **The subspace topology of a subspace is its module topology.** -/
theorem isModuleTopology_submodule (K : Submodule F V) : IsModuleTopology F K := by
  have := IsModuleTopology.toContinuousAdd F V
  have := IsModuleTopology.toContinuousSMul F V
  obtain ⟨π, hπ⟩ := K.subtype.exists_leftInverse_of_injective K.ker_subtype
  -- `id = π ∘ incl`, and `π` is continuous from `V` to `K` with its module topology
  have hπc : @Continuous V K _ (moduleTopology F K) π := by
    let _ : TopologicalSpace K := moduleTopology F K
    have : IsModuleTopology F K := ⟨rfl⟩
    exact continuous_of_linearMap' π
  have : ContinuousAdd K := K.toAddSubmonoid.continuousAdd
  have : ContinuousSMul F K := ⟨continuous_induced_rng.2
    (continuous_smul.comp (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)))⟩
  refine IsModuleTopology.of_continuous_id ?_
  have h3 : (π ∘ K.subtype : K → K) = id := funext fun x => LinearMap.congr_fun hπ x
  rw [← h3]
  exact @Continuous.comp K V K _ _ (moduleTopology F K) _ _ hπc continuous_subtype_val

/-- The subspace topology of a subspace is its module topology (instance form). -/
instance instIsModuleTopologySubmodule (K : Submodule F V) : IsModuleTopology F K :=
  isModuleTopology_submodule K

/-- **Preimages of compact sets under injective linear maps are compact.** -/
theorem isCompact_preimage_of_injective {V' : Type*} [AddCommGroup V'] [Module F V']
    [TopologicalSpace V'] [IsModuleTopology F V'] [T2Space V'] (f : V →ₗ[F] V')
    (hf : Function.Injective f) {C : Set V'} (hC : IsCompact C) : IsCompact (f ⁻¹' C) := by
  obtain ⟨g, hg⟩ := f.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.2 hf)
  have hgc : Continuous g := continuous_of_linearMap' g
  have hfc : Continuous f := continuous_of_linearMap' f
  refine (hC.image hgc).of_isClosed_subset (hC.isClosed.preimage hfc) fun v hv => ?_
  exact ⟨f v, hv, LinearMap.congr_fun hg v⟩

end Topology

section Haar

variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {V : Type*} [AddCommGroup V] [Module F V] [FiniteDimensional F V] [TopologicalSpace V]
  [IsModuleTopology F V] [MeasurableSpace V] [BorelSpace V]
  {V' : Type*} [AddCommGroup V'] [Module F V'] [FiniteDimensional F V'] [TopologicalSpace V']
  [IsModuleTopology F V'] [MeasurableSpace V'] [BorelSpace V']

omit [MeasurableSpace V] [BorelSpace V] in
/-- A quotient of a finite-dimensional space over a nonarchimedean local field is locally
compact. -/
instance instLocallyCompactSpaceQuotient (K : Submodule F V) :
    LocallyCompactSpace (V ⧸ K) :=
  locallyCompactSpace_of_finiteDimensional F (V ⧸ K)

omit [MeasurableSpace V] [BorelSpace V] in
/-- A quotient of a finite-dimensional space over a nonarchimedean local field is Hausdorff. -/
instance instT2SpaceQuotient (K : Submodule F V) : T2Space (V ⧸ K) :=
  t2Space_of_finiteDimensional F (V ⧸ K)

omit [MeasurableSpace V] [BorelSpace V] in
/-- A quotient of a finite-dimensional space over a nonarchimedean local field is second
countable. -/
instance instSecondCountableTopologyQuotient (K : Submodule F V) :
    SecondCountableTopology (V ⧸ K) :=
  secondCountableTopology_of_finiteDimensional F (V ⧸ K)

omit [FiniteDimensional F V] [MeasurableSpace V] [BorelSpace V] in
/-- A quotient of a space with the module topology over a local field is a topological group. -/
instance instIsTopologicalAddGroupQuotient (K : Submodule F V) : IsTopologicalAddGroup (V ⧸ K) :=
  IsModuleTopology.isTopologicalAddGroup F (V ⧸ K)

omit [MeasurableSpace V] [BorelSpace V] in
/-- Every subspace of a finite-dimensional space over a nonarchimedean local field is closed. -/
theorem isClosed_submodule (K : Submodule F V) : IsClosed (K : Set V) := by
  have h : (K : Set V) = (K.mkQ : V → V ⧸ K) ⁻¹' {0} := by
    ext v; simp [Submodule.Quotient.mk_eq_zero]
  rw [h]
  exact isClosed_singleton.preimage (continuous_of_linearMap' K.mkQ)

/-- A linear isomorphism of spaces with the module topology, as an additive homeomorphism. -/
def linearEquivToContinuousAddEquiv (e : V ≃ₗ[F] V') : V ≃ₜ+ V' :=
  { e.toAddEquiv with
    continuous_toFun := continuous_of_linearMap' e.toLinearMap
    continuous_invFun := continuous_of_linearMap' e.symm.toLinearMap }

omit [ValuativeRel F] [IsNonarchimedeanLocalField F] [FiniteDimensional F V] [MeasurableSpace V]
  [BorelSpace V] [FiniteDimensional F V'] [MeasurableSpace V'] [BorelSpace V'] in
@[simp] theorem linearEquivToContinuousAddEquiv_apply (e : V ≃ₗ[F] V') (v : V) :
    linearEquivToContinuousAddEquiv e v = e v := rfl

omit [FiniteDimensional F V] in
/-- **The image of a Haar measure under a linear isomorphism** of finite-dimensional spaces over a
nonarchimedean local field is a positive multiple of any Haar measure on the target. -/
theorem exists_map_eq_smul (μ : Measure V) [μ.IsAddHaarMeasure] (ν : Measure V')
    [ν.IsAddHaarMeasure] (e : V ≃ₗ[F] V') :
    ∃ c : ℝ≥0, 0 < c ∧ μ.map e = c • ν := by
  have := IsModuleTopology.isTopologicalAddGroup F V
  have := IsModuleTopology.isTopologicalAddGroup F V'
  have := locallyCompactSpace_of_finiteDimensional F V'
  have := secondCountableTopology_of_finiteDimensional F V'
  let E := linearEquivToContinuousAddEquiv e
  have hE : (μ.map E).IsAddHaarMeasure := E.isAddHaarMeasure_map μ
  have hme : μ.map e = μ.map E := rfl
  refine ⟨addHaarScalarFactor (μ.map E) ν, addHaarScalarFactor_pos_of_isAddHaarMeasure _ _, ?_⟩
  rw [hme]
  exact isAddLeftInvariant_eq_smul (μ.map E) ν

end Haar

section HaarMap

universe u v v'

/-- The image of a Haar measure under a linear isomorphism of spaces with their module topologies
is a Haar measure. -/
instance _root_.Langlands.Theta.isAddHaarMeasure_map_linearEquiv {F : Type u} [Field F]
    [TopologicalSpace F] {X : Type v} [AddCommGroup X] [Module F X] [TopologicalSpace X]
    [IsModuleTopology F X] [IsTopologicalAddGroup X] {X' : Type v'} [AddCommGroup X']
    [Module F X'] [TopologicalSpace X'] [IsModuleTopology F X'] [MeasurableSpace X] [BorelSpace X]
    [MeasurableSpace X'] [BorelSpace X'] (e : X' ≃ₗ[F] X) (ν : Measure X')
    [ν.IsAddHaarMeasure] : (ν.map e).IsAddHaarMeasure := by
  have := IsModuleTopology.toContinuousAdd F X'
  exact AddEquiv.isAddHaarMeasure_map ν e.toAddEquiv (continuous_of_linearMap' e.toLinearMap)
    (continuous_of_linearMap' e.symm.toLinearMap)

end HaarMap

end Langlands.HarmonicAnalysis
