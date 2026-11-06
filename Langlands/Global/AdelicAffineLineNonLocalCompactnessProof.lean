import Langlands.Global.AdelicAffineLineNonLocalCompactnessStatement
import Langlands.Global.GlobalPlaceTopologyFacts
import Langlands.Global.AdelicAffineLineSubspaceProof
import Mathlib.Topology.Compactness.LocallyCompact
import Mathlib.Topology.Homeomorph.Lemmas

/-! # Failure of local compactness for the adelic affine-line subspace -/

noncomputable section

universe u

open Topology Filter

namespace Langlands.Global

/-- An induced product topology with all one-coordinate spikes cannot be locally
compact if infinitely many coordinate spaces are noncompact. -/
theorem not_locallyCompactSpace_of_inducing_single
    {A B ι : Type*} {L : ι → Type*}
    [TopologicalSpace A] [TopologicalSpace B] [∀ i, TopologicalSpace (L i)]
    [Infinite ι] [DecidableEq ι] [∀ i, Zero (L i)] [∀ i, NoncompactSpace (L i)]
    (f : A → B × (∀ i, L i)) (hf : IsInducing f)
    (a₀ : A) (b₀ : B) (h₀ : f a₀ = (b₀, 0))
    (hsingle : ∀ i (x : L i), ∃ a, f a = (b₀, Pi.single i x)) :
    ¬ LocallyCompactSpace A := by
  classical
  intro hLC
  let := hLC
  obtain ⟨C, hC, hCnhds⟩ := exists_compact_mem_nhds a₀
  rw [hf.nhds_eq_comap, h₀] at hCnhds
  obtain ⟨U, hU, hUC⟩ := Filter.mem_comap.mp hCnhds
  rw [nhds_prod_eq] at hU
  obtain ⟨V, hV, W, hW, hVW⟩ := Filter.mem_prod_iff.mp hU
  rw [nhds_pi] at hW
  obtain ⟨I, t, ht, hIt⟩ := Filter.mem_pi'.mp hW
  obtain ⟨i, hi⟩ := Infinite.exists_notMem_finset I
  have hsurj : (fun a : A => (f a).2 i) '' C = Set.univ := by
    apply Set.eq_univ_of_forall
    intro x
    obtain ⟨a, ha⟩ := hsingle i x
    refine ⟨a, ?_, ?_⟩
    · apply hUC
      change f a ∈ U
      rw [ha]
      apply hVW
      refine ⟨mem_of_mem_nhds hV, hIt ?_⟩
      intro j hj
      have hji : j ≠ i := by
        intro hji
        apply hi
        simpa only [hji, Finset.mem_coe] using hj
      change Pi.single i x j ∈ t j
      rw [Pi.single_eq_of_ne hji x]
      exact mem_of_mem_nhds (ht j)
    · change (f a).2 i = x
      rw [ha]
      exact Pi.single_eq_same i x
  have hc : Continuous (fun a : A => (f a).2 i) :=
    (continuous_apply i).comp (continuous_snd.comp hf.continuous)
  exact noncompact_univ (L i) (hsurj ▸ hC.image hc)

/-- The original curve-place adelic carrier is not locally compact for the
independently defined full-product subspace topology. -/
theorem curvePlaceProductSubspace_not_locallyCompact
    (k F : Type u) [Field k] [Field F] [Algebra k F]
    [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F] [FunctionField k F] :
    letI := curvePlaceProductSubspaceAdeleTopology k F
    ¬ LocallyCompactSpace (CurvePlaceAdeleRing k F) := by
  classical
  let := curvePlaceProductSubspaceAdeleTopology k F
  let := functionField_places_infinite k F
  let (v : AlgebraicCurve.Place k F) : NoncompactSpace (curvePlaceCompletion v) :=
    curvePlaceCompletion_noncompact k F v
  let f : CurvePlaceAdeleRing k F → Unit ×
      (∀ v : AlgebraicCurve.Place k F, curvePlaceCompletion v) :=
    fun a => ((), curvePlaceCompletionProductMap k F a)
  have hraw : IsInducing (curvePlaceCompletionProductMap k F) := .induced _
  have hfc : Continuous f := continuous_const.prodMk hraw.continuous
  have hf : IsInducing f := IsInducing.of_comp hfc continuous_snd hraw
  apply not_locallyCompactSpace_of_inducing_single f hf 0 ()
  · rfl
  · intro i x
    refine ⟨RestrictedProduct.single (fun v => curvePlaceCompletionIntegers v) i x, ?_⟩
    apply Prod.ext
    · rfl
    · funext v
      exact RestrictedProduct.coe_single_apply _ i x v

/-- All infinite completion coordinates are retained while the infinitely many
finite completion coordinates obstruct local compactness. -/
theorem numberFieldProductSubspace_not_locallyCompact
    (K : Type u) [Field K] [NumberField K] :
    letI := numberFieldProductSubspaceAdeleTopology K
    ¬ LocallyCompactSpace (Adeles K) := by
  classical
  let := numberFieldProductSubspaceAdeleTopology K
  let := numberField_finitePlaces_infinite K
  let (v : FinitePlace K) : NoncompactSpace (FiniteCompletion K v) :=
    finiteCompletion_noncompact K v
  apply not_locallyCompactSpace_of_inducing_single
    (numberFieldCompletionProductMap K) (.induced _) 0 0
  · rfl
  · intro i x
    refine ⟨(0, RestrictedProduct.single (fun v : FinitePlace K =>
      v.adicCompletionIntegers K) i x), ?_⟩
    apply Prod.ext
    · rfl
    · funext v
      exact RestrictedProduct.coe_single_apply
        (fun w : FinitePlace K => w.adicCompletionIntegers K) i x v

/-- The actual affine-line range over a global function field inherits the
failure of local compactness through the proved embedding. -/
theorem curvePlaceAffineLineNonLocalCompactness :
    CurvePlaceAffineLineNonLocalCompactnessStatement.{u} := by
  intro k F _ _ _ _ _ _ _ S
  let := curvePlaceProductSubspaceAdeleTopology k F
  let := curvePlaceProjectiveAdelePointTopology k F S 1
  have hraw := curvePlaceProductSubspace_not_locallyCompact k F
  refine ⟨hraw, ?_⟩
  intro hLC
  exact hraw ((curvePlaceAffineLineSubspace k F S).toHomeomorph.locallyCompactSpace_iff.mpr hLC)

/-- The full number-field affine-line range, with every infinite factor, is
likewise not locally compact. -/
theorem numberFieldAffineLineNonLocalCompactness :
    NumberFieldAffineLineNonLocalCompactnessStatement.{u} := by
  intro K _ _ S
  let := numberFieldProductSubspaceAdeleTopology K
  let := numberFieldProjectiveAdelePointTopology K S 1
  have hraw := numberFieldProductSubspace_not_locallyCompact K
  refine ⟨hraw, ?_⟩
  intro hLC
  exact hraw ((numberFieldAffineLineSubspace K S).toHomeomorph.locallyCompactSpace_iff.mpr hLC)

/-- Conrad Example 4.3: the full-product adelic carrier and its actual standard
affine-line range in adelic projective one-space are not locally compact. -/
theorem adelicAffineLineNonLocalCompactness : AdelicAffineLineNonLocalCompactnessStatement.{u} :=
  ⟨curvePlaceAffineLineNonLocalCompactness, numberFieldAffineLineNonLocalCompactness⟩

end Langlands.Global
