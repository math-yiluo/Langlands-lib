import Langlands.Global.AdelicProjectiveRationalDensityStatement
import Langlands.Global.AdelicProjectiveComparisonProof
import Langlands.Global.GlobalCompletionWeakApproximation
import Langlands.Global.ProjectiveAffineDensity
import Mathlib.Topology.Algebra.Module.PerfectSpace

/-! # Rational-point density in actual adelic projective space -/

noncomputable section

universe u

open CategoryTheory Topology
open _root_.AlgebraicGeometry

namespace Langlands.Global

open Langlands.AlgebraicGeometry.PointTopology

private theorem denseRange_pi_of_finite_restrictions {X ι : Type*} {A : ι → Type*}
    [∀ i, TopologicalSpace (A i)] (f : X → ∀ i, A i)
    (hf : ∀ S : Finset ι, DenseRange (fun x (i : S) => f x i.val)) :
    DenseRange f := by
  intro z
  apply mem_closure_iff_nhds.mpr
  intro U hU
  rw [nhds_pi] at hU
  obtain ⟨S, t, ht, hSt⟩ := Filter.mem_pi'.mp hU
  have hN : Set.pi Set.univ (fun i : S => t i.val) ∈ 𝓝 (fun i : S => z i.val) :=
    set_pi_mem_nhds Set.finite_univ (fun i _ => ht i.val)
  obtain ⟨x, hx⟩ := (hf S).mem_nhds hN
  refine ⟨f x, hSt ?_, ⟨x, rfl⟩⟩
  intro i hi
  exact hx ⟨i, hi⟩ (Set.mem_univ _)

private theorem denseRange_projectiveAffineDiagonal (R : Type u) [CommRing R]
    {ι : Type*} (A : ι → Type u) [∀ i, Field (A i)] [∀ i, Algebra R (A i)]
    [∀ i, TopologicalSpace (A i)] [∀ i, IsTopologicalRing (A i)]
    [∀ i, IsOpenUnits (A i)] [∀ i, PerfectSpace (A i)]
    (hd : DenseRange (algebraMap R (∀ i, A i))) (n : ℕ) (j : Fin (n + 1)) :
    letI (i : ι) := schemePointTopology R (projectivePointScheme R n) (A i)
    DenseRange (fun a : ({k : Fin (n + 1) // k ≠ j} → R) =>
      fun i => projectiveAffinePoint R (A i) n j
        (fun k => algebraMap R (A i) (a k))) := by
  let (i : ι) := schemePointTopology R (projectivePointScheme R n) (A i)
  let C := {k : Fin (n + 1) // k ≠ j}
  let swap : (C → ∀ i, A i) → ∀ i, C → A i := fun a i k => a k i
  have hs : Function.Surjective swap := fun a => ⟨fun k i => a i k, rfl⟩
  have hsc : Continuous swap :=
    continuous_pi (fun i => continuous_pi (fun k =>
      (continuous_apply i).comp (continuous_apply k)))
  have hc : DenseRange (fun a : C → R => fun i k => algebraMap R (A i) (a k)) :=
    hs.denseRange.comp (DenseRange.piMap (fun _ : C => hd)) hsc
  have hp : DenseRange (Pi.map (fun i => projectiveAffinePoint R (A i) n j)) :=
    DenseRange.piMap (fun i => denseRange_projectiveAffinePoint R (A i) n j)
  exact hp.comp hc (Continuous.piMap (fun i =>
    (isOpenEmbedding_projectiveAffinePoint R (A i) n j).continuous))

section Curve

variable (k F : Type u) [Field k] [Field F] [Algebra k F] [Finite k]
variable [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F] [FunctionField k F]

omit [Finite k] [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F]
  [FunctionField k F] in
private theorem curveCompletion_perfectSpace (v : AlgebraicCurve.Place k F) :
    PerfectSpace (curvePlaceCompletion v) := by
  let : (Valued.v : Valuation (curvePlaceCompletion v) (WithZero (Multiplicative ℤ))).RankOne :=
    Valuation.IsRankOneDiscrete.rankOne _ (show (1 : NNReal) < 2 by norm_num)
  let := Valued.toNontriviallyNormedField (curvePlaceCompletion v)
    (WithZero (Multiplicative ℤ))
  infer_instance

private theorem denseRange_curveFullCompletionDiagonal :
    DenseRange (algebraMap F (∀ v : AlgebraicCurve.Place k F, curvePlaceCompletion v)) :=
  denseRange_pi_of_finite_restrictions _
    (fun S => denseRange_curvePlaceFiniteCompletionDiagonal k F S)

end Curve

/-- Weak approximation in the dense standard chart gives density of actual
rational projective points over every global function field. -/
theorem curvePlaceProjectiveRationalDensity :
    CurvePlaceProjectiveRationalDensityStatement.{u} := by
  intro k F _ _ _ _ _ _ _ S n
  let Y := projectivePointScheme F n
  let := curvePlaceProjectiveAdelePointTopology k F S n
  let := curvePlaceLocalPointTopology k F Y
  let (v : AlgebraicCurve.Place k F) : TopologicalSpace (RingPoint F Y (curvePlaceCompletion v)) :=
    schemePointTopology F Y (curvePlaceCompletion v)
  let (v : AlgebraicCurve.Place k F) : PerfectSpace (curvePlaceCompletion v) :=
    curveCompletion_perfectSpace k F v
  let d : RingPoint F Y F → CurvePlaceAdelePoints k F Y :=
    fun p => p.changeRing (Algebra.ofId F (CurvePlaceAdeleRing k F))
  let c := projectiveAffinePoint F F n 0
  let e := (curvePlaceProjectiveComparison k F S n).1.homeomorph
  have hd : DenseRange (curvePlaceAdelePointMap k F Y ∘ d ∘ c) := by
    convert denseRange_projectiveAffineDiagonal F
      (fun v : AlgebraicCurve.Place k F => curvePlaceCompletion v)
      (denseRange_curveFullCompletionDiagonal k F) n 0 using 1
    funext a v
    change ((projectiveAffinePoint F F n 0 a).changeRing
      (Algebra.ofId F (CurvePlaceAdeleRing k F))).changeRing
        (curvePlaceAdeleProjection k F v) = _
    rw [projectiveAffinePoint_changeRing, projectiveAffinePoint_changeRing]
    congr 1
  have h := e.symm.surjective.denseRange.comp hd e.symm.continuous
  have hdc : DenseRange (d ∘ c) := by
    convert h using 1
    funext a
    exact (e.symm_apply_apply (d (c a))).symm
  exact hdc.of_comp

section NumberField

variable (K : Type u) [Field K] [NumberField K]

private theorem finiteCompletion_perfectSpace (v : FinitePlace K) :
    PerfectSpace (FiniteCompletion K v) := by
  let := Valued.toNontriviallyNormedField (FiniteCompletion K v)
    (WithZero (Multiplicative ℤ))
  infer_instance

omit [NumberField K] in
private theorem infiniteCompletion_perfectSpace (v : InfinitePlace K) :
    PerfectSpace (InfiniteCompletion K v) := by
  let : NontriviallyNormedField (InfiniteCompletion K v) :=
    { (inferInstance : NormedField (InfiniteCompletion K v)) with
      non_trivial := by
        refine ⟨2, ?_⟩
        have h := (NumberField.InfinitePlace.Completion.isometry_extensionEmbedding v).norm_map_of_map_zero
            (map_zero (NumberField.InfinitePlace.Completion.extensionEmbedding v))
            (2 : InfiniteCompletion K v)
        rw [← h]
        norm_num only [map_ofNat, Complex.norm_ofNat] }
  infer_instance

private theorem denseRange_numberFieldFullCompletionDiagonal :
    DenseRange (algebraMap K ((∀ v : InfinitePlace K, InfiniteCompletion K v) ×
      (∀ v : FinitePlace K, FiniteCompletion K v))) := by
  intro z
  apply mem_closure_iff_nhds.mpr
  intro U hU
  rw [nhds_prod_eq] at hU
  obtain ⟨V, hV, W, hW, hVW⟩ := Filter.mem_prod_iff.mp hU
  rw [nhds_pi] at hW
  obtain ⟨S, t, ht, hSt⟩ := Filter.mem_pi'.mp hW
  have hN : V ×ˢ Set.pi Set.univ (fun v : S => t v.val) ∈
      𝓝 (z.1, fun v : S => z.2 v.val) :=
    prod_mem_nhds hV (set_pi_mem_nhds Set.finite_univ (fun v _ => ht v.val))
  obtain ⟨x, hx⟩ := (denseRange_numberFieldFiniteCompletionDiagonal K S).mem_nhds hN
  refine ⟨algebraMap K _ x, hVW ?_, ⟨x, rfl⟩⟩
  exact ⟨hx.1, hSt (fun v hv => hx.2 ⟨v, hv⟩ (Set.mem_univ _))⟩

end NumberField

/-- Simultaneous approximation at every finite set of places, retaining all
infinite places, gives density of actual number-field rational projective points. -/
theorem numberFieldProjectiveRationalDensity :
    NumberFieldProjectiveRationalDensityStatement.{u} := by
  intro K _ _ S n
  let Y := projectivePointScheme K n
  let := numberFieldProjectiveAdelePointTopology K S n
  let := numberFieldLocalPointTopology K Y
  let (v : InfinitePlace K) : TopologicalSpace (RingPoint K Y (InfiniteCompletion K v)) :=
    schemePointTopology K Y (InfiniteCompletion K v)
  let (v : FinitePlace K) : TopologicalSpace (RingPoint K Y (FiniteCompletion K v)) :=
    schemePointTopology K Y (FiniteCompletion K v)
  let (v : InfinitePlace K) : PerfectSpace (InfiniteCompletion K v) :=
    infiniteCompletion_perfectSpace K v
  let (v : FinitePlace K) : PerfectSpace (FiniteCompletion K v) :=
    finiteCompletion_perfectSpace K v
  let C := {i : Fin (n + 1) // i ≠ (0 : Fin (n + 1))}
  let swap : (C → ((∀ v : InfinitePlace K, InfiniteCompletion K v) ×
      (∀ v : FinitePlace K, FiniteCompletion K v))) →
      ((∀ v : InfinitePlace K, C → InfiniteCompletion K v) ×
        (∀ v : FinitePlace K, C → FiniteCompletion K v)) :=
    fun a => (fun v i => (a i).1 v, fun v i => (a i).2 v)
  have hs : Function.Surjective swap :=
    fun a => ⟨fun i => (fun v => a.1 v i, fun v => a.2 v i), rfl⟩
  have hsc : Continuous swap := Continuous.prodMk
    (continuous_pi fun v => continuous_pi fun i =>
      (continuous_apply v).comp (continuous_fst.comp (continuous_apply i)))
    (continuous_pi fun v => continuous_pi fun i =>
      (continuous_apply v).comp (continuous_snd.comp (continuous_apply i)))
  have hc := hs.denseRange.comp
    (DenseRange.piMap (fun _ : C => denseRange_numberFieldFullCompletionDiagonal K)) hsc
  have hpi := (DenseRange.piMap (fun v : InfinitePlace K =>
    denseRange_projectiveAffinePoint K (InfiniteCompletion K v) n 0)).prodMap
      (DenseRange.piMap (fun v : FinitePlace K =>
        denseRange_projectiveAffinePoint K (FiniteCompletion K v) n 0))
  have hpic : Continuous (Prod.map
      (Pi.map (fun v : InfinitePlace K => projectiveAffinePoint K (InfiniteCompletion K v) n 0))
      (Pi.map (fun v : FinitePlace K => projectiveAffinePoint K (FiniteCompletion K v) n 0))) :=
    (Continuous.piMap (fun v : InfinitePlace K =>
      (isOpenEmbedding_projectiveAffinePoint K (InfiniteCompletion K v) n 0).continuous)).prodMap
        (Continuous.piMap (fun v : FinitePlace K =>
          (isOpenEmbedding_projectiveAffinePoint K (FiniteCompletion K v) n 0).continuous))
  let d : RingPoint K Y K → NumberFieldAdelePoints K Y :=
    fun p => p.changeRing (Algebra.ofId K (Adeles K))
  let c := projectiveAffinePoint K K n 0
  let e := (numberFieldProjectiveComparison K S n).1.homeomorph
  have hd : DenseRange (numberFieldAdelePointMap K Y ∘ d ∘ c) := by
    convert hpi.comp hc hpic using 1
    funext a
    apply Prod.ext
    · funext v
      change ((projectiveAffinePoint K K n 0 a).changeRing
        (Algebra.ofId K (Adeles K))).changeRing
          (numberFieldInfiniteAdeleProjection K v) = _
      rw [projectiveAffinePoint_changeRing, projectiveAffinePoint_changeRing]
      congr 1
    · funext v
      change ((projectiveAffinePoint K K n 0 a).changeRing
        (Algebra.ofId K (Adeles K))).changeRing
          (numberFieldFiniteAdeleProjection K v) = _
      rw [projectiveAffinePoint_changeRing, projectiveAffinePoint_changeRing]
      congr 1
  have h := e.symm.surjective.denseRange.comp hd e.symm.continuous
  have hdc : DenseRange (d ∘ c) := by
    convert h using 1
    funext a
    exact (e.symm_apply_apply (d (c a))).symm
  exact hdc.of_comp

/-- The rational-point density conclusion of Conrad Example 4.3 in both
characteristics, for the actual arithmetic topology and principal point map. -/
theorem adelicProjectiveRationalDensity :
    AdelicProjectiveRationalDensityStatement.{u} :=
  ⟨curvePlaceProjectiveRationalDensity, numberFieldProjectiveRationalDensity⟩

end Langlands.Global
