import Langlands.TraceFormula.HilbertSumIntertwinerDominationStatement
import Langlands.Representation.Archimedean.GKHilbertIrreducibility
import Mathlib.Analysis.Normed.Lp.lpHolder
import Mathlib.Analysis.Normed.Operator.Extend

/-! # Extension of a dominated equivariant map from a Hilbert sum -/

noncomputable section

open scoped ENNReal

namespace Langlands.TraceFormula

universe uG uι uH uE uV

variable {G : Type uG} [Group G] {ι : Type uι} {H : ι → Type uH}
  [∀ i, NormedAddCommGroup (H i)] [∀ i, InnerProductSpace ℂ (H i)]

private def sumAction (σ : (i : ι) → G →* (H i →L[ℂ] H i))
    (hσ : ∀ i g x, ‖σ i g x‖ = ‖x‖) : G →* (lp H 2 →L[ℂ] lp H 2) where
  toFun g := lp.mapCLM 2 (fun i => σ i g) zero_le_one fun i =>
    (σ i g).opNorm_le_bound zero_le_one fun x => by rw [hσ, one_mul]
  map_one' := ContinuousLinearMap.ext fun x => lp.ext (funext fun i => by
    change σ i 1 (x i) = x i
    rw [map_one]
    rfl)
  map_mul' g h := ContinuousLinearMap.ext fun x => lp.ext (funext fun i => by
    change σ i (g * h) (x i) = σ i g (σ i h (x i))
    rw [map_mul]
    rfl)

/-- A dominated test-space map extends to an intertwiner on the entire Hilbert sum
and hence vanishes if all the summand intertwiners vanish. -/
theorem hilbertSumIntertwinerDomination :
    HilbertSumIntertwinerDominationStatement.{uG, uι, uH, uE, uV} := by
  classical
  intro G _ ι H _ _ _ σ hσ E _ _ _ π hzero V _ _ v w htranslate hbound
  let ρ := sumAction σ hσ
  have hρ (g : G) (x : lp H 2) (i : ι) : ρ g x i = σ i g (x i) := rfl
  have hnorm (g : G) (x : lp H 2) : ‖ρ g x‖ = ‖x‖ := by
    rw [lp.norm_eq_tsum_rpow (by norm_num : 0 < (2 : ℝ≥0∞).toReal),
      lp.norm_eq_tsum_rpow (by norm_num : 0 < (2 : ℝ≥0∞).toReal)]
    simp_rw [hρ, hσ]
  have hinner (g : G) (x y : lp H 2) : inner ℂ (ρ g x) (ρ g y) = inner ℂ x y :=
    (LinearMap.norm_map_iff_inner_map_map (ρ g)).mp (hnorm g) x y
  let L := (LinearMap.range v).topologicalClosure
  have hL : IsClosed (L : Set (lp H 2)) := Submodule.isClosed_topologicalClosure _
  let e : V →ₗ[ℂ] L := v.codRestrict L fun f =>
    (LinearMap.range v).le_topologicalClosure (LinearMap.mem_range_self v f)
  have he : DenseRange e := by
    have hr : (Subtype.val : L → lp H 2) '' Set.range e = Set.range v := by
      exact (Set.range_comp (Subtype.val : L → lp H 2) e).symm
    rw [denseRange_iff_closure_range, Topology.IsEmbedding.subtypeVal.closure_eq_preimage_closure_image, hr]
    exact Set.eq_univ_of_forall fun x => x.property
  let U := w.extendOfNorm e
  have hU (f : V) : U (e f) = w f := LinearMap.extendOfNorm_eq he hbound f
  have hstable (g : G) (x : lp H 2) (hx : x ∈ L) : ρ g x ∈ L := by
    apply (LinearMap.range v).topologicalClosure_minimal (t := L.comap (ρ g).toLinearMap) _
      (hL.preimage (ρ g).continuous) hx
    rintro _ ⟨f, rfl⟩
    obtain ⟨f', hf', -⟩ := htranslate g f
    have h : v f' = ρ g (v f) := lp.ext (funext hf')
    change ρ g (v f) ∈ L
    exact h ▸ (e f').property
  let : CompleteSpace L := hL.completeSpace_coe
  let ρL (g : G) : L →L[ℂ] L := ((ρ g).comp L.subtypeL).codRestrict L fun x => hstable g x x.2
  have hUρ (g : G) (x : L) : U (ρL g x) = π g (U x) := by
    refine he.induction_on x (isClosed_eq (U.continuous.comp (ρL g).continuous)
      ((π g).continuous.comp U.continuous)) ?_
    intro f
    obtain ⟨f', hf', hw'⟩ := htranslate g f
    have h : ρL g (e f) = e f' := Subtype.ext (lp.ext (funext hf')).symm
    rw [h, hU, hU, hw']
  let T : lp H 2 →L[ℂ] E := U.comp L.orthogonalProjectionOnto
  have hT (g : G) (x : lp H 2) : T (ρ g x) = π g (T x) := by
    change U (L.orthogonalProjectionOnto (ρ g x)) = π g (U (L.orthogonalProjectionOnto x))
    rw [← hUρ]
    apply congrArg (fun z : L => U z)
    apply Subtype.ext
    exact Archimedean.starProjection_commutes_of_invariant ρ L hL hstable hinner g x
  have hsingle (i : ι) (g : G) (x : H i) : ρ g (lp.single 2 i x) = lp.single 2 i (σ i g x) := by
    apply lp.ext
    funext j
    rw [hρ]
    by_cases hj : j = i
    · subst j
      simp only [lp.single_apply_self]
    · simp only [lp.single_apply_ne _ _ _ hj, map_zero]
  have hkill (i : ι) : T.comp (lp.singleContinuousLinearMap ℂ H 2 i) = 0 := by
    apply hzero i
    intro g x
    change T (lp.single 2 i (σ i g x)) = π g (T (lp.single 2 i x))
    rw [← hsingle, hT]
  have hTall (x : lp H 2) : T x = 0 := by
    have hs : HasSum (fun i => T (lp.single 2 i (x i))) (T x) :=
      (lp.hasSum_single (p := 2) (by norm_num) x).mapL T
    have hz : HasSum (fun _ : ι => (0 : E)) (T x) :=
      hs.congr_fun fun i => (congrArg (fun R : H i →L[ℂ] E => R (x i)) (hkill i)).symm
    exact hz.unique hasSum_zero
  ext f
  change w f = 0
  rw [← hU]
  have hp : L.orthogonalProjectionOnto (v f) = e f := by
    change L.orthogonalProjectionOnto (e f : lp H 2) = e f
    exact L.orthogonalProjectionOnto_mem_subspace_eq_self (e f)
  simpa only [T, ContinuousLinearMap.comp_apply, hp] using hTall (v f)

end Langlands.TraceFormula
