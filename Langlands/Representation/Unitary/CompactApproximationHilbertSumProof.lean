import Langlands.Representation.Unitary.CompactApproximationHilbertSumStatement
import Langlands.Representation.Unitary.CompactApproximationOrthogonalProof

noncomputable section

namespace Langlands.Analysis

universe uG uE

/-- Canonical summation identifies the actual Hilbert sum with W and intertwines
its coordinate action with the original unitary action. -/
theorem compactApproximationHilbertSum :
    CompactApproximationHilbertSumStatement.{uG, uE} := by
  classical
  intro G _ E _ _ _ π hunit T hcompact hsymm hlim hpres W hWclosed hWinv
  obtain ⟨A, hGood, hPair, hTotal⟩ :=
    compactApproximationOrthogonal G E π hunit T hcompact hsymm hlim hpres
      W hWclosed hWinv
  have (P : A) : CompleteSpace P.1 := (hGood P.1 P.2).2.2.1.completeSpace_coe
  have hOrtho : OrthogonalFamily ℂ (fun P : A => ↥P.1)
      (fun P : A => P.1.subtypeₗᵢ) := by
    apply orthogonalFamily_iff_pairwise.mpr
    intro P Q hPQ
    exact hPair P.2 Q.2 (fun h => hPQ (Subtype.ext h))
  let H := lp (fun P : A => ↥P.1) 2
  let L : H →ₗᵢ[ℂ] E := hOrtho.linearIsometry
  have hRange : LinearMap.range L.toLinearMap = W := by
    rw [hOrtho.range_linearIsometry]
    simpa only [Submodule.subtypeₗᵢ_toLinearMap, Submodule.range_subtype,
      ← sSup_eq_iSup'] using hTotal
  have hLmem (v : H) : L v ∈ W := by
    rw [← hRange]
    exact LinearMap.mem_range_self L.toLinearMap v
  let Lw : H →ₗᵢ[ℂ] W :=
    { toLinearMap := L.toLinearMap.codRestrict W hLmem
      norm_map' := fun v => L.norm_map v }
  have hSurj : Function.Surjective Lw := by
    intro w
    have hw : (w : E) ∈ LinearMap.range L.toLinearMap := by
      rw [hRange]
      exact w.2
    obtain ⟨v, hv⟩ := hw
    exact ⟨v, Subtype.ext hv⟩
  let U : H ≃ₗᵢ[ℂ] W := LinearIsometryEquiv.ofSurjective Lw hSurj
  have hU (v : H) : (U v : E) = L v := rfl
  have hSum (v : H) : HasSum (fun P : A => (v P : E)) (U v : E) := by
    rw [hU]
    exact hOrtho.hasSum_linearIsometry v
  have hSingle (P : A) (x : P.1) : (U (lp.single 2 P x) : E) = x := by
    rw [hU]
    exact hOrtho.linearIsometry_apply_single x
  let R (g : G) : H →L[ℂ] H :=
    U.symm.toLinearIsometry.toContinuousLinearMap.comp
      (((π g).restrict (hWinv g)).comp U.toLinearIsometry.toContinuousLinearMap)
  have hR (g : G) (v : H) : (U (R g v) : E) = π g (U v) := by
    change (U (U.symm ((π g).restrict (hWinv g) (U v))) : E) = _
    rw [U.apply_symm_apply]
    rfl
  let ρ : G →* (H →L[ℂ] H) :=
    { toFun := R
      map_one' := by
        apply ContinuousLinearMap.ext
        intro v
        apply U.injective
        apply Subtype.ext
        change (U (R 1 v) : E) = (U v : E)
        rw [hR, map_one]
        rfl
      map_mul' := by
        intro g h
        apply ContinuousLinearMap.ext
        intro v
        apply U.injective
        apply Subtype.ext
        change (U (R (g * h) v) : E) = (U (R g (R h v)) : E)
        rw [hR, hR, hR, map_mul]
        rfl }
  have hEquiv (g : G) (v : H) : (U (ρ g v) : E) = π g (U v) := hR g v
  refine ⟨A, hGood, hPair, U, hSum, hSingle, ρ, ?_, hEquiv, ?_⟩
  · intro g v P
    have hNorm (x : E) : ‖π g x‖ = ‖x‖ :=
      ((π g).toLinearMap.isometryOfInner (hunit g)).norm_map x
    let w : H := ⟨fun Q : A =>
      ⟨π g (v Q), (hGood Q.1 Q.2).2.2.2.1 g (v Q) (v Q).2⟩,
      (lp.memℓp v).mono' (fun Q => (hNorm (v Q)).le)⟩
    have hw : U w = U (ρ g v) := by
      apply Subtype.ext
      calc
        (U w : E) = π g (U v) := (hSum w).unique ((π g).hasSum (hSum v))
        _ = (U (ρ g v) : E) := (hEquiv g v).symm
    exact congrArg (fun z : H => (z P : E)) (U.injective hw).symm
  · intro g v w
    calc
      inner ℂ (ρ g v) (ρ g w) = inner ℂ (U (ρ g v)) (U (ρ g w)) :=
        (U.inner_map_map _ _).symm
      _ = inner ℂ (U v) (U w) := by
        change inner ℂ (U (ρ g v) : E) (U (ρ g w) : E) =
          inner ℂ (U v : E) (U w : E)
        rw [hEquiv, hEquiv, hunit]
      _ = inner ℂ v w := U.inner_map_map v w

end Langlands.Analysis
