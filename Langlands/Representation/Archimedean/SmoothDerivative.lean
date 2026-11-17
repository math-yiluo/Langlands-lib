import Langlands.Representation.Archimedean.SmoothVectors
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions
import Mathlib.Analysis.Normed.Module.Seminorm.Norm

/-! # Genuine derivatives preserve smooth vectors -/

noncomputable section

open scoped Manifold ContDiff

namespace Langlands.Archimedean

universe u𝔤 uH uG uE

variable {𝔤 : Type u𝔤} [NormedAddCommGroup 𝔤] [NormedSpace ℝ 𝔤]
  {H : Type uH} [TopologicalSpace H] (I : ModelWithCorners ℝ 𝔤 H)
  {G : Type uG} [Group G] [TopologicalSpace G] [ChartedSpace H G]
  {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℂ E]
  (π : G →* (E →L[ℂ] E))

set_option backward.isDefEq.respectTransparency false in
/-- A bounded operator can be pulled through the orbit derivative. -/
theorem apply_lieDerivative (g : G) (X : 𝔤) {v : E}
    (hv : IsSmoothVector I π v) :
    π g (lieDerivative I π X v) =
      mfderiv I 𝓘(ℝ, E) (fun h => π (g * h) v) 1 X := by
  let A := (π g).restrictScalars ℝ
  have hf : MDifferentiableAt I 𝓘(ℝ, E) (orbitMap π v) 1 :=
    hv.mdifferentiableAt (by simp)
  have hA : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, E) A (orbitMap π v 1) :=
    A.differentiableAt.mdifferentiableAt
  have he : (fun h => π (g * h) v) = A ∘ orbitMap π v := by
    funext h
    simp only [Function.comp_apply, A, orbitMap, map_mul,
      mul_apply_eq_comp]
    rfl
  rw [he, mfderiv_comp 1 hA hf, ContinuousLinearMap.mfderiv_eq]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- Genuine derivatives are additive on smooth vectors. -/
theorem lieDerivative_add (X : 𝔤) {v w : E}
    (hv : IsSmoothVector I π v) (hw : IsSmoothVector I π w) :
    lieDerivative I π X (v + w) = lieDerivative I π X v + lieDerivative I π X w := by
  have he : orbitMap π (v + w) = orbitMap π v + orbitMap π w := by
    funext g
    exact map_add (π g) v w
  unfold lieDerivative
  rw [he, mfderiv_add (hv.mdifferentiableAt (by simp))
    (hw.mdifferentiableAt (by simp))]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- Genuine real orbit derivatives are complex linear on smooth vectors. -/
theorem lieDerivative_smul (X : 𝔤) (c : ℂ) {v : E}
    (hv : IsSmoothVector I π v) :
    lieDerivative I π X (c • v) = c • lieDerivative I π X v := by
  let A := (c • ContinuousLinearMap.id ℂ E).restrictScalars ℝ
  have hf : MDifferentiableAt I 𝓘(ℝ, E) (orbitMap π v) 1 :=
    hv.mdifferentiableAt (by simp)
  have hA : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, E) A (orbitMap π v 1) :=
    A.differentiableAt.mdifferentiableAt
  have he : orbitMap π (c • v) = A ∘ orbitMap π v := by
    funext g
    exact map_smul (π g) c v
  unfold lieDerivative
  rw [he, mfderiv_comp 1 hA hf, ContinuousLinearMap.mfderiv_eq]
  rfl

variable [LieGroup I ∞ G]

set_option backward.isDefEq.respectTransparency false in
/-- Every genuine real orbit derivative of a smooth vector is smooth. -/
theorem isSmoothVector_lieDerivative (X : 𝔤) {v : E}
    (hv : IsSmoothVector I π v) : IsSmoothVector I π (lieDerivative I π X v) := by
  have hf : ContMDiff (I.prod I) 𝓘(ℝ, E) ∞
      (fun p : G × G => π (p.1 * p.2) v) :=
    hv.comp (contMDiff_mul I ∞)
  intro g₀
  have hd := (hf.contMDiffAt (x := (g₀, (1 : G)))).mfderiv_apply (m := ∞) (x₀ := g₀)
    (fun g h : G => π (g * h) v) (fun _ : G => (1 : G))
    (fun g : G => g) (fun _ : G => X)
    contMDiffAt_const contMDiffAt_id contMDiffAt_const (by simp)
  have hc : ∀ g : G,
      inTangentCoordinates I 𝓘(ℝ, E) (fun _ : G => (1 : G))
        (fun g : G => π (g * 1) v)
        (fun g : G => mfderiv I 𝓘(ℝ, E) (fun h => π (g * h) v) 1)
        g₀ g = mfderiv I 𝓘(ℝ, E) (fun h => π (g * h) v) 1 := by
    intro g
    rw [inTangentCoordinates_eq]
    · rw [tangentBundleCore_coordChange_model_space]
      have hself : (tangentBundleCore I G).coordChange
          (achart H (1 : G)) (achart H (1 : G)) 1 =
            ContinuousLinearMap.id ℝ 𝔤 := by
        ext Y
        exact tangentCoordChange_self (mem_extChartAt_source (I := I) (1 : G))
      rw [hself, ContinuousLinearMap.id_comp, ContinuousLinearMap.comp_id]
    · exact mem_chart_source H (1 : G)
    · simp
  simp_rw [hc] at hd
  have heq : orbitMap π (lieDerivative I π X v) =
      (fun g => mfderiv I 𝓘(ℝ, E) (fun h => π (g * h) v) 1 X) := by
    funext g
    exact apply_lieDerivative I π g X hv
  rw [heq]
  exact hd

/-- The genuine derived operator restricted to the complex space of smooth vectors. -/
def smoothLieDerivative (X : 𝔤) : smoothVectors I π →ₗ[ℂ] smoothVectors I π where
  toFun v := ⟨lieDerivative I π X v, isSmoothVector_lieDerivative I π X v.property⟩
  map_add' v w := Subtype.ext (lieDerivative_add I π X v.property w.property)
  map_smul' c v := Subtype.ext (lieDerivative_smul I π X c v.property)

@[simp]
theorem smoothLieDerivative_apply (X : 𝔤) (v : smoothVectors I π) :
    (smoothLieDerivative I π X v : E) = lieDerivative I π X v := rfl

/-- A word of genuine derived operators, still acting on smooth vectors. -/
def smoothIteratedLieDerivative : List 𝔤 → smoothVectors I π →ₗ[ℂ] smoothVectors I π
  | [] => LinearMap.id
  | X :: Xs => (smoothLieDerivative I π X).comp (smoothIteratedLieDerivative Xs)

@[simp]
theorem smoothIteratedLieDerivative_apply (Xs : List 𝔤) (v : smoothVectors I π) :
    (smoothIteratedLieDerivative I π Xs v : E) = iteratedLieDerivative I π Xs v := by
  induction Xs with
  | nil => rfl
  | cons X Xs ih =>
      change lieDerivative I π X (smoothIteratedLieDerivative I π Xs v : E) = _
      rw [ih, iteratedLieDerivative_cons]

/-- Concatenating words composes their genuine derived operators in order. -/
theorem smoothIteratedLieDerivative_append (Xs Ys : List 𝔤) :
    smoothIteratedLieDerivative I π (Xs ++ Ys) =
      (smoothIteratedLieDerivative I π Xs).comp (smoothIteratedLieDerivative I π Ys) := by
  induction Xs with
  | nil => rfl
  | cons X Xs ih =>
      simp only [List.cons_append, smoothIteratedLieDerivative, ih, LinearMap.comp_assoc]

/-- The genuine word norm, bundled as a complex seminorm on smooth vectors. -/
def wordSeminorm (Xs : List 𝔤) : Seminorm ℂ (smoothVectors I π) :=
  (normSeminorm ℂ E).comp
    ((smoothVectors I π).subtype.comp (smoothIteratedLieDerivative I π Xs))

@[simp]
theorem wordSeminorm_apply (Xs : List 𝔤) (v : smoothVectors I π) :
    wordSeminorm I π Xs v = ‖iteratedLieDerivative I π Xs v‖ := by
  simp [wordSeminorm]

end Langlands.Archimedean
