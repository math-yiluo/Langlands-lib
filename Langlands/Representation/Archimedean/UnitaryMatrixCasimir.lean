import Langlands.Representation.Archimedean.BanachOrbitSmoothing
import Langlands.Representation.Archimedean.MatrixTranslationDerivatives
import Langlands.Representation.Archimedean.SmoothUnitAction
import Langlands.Representation.Archimedean.UnitaryRegularizationGraph
import Mathlib.Analysis.InnerProductSpace.Calculus

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Function MeasureTheory Set
open scoped Manifold ContDiff Matrix.Norms.Operator InnerProductSpace

namespace Langlands.Archimedean

universe uF uE

variable {F : Type uF} [RCLike F] {n : ℕ}
  {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  (π : Langlands.GeneralLinear n F →* (E →L[ℂ] E))

local notation "M" => Matrix (Fin n) (Fin n) F
local notation "G" => Langlands.GeneralLinear n F
local notation "I" => matrixModel F n
local notation "S" => smoothVectors I π

private def matrixDerivedPair (v : S) : M →ₗ[ℝ] M →ₗ[ℝ] S :=
  let D := smoothLieDerivativeDirection I π
  LinearMap.mk₂ ℝ (fun X Y => D X (D Y v))
    (fun X Y Z => by rw [map_add, LinearMap.add_apply])
    (fun r X Y => by rw [map_smul, LinearMap.smul_apply])
    (fun X Y Z => by rw [map_add, LinearMap.add_apply, map_add])
    (fun r X Y => by
      rw [map_smul, LinearMap.smul_apply]
      exact ((D X).restrictScalars ℝ).map_smul r (D Y v))

/-- The real trace Casimir in the genuine derived representation. -/
def matrixSmoothTraceCasimir : S →ₗ[ℂ] S :=
  ∑ i, smoothIteratedLieDerivative I π [matrixTraceUnit F n i, matrixTraceDualUnit F n i]

theorem matrixSmoothTraceCasimir_apply (v : S) :
    matrixSmoothTraceCasimir π v =
      ∑ i, smoothLieDerivative I π (matrixTraceUnit F n i)
        (smoothLieDerivative I π (matrixTraceDualUnit F n i) v) := by
  simp only [matrixSmoothTraceCasimir, LinearMap.sum_apply]
  rfl

/-- The trace Casimir commutes with the action of every matrix unit. -/
theorem matrixSmoothTraceCasimir_translate (g : G) (v : S) :
    matrixSmoothTraceCasimir π (smoothRepresentation I π g v) =
      smoothRepresentation I π g (matrixSmoothTraceCasimir π v) := by
  let e := matrixRealConjugation g⁻¹
  have he (X Y : M) : matrixRealTracePairing F n (e X) (e Y) = matrixRealTracePairing F n X Y :=
    matrixRealTracePairing_units_conj F n g⁻¹ X Y
  let B := matrixDerivedPair π v
  have hw (X Y : M) :
      smoothLieDerivative I π X (smoothLieDerivative I π Y (smoothRepresentation I π g v)) =
        smoothRepresentation I π g (B (e X) (e Y)) := by
    apply Subtype.ext
    change (smoothLieDerivative I π X
      (smoothLieDerivative I π Y (smoothRepresentation I π g v)) : E) =
      π g (B (e X) (e Y) : E)
    have h := DerivativeSmoothVectors.derivativeCoordinates_representation_units π [X, Y] g
      ((DerivativeSmoothVectors.toSmooth I π).symm v)
    simp only [DerivativeSmoothVectors.derivativeCoordinates_apply,
      DerivativeSmoothVectors.toSmooth_representation, LinearEquiv.apply_symm_apply,
      List.map_cons, List.map_nil, iteratedLieDerivative_cons, iteratedLieDerivative_nil] at h
    simpa only [B, matrixDerivedPair, LinearMap.mk₂_apply, smoothLieDerivativeDirection,
      LinearMap.coe_mk, AddHom.coe_mk, e, matrixRealConjugation_apply, inv_inv,
      DerivativeSmoothVectors.inverseConjugationCLM_apply, smoothLieDerivative_apply] using h
  rw [matrixSmoothTraceCasimir_apply]
  simp_rw [hw]
  rw [← map_sum, sum_matrixTraceContraction_invariant F n e he B, matrixSmoothTraceCasimir_apply]
  rfl

/-- Differentiating a unitary action in a real direction gives a skew-symmetric operator. -/
theorem inner_smoothLieDerivative_matrix (hπu : ∀ g v w, inner ℂ (π g v) (π g w) = inner ℂ v w)
    (X : M) (v w : S) :
    inner ℂ (smoothLieDerivative I π X v : E) w =
      -inner ℂ (v : E) (smoothLieDerivative I π X w : E) := by
  apply eq_neg_of_add_eq_zero_left
  let f := orbitMap π (v : E)
  let k := orbitMap π (w : E)
  have hf : MDifferentiableAt I 𝓘(ℝ, E) f (1 : G) := v.property.mdifferentiableAt (by simp)
  have hk : MDifferentiableAt I 𝓘(ℝ, E) k (1 : G) := w.property.mdifferentiableAt (by simp)
  let p : G → E × E := fun g => (f g, k g)
  let q : E × E → ℂ := fun z => inner ℂ z.1 z.2
  have hq : HasMFDerivAt (𝓘(ℝ, E).prod 𝓘(ℝ, E)) 𝓘(ℝ, ℂ) q (p 1)
      (fderivInnerCLM ℂ (p 1)) := by
    rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod]
    exact (isBoundedBilinearMap_inner (𝕜 := ℂ) (E := E)).hasFDerivAt (p 1) |>.hasMFDerivAt
  have he : q ∘ p = fun _ : G => inner ℂ (v : E) (w : E) := funext fun g => hπu g v w
  have hp : MDifferentiableAt I (𝓘(ℝ, E).prod 𝓘(ℝ, E)) p (1 : G) := hf.prodMk hk
  have h := mfderiv_comp (1 : G) hq.mdifferentiableAt hp
  have hp' : mfderiv I (𝓘(ℝ, E).prod 𝓘(ℝ, E)) p (1 : G) =
      (mfderiv I 𝓘(ℝ, E) f (1 : G)).prod (mfderiv I 𝓘(ℝ, E) k (1 : G)) := mfderiv_prodMk hf hk
  rw [he, mfderiv_const, hq.mfderiv, hp'] at h
  have h1 : p 1 = (v.val, w.val) := by simp [p, f, k, orbitMap]
  have hX := congrArg (fun T : M →L[ℝ] ℂ => T X) h.symm
  change fderivInnerCLM ℂ (p 1)
    (mfderiv I 𝓘(ℝ, E) f (1 : G) X, mfderiv I 𝓘(ℝ, E) k (1 : G) X) = 0 at hX
  simpa only [h1, fderivInnerCLM_apply, add_comm, f, k,
    smoothLieDerivative_apply, lieDerivative] using hX

/-- Two skew adjoints and the symmetric trace contraction give a symmetric operator. -/
theorem inner_matrixSmoothTraceCasimir (hπu : ∀ g v w, inner ℂ (π g v) (π g w) = inner ℂ v w)
    (v w : S) :
    inner ℂ (matrixSmoothTraceCasimir π v : E) w =
      inner ℂ (v : E) (matrixSmoothTraceCasimir π w : E) := by
  let B := matrixDerivedPair π w
  have he (X Y : M) : inner ℂ
      (smoothLieDerivative I π X (smoothLieDerivative I π Y v) : E) w =
      inner ℂ (v : E) (B Y X : E) := by
    rw [inner_smoothLieDerivative_matrix π hπu X, inner_smoothLieDerivative_matrix π hπu Y, neg_neg]
    rfl
  calc
    _ = ∑ i, inner ℂ (v : E) (B (matrixTraceDualUnit F n i) (matrixTraceUnit F n i) : E) := by
      rw [matrixSmoothTraceCasimir_apply]
      change inner ℂ ((smoothVectors I π).subtype (∑ i, _)) w = _
      simp only [map_sum, sum_inner, Submodule.subtype_apply, he]
    _ = inner ℂ (v : E) (matrixSmoothTraceCasimir π w : E) := by
      rw [← inner_sum]
      change inner ℂ (v : E) (∑ i, (smoothVectors I π).subtype (B _ _)) = _
      rw [← map_sum]
      rw [sum_matrixTraceContraction_swap F n B]
      rw [matrixSmoothTraceCasimir_apply]
      rfl

variable [CompleteSpace E] [MeasurableSpace (Langlands.GeneralLinear n F)]
  [BorelSpace (Langlands.GeneralLinear n F)]

/-- The symmetric trace Casimir is scalar on the smooth vectors of a
topologically irreducible unitary representation. -/
theorem exists_matrixSmoothTraceCasimir_eq_smul (μ : Measure G) [μ.IsHaarMeasure]
    (hπ : IsContinuousRepresentation π)
    (hπu : ∀ g v w, inner ℂ (π g v) (π g w) = inner ℂ v w)
    (hirr : IsTopologicallyIrreducible π) :
    ∃ c : ℂ, ∀ v : S, matrixSmoothTraceCasimir π v = c • v := by
  let A : S →ₗ[ℂ] E := (smoothVectors I π).subtype
  let C := matrixSmoothTraceCasimir π
  let B := A.comp C
  have hd : DenseRange (A : S → E) :=
    (dense_smoothVectors_units π μ hπ).mono (fun x hx => ⟨⟨x, hx⟩, rfl⟩)
  have hA : A ≠ 0 := by
    have := hirr.1
    obtain ⟨x, hx⟩ := exists_ne (0 : E)
    intro he
    have hclosed : IsClosed ({0} : Set E) := isClosed_singleton
    have hh : Set.range (A : S → E) ⊆ ({0} : Set E) := by
      rw [he]
      simp
    exact hx (Set.mem_singleton_iff.mp (closure_minimal hh hclosed (hd x)))
  have hstable (g : G) (v : S) : ∃ w, A w = π g (A v) ∧ B w = π g (B v) := by
    refine ⟨smoothRepresentation I π g v, rfl, ?_⟩
    change (C (smoothRepresentation I π g v) : E) = _
    rw [matrixSmoothTraceCasimir_translate]
    rfl
  obtain ⟨T, hT, he⟩ := exists_unitaryIntertwiner_of_regularization_pairing π π hπu hπu hirr
    A B hA hstable B A hd (inner_matrixSmoothTraceCasimir π hπu)
  have hc (g : G) : Commute T (π g) := ContinuousLinearMap.ext (he g)
  obtain ⟨c, hc⟩ := exists_eq_scalar_of_unitary_commute π hπu hirr T hc
  refine ⟨c, fun v => Subtype.ext ?_⟩
  change B v = c • A v
  rw [← hT, hc]
  rfl

end Langlands.Archimedean
