import Langlands.Representation.Archimedean.CompactWeightedOrbit
import Langlands.Representation.Archimedean.OrthogonalGroupAveraging
import Langlands.Representation.Archimedean.TranslateFinite

/-! # Density of finite orbit spans for the orthogonal group -/

noncomputable section

open MeasureTheory Set

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Archimedean

section CompactAverage

variable {K E : Type*} [Group K] [TopologicalSpace K] [IsTopologicalGroup K]
  [CompactSpace K] [MeasurableSpace K] [BorelSpace K]
  (ν : Measure K) [IsFiniteMeasure ν] [ν.IsMulLeftInvariant]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
  (R : K →* (E →L[ℂ] E)) (hR : IsContinuousRepresentation R)

local notation "ρK" => MonoidHom.comp (RingHom.toMonoidHom ContinuousLinearMap.toLinearMapRingHom) R
local notation "j" => ContinuousMap.id K

/-- Averaging the orbit of a fixed vector depends complex-linearly on the weight. -/
def compactWeightedOrbitWeightMap (v : E) : C(K, ℂ) →ₗ[ℂ] E where
  toFun u := compactWeightedOrbit ν R hR j u v
  map_add' u z := by
    rw [compactWeightedOrbit_apply, compactWeightedOrbit_apply, compactWeightedOrbit_apply,
      ← integral_add (integrable_compactWeightedOrbit ν R hR j u v)
        (integrable_compactWeightedOrbit ν R hR j z v)]
    simp only [ContinuousMap.add_apply, add_smul]
  map_smul' c u := by
    rw [compactWeightedOrbit_apply, compactWeightedOrbit_apply, ← integral_smul]
    simp only [ContinuousMap.smul_apply, smul_eq_mul, mul_smul, RingHom.id_apply]

/-- Averaging a vector against a weight with finite-dimensional left-translation span
produces a finite vector of the original action. -/
theorem isFiniteVector_compactAverage_of_finiteWeight (w : C(K, ℂ))
    (hw : FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k : K =>
      fun x : K => w (k⁻¹ * x)))) (v : E) :
    FiniteVectors.IsFiniteVector ρK (compactWeightedOrbit ν R hR j w v) := by
  let S := Submodule.span ℂ (Set.range fun k : K => fun x : K => w (k⁻¹ * x))
  let : FiniteDimensional ℂ S := hw
  let φ (k : K) : C(K, ℂ) :=
    ⟨fun x => w (k⁻¹ * x), w.continuous.comp (continuous_const.mul continuous_id)⟩
  let P := compactWeightedOrbitWeightMap ν R hR v
  let C := Submodule.span ℂ (Set.range φ)
  let T : C(K, ℂ) →ₗ[ℂ] (K → ℂ) := ContinuousMap.coeFnLinearMap ℂ
  have hC : C.map T ≤ S := by
    dsimp only [C]
    rw [Submodule.map_span]
    apply Submodule.span_le.mpr
    rintro _ ⟨_, ⟨k, rfl⟩, rfl⟩
    exact Submodule.subset_span ⟨k, rfl⟩
  let I : C →ₗ[ℂ] S := LinearMap.codRestrict S (T.comp C.subtype) fun z =>
    hC (Submodule.mem_map_of_mem z.property)
  have hI : Function.Injective I := by
    intro x y h
    apply Subtype.ext
    apply ContinuousMap.ext
    intro k
    exact congrArg (fun z : S => z.val k) h
  let : FiniteDimensional ℂ C := Module.Finite.of_injective I hI
  apply Submodule.finiteDimensional_of_le (S₂ := C.map P)
  apply Submodule.span_le.mpr
  rintro _ ⟨k, rfl⟩
  refine ⟨φ k, Submodule.subset_span ⟨k, rfl⟩, ?_⟩
  change compactWeightedOrbit ν R hR j (φ k) v = R k (compactWeightedOrbit ν R hR j w v)
  rw [compactWeightedOrbit_apply, compactWeightedOrbit_apply, ← integral_mul_left_eq_self _ k,
    ← (R k).integral_comp_comm (integrable_compactWeightedOrbit ν R hR j w v)]
  apply integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  change w (k⁻¹ * (k * x)) • R (k * x) v = R k (w x • R x v)
  rw [inv_mul_cancel_left, map_mul, mul_apply_eq_comp, map_smul]

end CompactAverage

section Orthogonal

open OrthogonalFinitePolynomial

variable (n : ℕ)

local notation "K" => Matrix.unitaryGroup (Fin n) ℝ

private theorem leftFinite_polynomialStar (w : C(K, ℂ)) (hw : w ∈ polynomialStar n) :
    FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k : K => fun x : K => w (k⁻¹ * x))) := by
  have hmem : (w : K → ℂ) ∈ polynomialFunctions n := by
    have hsub : w ∈ (polynomialStar n).toSubalgebra := hw
    rw [polynomialStar_toSubalgebra] at hsub
    clear hw
    induction hsub using Algebra.adjoin_induction with
    | mem φ hφ =>
        obtain ⟨ij, rfl⟩ := hφ
        exact entry_mem_polynomialFunctions ij
    | algebraMap c => exact (polynomialFunctions n).algebraMap_mem c
    | add f g hf hg hf' hg' => exact (polynomialFunctions n).add_mem hf' hg'
    | mul f g hf hg hf' hg' => exact (polynomialFunctions n).mul_mem hf' hg'
  obtain ⟨P, hP⟩ := exists_mvPolynomial_of_mem_polynomialFunctions hmem
  let f (x : K) : ℂ := MvPolynomial.eval (fun (ij : Fin n × Fin n) =>
    ((x : Matrix (Fin n) (Fin n) ℝ) ij.2 ij.1 : ℂ)) P
  have hf (x : K) : f x = w x⁻¹ := by
    rw [hP]
    unfold f
    congr 1
  have hTf : TranslateFinite.IsTranslateFinite (id : K → K) f := by
    have hpoly (p : MvPolynomial (Fin n × Fin n) ℂ) :
        TranslateFinite.IsTranslateFinite (id : K → K) (fun x : K =>
          MvPolynomial.eval (fun (ij : Fin n × Fin n) => ((x : Matrix (Fin n) (Fin n) ℝ) ij.2 ij.1 : ℂ)) p) := by
      induction p using MvPolynomial.induction_on with
      | C c => simpa using TranslateFinite.isTranslateFinite_const (id : K → K) c
      | add p q hp hq => simpa using TranslateFinite.isTranslateFinite_add hp hq
      | mul_X p ij hp =>
          simpa using TranslateFinite.isTranslateFinite_mul hp
            (TranslateFinite.isTranslateFinite_entry (ij.2, ij.1))
    exact hpoly P
  let L : (K → ℂ) →ₗ[ℂ] (K → ℂ) := LinearMap.funLeft ℂ ℂ (fun x : K => x⁻¹)
  let M := Submodule.span ℂ (Set.range fun k : K => Whittaker.rightTranslation ℂ K (id k) f)
  let : FiniteDimensional ℂ M := hTf
  apply Submodule.finiteDimensional_of_le (S₂ := M.map L)
  apply Submodule.span_le.mpr
  rintro _ ⟨k, rfl⟩
  refine ⟨Whittaker.rightTranslation ℂ K (id k) f, Submodule.subset_span ⟨k, rfl⟩, ?_⟩
  funext x
  change f (x⁻¹ * k) = w (k⁻¹ * x)
  simp [hf, mul_inv_rev]

/-- In a continuous Banach representation of the orthogonal group, the vectors with
finite-dimensional compact orbit span are norm dense. -/
theorem dense_finiteVectors_orthogonal
    (ν : Measure K) [ν.IsHaarMeasure]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (R : K →* (E →L[ℂ] E)) (hR : IsContinuousRepresentation R) :
    Dense ((FiniteVectors.subrepresentation
      (ContinuousLinearMap.toLinearMapRingHom.toMonoidHom.comp R)).toSubmodule : Set E) := by
  let ρK := ContinuousLinearMap.toLinearMapRingHom.toMonoidHom.comp R
  let V := (FiniteVectors.subrepresentation ρK).toSubmodule
  let W := V.topologicalClosure
  intro v
  let f : C(K, E) := ⟨fun k => R k v, hR.comp (continuous_id.prodMk continuous_const)⟩
  have htest (w : C(K, ℂ)) (hw : w ∈ polynomialStar n) : ∫ k, w k • f k ∂ν ∈ W := by
    apply V.le_topologicalClosure
    exact isFiniteVector_compactAverage_of_finiteWeight ν R hR w (leftFinite_polynomialStar n w hw) v
  have h := mem_closedSubmodule_of_polynomial_integrals_mem ν f (W := W)
    V.isClosed_topologicalClosure htest 1
  change R 1 v ∈ W at h
  rw [map_one, one_apply_eq_self] at h
  change v ∈ W
  exact h

end Orthogonal

end Langlands.Archimedean
