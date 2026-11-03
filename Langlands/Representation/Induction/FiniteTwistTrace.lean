import Langlands.Representation.Induction.CompactSectionTwistExpansion
import Langlands.Representation.Induction.FixedVectorModel
import Langlands.Representation.Character.Basic
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Trace

/-! Finite character coefficients for traces of actual induced Hecke operators. -/

noncomputable section

namespace Langlands.Induction

open HarmonicAnalysis MeasureTheory
open scoped Classical

universe uG uV uI

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- Identify actual fixed spaces for a character trivial on the subgroup. -/
def twistFixedSpaceEquiv (P : Subgroup G) (σ : Representation ℂ P V)
    (H : Subgroup P) (χ : P →* ℂˣ) (hχ : H ≤ χ.ker) :
    fixedVectors (twist χ σ) H ≃ₗ[ℂ] fixedVectors σ H where
  toFun v := ⟨v.val, by
    rw [← fixedVectors_twist_eq_of_le_ker χ σ H hχ]
    exact v.property⟩
  invFun v := ⟨v.val, by
    rw [fixedVectors_twist_eq_of_le_ker χ σ H hχ]
    exact v.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Evaluation identifies every allowed twisted fixed space with one common
coefficient product, before choosing a basis of that product. -/
def fixedTwistEvaluationEquiv (P : Subgroup G) (σ : Representation ℂ P V)
    (K : OpenSubgroup G) (hK : IsCompact (K : Set G)) (t : Finset G)
    (hcover : ∀ x : G, ∃ i ∈ t, ∃ p ∈ P, ∃ k ∈ K, x = p * i * k)
    (hdistinct : Function.Injective (fun i : t => DoubleCoset.mk P K.toSubgroup (i : G)))
    (χ : P →* ℂˣ) (hχ : ∀ i : t, (conjOpenSubgroup P K i).toSubgroup ≤ χ.ker) :
    fixedVectors (smoothInduced P (twist χ σ)) K.toSubgroup ≃ₗ[ℂ]
      ((i : t) → fixedVectors σ (conjOpenSubgroup P K i).toSubgroup) :=
  (fixedEvaluationEquiv P (twist χ σ) K hK t hcover hdistinct).trans
    (LinearEquiv.piCongrRight (fun i => twistFixedSpaceEquiv P σ _ χ (hχ i)))

theorem fixedTwistEvaluationEquiv_apply_val
    (P : Subgroup G) (σ : Representation ℂ P V)
    (K : OpenSubgroup G) (hK : IsCompact (K : Set G)) (t : Finset G)
    (hcover : ∀ x : G, ∃ i ∈ t, ∃ p ∈ P, ∃ k ∈ K, x = p * i * k)
    (hdistinct : Function.Injective (fun i : t => DoubleCoset.mk P K.toSubgroup (i : G)))
    (χ : P →* ℂˣ) (hχ : ∀ i : t, (conjOpenSubgroup P K i).toSubgroup ≤ χ.ker)
    (v : fixedVectors (smoothInduced P (twist χ σ)) K.toSubgroup) (i : t) :
    ((fixedTwistEvaluationEquiv P σ K hK t hcover hdistinct χ hχ v) i).val =
      eval P (twist χ σ) v.val i := rfl

theorem fixedTwistEvaluationEquiv_symm_coe
    (P : Subgroup G) (σ : Representation ℂ P V)
    (K : OpenSubgroup G) (hK : IsCompact (K : Set G)) (t : Finset G)
    (hcover : ∀ x : G, ∃ i ∈ t, ∃ p ∈ P, ∃ k ∈ K, x = p * i * k)
    (hdistinct : Function.Injective (fun i : t => DoubleCoset.mk P K.toSubgroup (i : G)))
    (χ : P →* ℂˣ) (hχ : ∀ i : t, (conjOpenSubgroup P K i).toSubgroup ≤ χ.ker)
    (v : (i : t) → fixedVectors σ (conjOpenSubgroup P K i).toSubgroup) :
    (fixedTwistEvaluationEquiv P σ K hK t hcover hdistinct χ hχ |>.symm v).val =
      ∑ i : t, (twistedDoubleCosetSection P σ K hK i (v i) χ (hχ i)).val := by
  change ((fixedEvaluationEquiv P (twist χ σ) K hK t hcover hdistinct).symm
    (fun i => (twistFixedSpaceEquiv P σ _ χ (hχ i)).symm (v i))).val = _
  rw [fixedEvaluationEquiv_symm_apply]
  change (fixedVectors (smoothInduced P (twist χ σ)) K.toSubgroup).subtype
    (∑ i : t, fixedDoubleCosetSection P (twist χ σ) K hK i
      ((twistFixedSpaceEquiv P σ _ χ (hχ i)).symm (v i))) = _
  rw [map_sum]
  rfl

variable {ι : Type uI}

/-- Extend one product-basis coordinate in one component to the full inducing
carrier by the algebraic linear left inverse of the fixed-space inclusion. -/
def fixedModelCoordinate (P : Subgroup G) (σ : Representation ℂ P V)
    (K : OpenSubgroup G) (t : Finset G)
    (b : Module.Basis ι ℂ ((i : t) → fixedVectors σ (conjOpenSubgroup P K i).toSubgroup))
    (j : ι) (i : t) : V →ₗ[ℂ] ℂ := by
  classical
  exact ((b.coord j).comp (LinearMap.single ℂ _ i)).comp
    (fixedVectors σ (conjOpenSubgroup P K i).toSubgroup).subtype.leftInverse

theorem fixedModelCoordinate_apply
    (P : Subgroup G) (σ : Representation ℂ P V) (K : OpenSubgroup G) (t : Finset G)
    (b : Module.Basis ι ℂ ((i : t) → fixedVectors σ (conjOpenSubgroup P K i).toSubgroup))
    (j : ι) (i : t) (v : fixedVectors σ (conjOpenSubgroup P K i).toSubgroup) :
    fixedModelCoordinate P σ K t b j i v.val = b.coord j (Pi.single i v) := by
  classical
  change b.coord j (LinearMap.single ℂ _ i
    ((fixedVectors σ (conjOpenSubgroup P K i).toSubgroup).subtype.leftInverse
      ((fixedVectors σ (conjOpenSubgroup P K i).toSubgroup).subtype v))) = _
  rw [LinearMap.leftInverse_apply_of_inj
    (fixedVectors σ (conjOpenSubgroup P K i).toSubgroup).ker_subtype]
  rfl

theorem fixedModelCoordinate_sum
    (P : Subgroup G) (σ : Representation ℂ P V) (K : OpenSubgroup G) (t : Finset G)
    (b : Module.Basis ι ℂ ((i : t) → fixedVectors σ (conjOpenSubgroup P K i).toSubgroup))
    (j : ι) (v : (i : t) → fixedVectors σ (conjOpenSubgroup P K i).toSubgroup) :
    ∑ i : t, fixedModelCoordinate P σ K t b j i (v i).val = b.coord j v := by
  classical
  simp_rw [fixedModelCoordinate_apply]
  rw [← map_sum, Finset.univ_sum_single]

variable [MeasurableSpace G] [BorelSpace G]
variable (μ : Measure G) [IsFiniteMeasureOnCompacts μ] [Measure.IsMulLeftInvariant μ]
variable [Fintype ι]

/-- Finite coefficients for the trace, chosen before the character. -/
def inducedFixedTraceTwistCoefficients
    (P : Subgroup G) (σ : Representation ℂ P V)
    (K : OpenSubgroup G) (t : Finset G)
    (b : Module.Basis ι ℂ ((i : t) → fixedVectors σ (conjOpenSubgroup P K i).toSubgroup))
    (f : SchwartzBruhat G) (hf : ∀ (k : K) g, f (g * (k : G)) = f g) : P →₀ ℂ :=
  ∑ j : ι, ∑ y : t, ∑ x : t,
    integratedCompactSectionTwistCoefficients μ P σ K f hf x (b j x).val
      (fixedModelCoordinate P σ K t b j y) y

/-- Character evaluation of the common coefficients is the trace of the actual
Hecke operator on the actual fixed vectors of the twisted induction. -/
theorem inducedFixedTraceTwistCoefficients_eval
    (P : Subgroup G) (σ : Representation ℂ P V)
    (K : OpenSubgroup G) (hK : IsCompact (K : Set G)) (t : Finset G)
    (hcover : ∀ x : G, ∃ i ∈ t, ∃ p ∈ P, ∃ k ∈ K, x = p * i * k)
    (hdistinct : Function.Injective (fun i : t => DoubleCoset.mk P K.toSubgroup (i : G)))
    (b : Module.Basis ι ℂ ((i : t) → fixedVectors σ (conjOpenSubgroup P K i).toSubgroup))
    (f : SchwartzBruhat G)
    (hf : f ∈ Hecke.TestFunction.biInvariant K.toSubgroup K.toSubgroup)
    (χ : P →* ℂˣ) (hχ : ∀ i : t, (conjOpenSubgroup P K i).toSubgroup ≤ χ.ker) :
    Finsupp.linearCombination ℂ (fun p : P => (χ p : ℂ))
        (inducedFixedTraceTwistCoefficients μ P σ K t b f hf.2) =
      LinearMap.trace ℂ (fixedVectors (smoothInduced P (twist χ σ)) K.toSubgroup)
        ((Hecke.integratedActionToFixed μ (smoothInduced P (twist χ σ))
          (smoothInduced_smooth P (twist χ σ)) hf).comp
            (fixedVectors (smoothInduced P (twist χ σ)) K.toSubgroup).subtype) := by
  let e := fixedTwistEvaluationEquiv P σ K hK t hcover hdistinct χ hχ
  let T := (Hecke.integratedActionToFixed μ (smoothInduced P (twist χ σ))
    (smoothInduced_smooth P (twist χ σ)) hf).comp
      (fixedVectors (smoothInduced P (twist χ σ)) K.toSubgroup).subtype
  calc
    _ = ∑ j : ι, b.coord j (e (T (e.symm (b j)))) := by
      rw [inducedFixedTraceTwistCoefficients, map_sum]
      apply Finset.sum_congr rfl
      intro j _
      rw [← fixedModelCoordinate_sum P σ K t b j (e (T (e.symm (b j)))), map_sum]
      apply Finset.sum_congr rfl
      intro y _
      rw [map_sum]
      let E : SmoothFunctions P (twist χ σ) →ₗ[ℂ] ℂ :=
        { toFun := fun F => fixedModelCoordinate P σ K t b j y
            (eval P (twist χ σ) F y)
          map_add' := fun _ _ => (fixedModelCoordinate P σ K t b j y).map_add _ _
          map_smul' := fun _ _ => (fixedModelCoordinate P σ K t b j y).map_smul _ _ }
      calc
        _ = ∑ x : t, E (Hecke.integratedAction μ (smoothInduced P (twist χ σ))
            (smoothInduced_smooth P (twist χ σ)) f
              (twistedDoubleCosetSection P σ K hK x (b j x) χ (hχ x)).val) := by
          apply Finset.sum_congr rfl
          intro x _
          exact integratedCompactSectionTwistCoefficients_eval μ P σ K hK f hf.2
            x (b j x) (fixedModelCoordinate P σ K t b j y) y χ (hχ x)
        _ = E (Hecke.integratedAction μ (smoothInduced P (twist χ σ))
              (smoothInduced_smooth P (twist χ σ)) f (e.symm (b j)).val) := by
          dsimp only [e]
          rw [fixedTwistEvaluationEquiv_symm_coe, map_sum, map_sum]
    _ = LinearMap.trace ℂ _ (e.conj T) := by
      rw [LinearMap.trace_eq_matrix_trace ℂ b]
      simp only [Matrix.trace, Matrix.diag_apply, LinearMap.toMatrix_apply,
        Module.Basis.coord_apply, LinearEquiv.conj_apply_apply]
    _ = LinearMap.trace ℂ _ T := LinearMap.trace_conj' T e

variable [T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G]

/-- Under actual admissibility, the same finite coefficients compute the
distribution character of the twisted induced representation. -/
theorem induced_distribution_eq_twistCoefficients
    (P : Subgroup G) (σ : Representation ℂ P V)
    (K : OpenSubgroup G) (hK : IsCompact (K : Set G)) (t : Finset G)
    (hcover : ∀ x : G, ∃ i ∈ t, ∃ p ∈ P, ∃ k ∈ K, x = p * i * k)
    (hdistinct : Function.Injective (fun i : t => DoubleCoset.mk P K.toSubgroup (i : G)))
    (b : Module.Basis ι ℂ ((i : t) → fixedVectors σ (conjOpenSubgroup P K i).toSubgroup))
    (f : SchwartzBruhat G)
    (hf : f ∈ Hecke.TestFunction.biInvariant K.toSubgroup K.toSubgroup)
    (χ : P →* ℂˣ) (hχ : ∀ i : t, (conjOpenSubgroup P K i).toSubgroup ≤ χ.ker)
    (hAdm : IsAdmissible (smoothInduced P (twist χ σ))) :
    Character.distribution μ (smoothInduced P (twist χ σ)) hAdm f =
      Finsupp.linearCombination ℂ (fun p : P => (χ p : ℂ))
        (inducedFixedTraceTwistCoefficients μ P σ K t b f hf.2) := by
  rw [Character.distribution_eq_fixedVectors μ _ hAdm K hf]
  exact (inducedFixedTraceTwistCoefficients_eval μ P σ K hK t hcover hdistinct
    b f hf χ hχ).symm

end Langlands.Induction
