import Langlands.Representation.Aubert.JacquetCutComplex
import Langlands.Representation.Aubert.JacquetConcentrationReflection
import Mathlib.Algebra.Exact.Basic

/-! Transporting exactness through the actual homogeneous Jacquet equivalences. -/

noncomputable section

namespace Langlands.Aubert.ActualCutComplex

open CategoryTheory GeneralLinear SmoothRep

universe uF uV

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}
  (T : F.TopologicalData) {n : ℕ} (C : BlockShape n)
  {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- The actual degree equivalence, including its normalized Levi action. -/
def jacquetDegreeRepresentationEquiv
    (ρ : Representation ℂ (GeneralLinear n F.Carrier) V) (k : ℕ) :
    (T.normalizedJacquet C (degreeRepresentation T ρ k)).Equiv
      (jacquetDegreeRepresentation T C ρ k) :=
  Representation.Equiv.mk (jacquetDegreeEquiv T C ρ k)
    (fun m => LinearMap.ext (jacquetDegreeEquiv_intertwining T C ρ k m))

theorem jacquetDiagram_map_intertwining
    (ρ : Representation ℂ (GeneralLinear n F.Carrier) V)
    {s t : Finset (Fin (n - 1))} (h : s ⊆ t) (m : C.Levi F.Carrier)
    (x : (jacquetDiagram T C ρ).Obj s) :
    (jacquetDiagram T C ρ).map h
        (T.normalizedJacquet C (Transition.term T (shape s) ρ) m x) =
      T.normalizedJacquet C (Transition.term T (shape t) ρ) m
        ((jacquetDiagram T C ρ).map h x) :=
  LinearMap.congr_fun ((T.normalizedJacquetMap C (transition T ρ h)).isIntertwining' m) x

/-- The signed homogeneous differential with the actual coordinate Levi actions. -/
def jacquetDegreeDifferential
    (ρ : Representation ℂ (GeneralLinear n F.Carrier) V) (k : ℕ) :
    (jacquetDegreeRepresentation T C ρ k).IntertwiningMap
      (jacquetDegreeRepresentation T C ρ (k + 1)) where
  toLinearMap := (jacquetDiagram T C ρ).degreeDifferential k
  isIntertwining' m := LinearMap.ext
    (EquivariantDiagram.degreeDifferential_intertwining (jacquetDiagram T C ρ)
      (fun s => T.normalizedJacquet C (Transition.term T (shape s) ρ))
      (jacquetDiagram_map_intertwining T C ρ) k m)

/-- The degree equivalences give a square of actual intertwiners. -/
theorem jacquetDegreeRepresentationEquiv_differential
    (ρ : Representation ℂ (GeneralLinear n F.Carrier) V) (k : ℕ) :
    (jacquetDegreeRepresentationEquiv T C ρ (k + 1)).toIntertwiningMap.comp
        (T.normalizedJacquetMap C (differential T ρ k)) =
      (jacquetDegreeDifferential T C ρ k).comp
        (jacquetDegreeRepresentationEquiv T C ρ k).toIntertwiningMap := by
  apply Representation.IntertwiningMap.ext
  exact LinearMap.ext (jacquetDegreeEquiv_differential T C ρ k)

/-- Injectivity is unchanged by the actual degreewise Jacquet comparison. -/
theorem jacquetDifferential_injective_iff
    (ρ : Representation ℂ (GeneralLinear n F.Carrier) V) (k : ℕ) :
    Function.Injective (T.normalizedJacquetMap C (differential T ρ k)) ↔
      Function.Injective ((jacquetDiagram T C ρ).degreeDifferential k) := by
  constructor
  · intro hf x y hxy
    apply (jacquetDegreeEquiv T C ρ k).symm.injective
    apply hf
    apply (jacquetDegreeEquiv T C ρ (k + 1)).injective
    simpa only [jacquetDegreeEquiv_differential, LinearEquiv.apply_symm_apply] using hxy
  · intro hg x y hxy
    apply (jacquetDegreeEquiv T C ρ k).injective
    apply hg
    rw [← jacquetDegreeEquiv_differential, ← jacquetDegreeEquiv_differential, hxy]

/-- Middle exactness is unchanged by the actual degreewise Jacquet comparison. -/
theorem jacquetDifferential_exact_iff
    (ρ : Representation ℂ (GeneralLinear n F.Carrier) V) (k : ℕ) :
    LinearMap.range (T.normalizedJacquetMap C (differential T ρ k)).toLinearMap =
        LinearMap.ker (T.normalizedJacquetMap C (differential T ρ (k + 1))).toLinearMap ↔
      LinearMap.range ((jacquetDiagram T C ρ).degreeDifferential k) =
        LinearMap.ker ((jacquetDiagram T C ρ).degreeDifferential (k + 1)) := by
  have h := LinearMap.exact_iff_of_surjective_of_bijective_of_injective
    (T.normalizedJacquetMap C (differential T ρ k)).toLinearMap
    (T.normalizedJacquetMap C (differential T ρ (k + 1))).toLinearMap
    ((jacquetDiagram T C ρ).degreeDifferential k)
    ((jacquetDiagram T C ρ).degreeDifferential (k + 1))
    (jacquetDegreeEquiv T C ρ k).toLinearMap
    (jacquetDegreeEquiv T C ρ (k + 1)).toLinearMap
    (jacquetDegreeEquiv T C ρ (k + 1 + 1)).toLinearMap
    (LinearMap.ext (fun x => (jacquetDegreeEquiv_differential T C ρ k x).symm))
    (LinearMap.ext (fun x => (jacquetDegreeEquiv_differential T C ρ (k + 1) x).symm))
    (jacquetDegreeEquiv T C ρ k).surjective
    (jacquetDegreeEquiv T C ρ (k + 1)).bijective
    (jacquetDegreeEquiv T C ρ (k + 1 + 1)).injective
  constructor
  · intro hex
    exact (LinearMap.exact_iff.mp (h.mp (LinearMap.exact_iff.mpr hex.symm))).symm
  · intro hex
    exact (LinearMap.exact_iff.mp (h.mpr (LinearMap.exact_iff.mpr hex.symm))).symm

/-- Vanishing of each degree is unchanged by the genuine quotient equivalence. -/
theorem jacquetDegree_subsingleton_iff
    (ρ : Representation ℂ (GeneralLinear n F.Carrier) V) (k : ℕ) :
    Subsingleton (C.JacquetModule (degreeRepresentation T ρ k)) ↔
      Subsingleton ((jacquetDiagram T C ρ).Degree k) :=
  (jacquetDegreeEquiv T C ρ k).toEquiv.subsingleton_congr

/-- The existing concentration condition can be checked on the actual
coordinate Jacquet diagram, with its unchanged exterior signs. -/
theorem jacquetConcentratedAt_iff_diagram (P : BlockShape n → Prop) :
    letI := T.topology
    ∀ (A : SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear n F.Carrier)) (m : ℕ),
      JacquetConcentratedAt F T P A m ↔
        (0 < m → ∀ C, P C →
          Function.Injective ((jacquetDiagram T C A.representation).degreeDifferential 0)) ∧
        (∀ i, i + 1 < m → ∀ C, P C →
          LinearMap.range ((jacquetDiagram T C A.representation).degreeDifferential i) =
            LinearMap.ker
              ((jacquetDiagram T C A.representation).degreeDifferential (i + 1))) ∧
        (∀ k, m < k → ∀ C, P C →
          Subsingleton ((jacquetDiagram T C A.representation).Degree k)) := by
  let := T.topology
  intro A m
  constructor
  · rintro ⟨hinj, hex, hzero⟩
    refine ⟨fun hm C hC => ?_, fun i hi C hC => ?_, fun k hk C hC => ?_⟩
    · exact (jacquetDifferential_injective_iff T C A.representation 0).mp (hinj hm C hC)
    · exact (jacquetDifferential_exact_iff T C A.representation i).mp (hex i hi C hC)
    · exact (jacquetDegree_subsingleton_iff T C A.representation k).mp (hzero k hk C hC)
  · rintro ⟨hinj, hex, hzero⟩
    refine ⟨fun hm C hC => ?_, fun i hi C hC => ?_, fun k hk C hC => ?_⟩
    · exact (jacquetDifferential_injective_iff T C A.representation 0).mpr (hinj hm C hC)
    · exact (jacquetDifferential_exact_iff T C A.representation i).mpr (hex i hi C hC)
    · exact (jacquetDegree_subsingleton_iff T C A.representation k).mpr (hzero k hk C hC)

end Langlands.Aubert.ActualCutComplex
