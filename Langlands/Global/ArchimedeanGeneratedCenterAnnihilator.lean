import Langlands.Global.ArchimedeanCompactTypes
import Langlands.Global.ArchimedeanCenterFinite
import Langlands.Global.ArchimedeanCovarianceProof
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix
import Mathlib.LinearAlgebra.Isomorphisms

/-! # A common center annihilator for the actual generated module -/

noncomputable section
universe u
set_option autoImplicit false

namespace Langlands.Global.ArchimedeanGL

open DerivativeSmoothFunctions

private theorem finite_quotient_ker_end
    {Z V : Type*} [CommRing Z] [Algebra ℂ Z] [AddCommGroup V] [Module ℂ V]
    [Module.Finite ℂ V] (A : Z →ₐ[ℂ] Module.End ℂ V) :
    Module.Finite ℂ (Z ⧸ (RingHom.ker A.toRingHom).restrictScalars ℂ) := by
  change Module.Finite ℂ (Z ⧸ LinearMap.ker A.toLinearMap)
  have : Module.Finite ℂ (Module.End ℂ V) := Module.Finite.linearMap ℂ ℂ V V
  have : Module.Finite ℂ A.toLinearMap.range := inferInstance
  exact Module.Finite.of_injective A.toLinearMap.quotKerEquivRange.toLinearMap
    A.toLinearMap.quotKerEquivRange.injective

variable (K : Type u) [Field K] [NumberField K] (n : ℕ)

/-- Covariance preserves finiteness of the whole center orbit without requiring
the center-conjugation automorphism to be pointwise the identity. -/
theorem isCenterFinite_smoothRightAction (g : InfiniteAdelicGL K n)
    {f : SmoothFunctions K n} (hf : IsCenterFinite K n f) :
    IsCenterFinite K n (smoothRightAction K n g f) := by
  have : Module.Finite ℂ (centerOrbitSpan K n f) := hf
  apply Submodule.finiteDimensional_of_le
    (S₂ := (centerOrbitSpan K n f).map (smoothRightAction K n g))
  apply Submodule.span_le.mpr
  rintro _ ⟨z, rfl⟩
  change centerAction K n z (smoothRightAction K n g f) ∈
    (centerOrbitSpan K n f).map (smoothRightAction K n g)
  refine ⟨centerAction K n ((centerConjugation K n g).symm z) f,
    centerAction_mem_centerOrbitSpan K n f _, ?_⟩
  rw [centerRightCovariance]
  simp only [AlgEquiv.apply_symm_apply]

/-- Center translates of the whole actual compact orbit of one smooth vector. -/
def compactCenterSeedSpan (f : SmoothFunctions K n) :
    Submodule ℂ (SmoothFunctions K n) :=
  Submodule.span ℂ (Set.range fun p : standardInfiniteCompact K n × EnvelopingCenter K n =>
    centerAction K n p.2 (smoothRightAction K n p.1.val f))

theorem compactAction_mem_compactCenterSeedSpan (f : SmoothFunctions K n)
    (k : standardInfiniteCompact K n) :
    smoothRightAction K n k.val f ∈ compactCenterSeedSpan K n f := by
  have h : centerAction K n 1 (smoothRightAction K n k.val f) ∈
      compactCenterSeedSpan K n f :=
    Submodule.subset_span ⟨(k, 1), rfl⟩
  simpa only [map_one, Module.End.one_apply] using h

/-- Compact finiteness and center finiteness give a finite joint seed even when
the compact action merely normalizes the center action. -/
theorem compactCenterSeedSpan_finite (f : SmoothFunctions K n)
    (hf : Langlands.FiniteVectors.IsFiniteVector
      ((smoothRightAction K n).comp (standardInfiniteCompact K n).subtype) f)
    (hz : IsCenterFinite K n f) :
    Module.Finite ℂ (compactCenterSeedSpan K n f) := by
  classical
  obtain ⟨s, hs, hspan⟩ :=
    (Submodule.fg_span_iff_fg_span_finset_subset
      (Set.range fun k : standardInfiniteCompact K n =>
        smoothRightAction K n k.val f)).mp
      (Module.Finite.iff_fg.mp hf)
  let k : s → standardInfiniteCompact K n := fun i => (hs i.property).choose
  have hk (i : s) : smoothRightAction K n (k i).val f = i.val :=
    (hs i.property).choose_spec
  let S : Submodule ℂ (SmoothFunctions K n) :=
    ⨆ i : s, centerOrbitSpan K n (smoothRightAction K n (k i).val f)
  have : ∀ i : s, Module.Finite ℂ
      (centerOrbitSpan K n (smoothRightAction K n (k i).val f)) :=
    fun i => isCenterFinite_smoothRightAction K n (k i).val hz
  have : Module.Finite ℂ S := Submodule.finite_iSup _
  apply Submodule.finiteDimensional_of_le (S₂ := S)
  apply Submodule.span_le.mpr
  rintro _ ⟨⟨l, z⟩, rfl⟩
  have hle : Submodule.span ℂ (s : Set (SmoothFunctions K n)) ≤
      S.comap (centerAction K n z) := by
    apply Submodule.span_le.mpr
    intro v hv
    let i : s := ⟨v, hv⟩
    change centerAction K n z i.val ∈ S
    rw [← hk i]
    exact (le_iSup
      (fun j : s => centerOrbitSpan K n (smoothRightAction K n (k j).val f)) i)
      (centerAction_mem_centerOrbitSpan K n _ z)
  apply hle
  rw [← hspan]
  exact Langlands.FiniteVectors.action_mem_orbitSpan
    ((smoothRightAction K n).comp (standardInfiniteCompact K n).subtype) l f

/-- The finite seed is invariant under the full actual center action. -/
theorem centerAction_mem_compactCenterSeedSpan (f : SmoothFunctions K n)
    (z : EnvelopingCenter K n) {v : SmoothFunctions K n}
    (hv : v ∈ compactCenterSeedSpan K n f) :
    centerAction K n z v ∈ compactCenterSeedSpan K n f := by
  induction hv using Submodule.span_induction with
  | mem v hv =>
    obtain ⟨⟨k, w⟩, rfl⟩ := hv
    rw [← Module.End.mul_apply, ← map_mul]
    exact Submodule.subset_span ⟨(k, z * w), rfl⟩
  | zero => simp
  | add v w hv hw ihv ihw =>
    simpa only [map_add] using Submodule.add_mem _ ihv ihw
  | smul c v hv ih =>
    simpa only [map_smul] using Submodule.smul_mem _ c ih

/-- The actual center representation restricted to its invariant compact seed. -/
def compactCenterSeedAction (f : SmoothFunctions K n) :
    EnvelopingCenter K n →ₐ[ℂ] Module.End ℂ (compactCenterSeedSpan K n f) where
  toFun z := (centerAction K n z).restrict
    (fun _ hv => centerAction_mem_compactCenterSeedSpan K n f z hv)
  map_zero' := by
    apply LinearMap.ext
    intro v
    apply Subtype.ext
    simp
  map_one' := by
    apply LinearMap.ext
    intro v
    apply Subtype.ext
    simp
  map_add' z w := by
    apply LinearMap.ext
    intro v
    apply Subtype.ext
    simp
  map_mul' z w := by
    apply LinearMap.ext
    intro v
    apply Subtype.ext
    simp [Module.End.mul_apply]
  commutes' c := by
    apply LinearMap.ext
    intro v
    apply Subtype.ext
    simp

@[simp]
theorem compactCenterSeedAction_apply (f : SmoothFunctions K n)
    (z : EnvelopingCenter K n) (v : compactCenterSeedSpan K n f) :
    (compactCenterSeedAction K n f z v).val = centerAction K n z v.val := rfl

/-- One center ideal annihilating the whole compact seed. -/
def compactCenterSeedAnnihilator (f : SmoothFunctions K n) :
    Ideal (EnvelopingCenter K n) :=
  RingHom.ker (compactCenterSeedAction K n f).toRingHom

theorem compactCenterSeedAnnihilator_restrictScalars (f : SmoothFunctions K n) :
    (compactCenterSeedAnnihilator K n f).restrictScalars ℂ =
      LinearMap.ker (compactCenterSeedAction K n f).toLinearMap := rfl

theorem centerAction_eq_zero_of_mem_compactCenterSeedAnnihilator
    (f : SmoothFunctions K n) {z : EnvelopingCenter K n}
    (hz : z ∈ compactCenterSeedAnnihilator K n f)
    {v : SmoothFunctions K n} (hv : v ∈ compactCenterSeedSpan K n f) :
    centerAction K n z v = 0 := by
  have h : compactCenterSeedAction K n f z = 0 := hz
  have hval := congrArg
    (fun A : Module.End ℂ (compactCenterSeedSpan K n f) =>
      (A ⟨v, hv⟩).val) h
  exact hval

set_option backward.isDefEq.respectTransparency false in
/-- The kernel has finite complex codimension since its quotient embeds into
the endomorphism algebra of the finite-dimensional compact seed. -/
theorem compactCenterSeedAnnihilator_finite_quotient (f : SmoothFunctions K n)
    (hf : Langlands.FiniteVectors.IsFiniteVector
      ((smoothRightAction K n).comp (standardInfiniteCompact K n).subtype) f)
    (hz : IsCenterFinite K n f) :
    Module.Finite ℂ (EnvelopingCenter K n ⧸
      (compactCenterSeedAnnihilator K n f).restrictScalars ℂ) := by
  have hS : Module.Finite ℂ (compactCenterSeedSpan K n f) :=
    compactCenterSeedSpan_finite K n f hf hz
  change Module.Finite ℂ (EnvelopingCenter K n ⧸
    (RingHom.ker (compactCenterSeedAction K n f).toRingHom).restrictScalars ℂ)
  exact @finite_quotient_ker_end (EnvelopingCenter K n) (compactCenterSeedSpan K n f)
    inferInstance inferInstance inferInstance inferInstance hS (compactCenterSeedAction K n f)

/-- Centrality extends annihilation of the compact seed to all its enveloping
derivatives, in the action order used by the actual generated module. -/
theorem centerAction_generated_eq_zero
    (f : SmoothFunctions K n) {z : EnvelopingCenter K n}
    (hz : z ∈ compactCenterSeedAnnihilator K n f)
    (k : standardInfiniteCompact K n) (a : EnvelopingAlgebra K n) :
    centerAction K n z
      (smoothRightAction K n k.val (envelopingAction K n a f)) = 0 := by
  rw [envelopingRightCovariance, centerAction_apply,
    ← envelopingAction_mul, ← centerInclusion_commute, envelopingAction_mul]
  change envelopingAction K n (envelopingConjugation K n k.val a)
    (centerAction K n z (smoothRightAction K n k.val f)) = 0
  rw [centerAction_eq_zero_of_mem_compactCenterSeedAnnihilator K n f hz
    (compactAction_mem_compactCenterSeedSpan K n f k), map_zero]

/-- The same ideal kills the entire algebraic compact-and-enveloping span. -/
theorem centerAction_generatedSpan_eq_zero
    (f : SmoothFunctions K n) {z : EnvelopingCenter K n}
    (hz : z ∈ compactCenterSeedAnnihilator K n f)
    {v : SmoothFunctions K n}
    (hv : v ∈ Submodule.span ℂ
      (Set.range fun p : standardInfiniteCompact K n × EnvelopingAlgebra K n =>
        smoothRightAction K n p.1.val (envelopingAction K n p.2 f))) :
    centerAction K n z v = 0 := by
  have hle : Submodule.span ℂ
      (Set.range fun p : standardInfiniteCompact K n × EnvelopingAlgebra K n =>
        smoothRightAction K n p.1.val (envelopingAction K n p.2 f)) ≤
      LinearMap.ker (centerAction K n z) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨⟨k, a⟩, rfl⟩
    exact centerAction_generated_eq_zero K n f hz k a
  exact hle hv

/-- A compact-finite, center-finite vector has one finite-codimensional center
ideal annihilating its whole actual generated differential module. -/
theorem exists_common_center_ideal_generatedCompactDifferentialSpan
    (f : DerivativeSmoothFunctions K n)
    (hf : Langlands.FiniteVectors.IsFiniteVector (compactAction K n) f)
    (hz : IsCenterFinite K n (toSmooth K n f)) :
    ∃ I : Ideal (EnvelopingCenter K n),
      Module.Finite ℂ (EnvelopingCenter K n ⧸ I.restrictScalars ℂ) ∧
      ∀ z ∈ I, ∀ x, x ∈ Submodule.span ℂ
        (Set.range fun p : standardInfiniteCompact K n × EnvelopingAlgebra K n =>
          compactAction K n p.1 (operator K n p.2 f)) →
        operator K n (centerInclusion K n z) x = 0 := by
  have hfs : Langlands.FiniteVectors.IsFiniteVector
      ((smoothRightAction K n).comp (standardInfiniteCompact K n).subtype)
      (toSmooth K n f) :=
    hf.map (compactActionEquiv K n).toIntertwiningMap
  refine ⟨compactCenterSeedAnnihilator K n (toSmooth K n f),
    compactCenterSeedAnnihilator_finite_quotient K n _ hfs hz, ?_⟩
  intro z hz x hx
  have hle : Submodule.span ℂ
      (Set.range fun p : standardInfiniteCompact K n × EnvelopingAlgebra K n =>
        compactAction K n p.1 (operator K n p.2 f)) ≤
      LinearMap.ker ((centerAction K n z).comp (toSmooth K n).toLinearMap) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨⟨k, a⟩, rfl⟩
    change centerAction K n z
      (toSmooth K n (compactAction K n k (operator K n a f))) = 0
    rw [toSmooth_compactAction, toSmooth_operator]
    exact centerAction_generated_eq_zero K n (toSmooth K n f) hz k a
  apply (toSmooth K n).injective
  change centerAction K n z (toSmooth K n x) = 0
  exact hle hx

end Langlands.Global.ArchimedeanGL
