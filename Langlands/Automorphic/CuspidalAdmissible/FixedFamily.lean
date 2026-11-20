import Langlands.Automorphic.SmoothFamilyReproduction
import Langlands.Automorphic.AutomorphicAdmissibilityStatement
import Langlands.Automorphic.OperatorCompactCompatibility

/-! # A common kernel at fixed level and cofinite center ideal -/

noncomputable section
universe u
open MeasureTheory
set_option autoImplicit false

namespace Langlands.Automorphic.OperatorRealization

open Langlands.Global ArchimedeanGL DerivativeSmoothFunctions ContinuousRationalFunctions

variable {F : Type u} [Field F] [NumberField F] {n : ℕ} (S : OperatorRealization F n)

local instance : AddCommGroup (RationalInvariantFunctions F n) := Submodule.addCommGroup _
local instance : AddCommGroup (ContinuousRationalFunctions F n) := Submodule.addCommGroup _
local instance : AddCommGroup (FiniteSmoothRationalFunctions F n) := Submodule.addCommGroup _
local instance : AddCommGroup (StableAutomorphicFunctions F n) := Submodule.addCommGroup _
local instance : AddCommGroup S.Space := Submodule.addCommGroup _

variable (J : Ideal (EnvelopingCenter F n)) (L : Subgroup (FiniteAdelicGL F n))
variable {m : ℕ} (σ : Representation ℂ (standardInfiniteCompact F n) (Fin m → ℂ))

/-- The joint multiplicity space in a realization with values annihilated by the center ideal. -/
def annihilatedMultiplicitySpace : Submodule ℂ ((Fin m → ℂ) →ₗ[ℂ] S.Space) :=
  Langlands.jointMultiplicitySpace S.finiteRepresentation S.compactRepresentation L σ ⊓
    ⨅ v : Fin m → ℂ, ⨅ z ∈ J,
      (LinearMap.ker (S.envelopingAction (z : EnvelopingAlgebra F n))).comap (LinearMap.applyₗ v)

theorem mem_annihilatedMultiplicitySpace (T : (Fin m → ℂ) →ₗ[ℂ] S.Space) :
    T ∈ S.annihilatedMultiplicitySpace J L σ ↔
      ((∀ v, T v ∈ Langlands.fixedVectors S.finiteRepresentation L) ∧
        ∀ k v, T (σ k v) = S.compactRepresentation k (T v)) ∧
      ∀ v z, z ∈ J → S.envelopingAction (z : EnvelopingAlgebra F n) (T v) = 0 := by
  simp only [annihilatedMultiplicitySpace, Submodule.mem_inf,
    Langlands.mem_jointMultiplicitySpace, Submodule.mem_iInf, Submodule.mem_comap,
    LinearMap.mem_ker]
  rfl

/-- The submodule spanned by all values of the intertwiners in the fixed multiplicity space. -/
def multiplicityValueSpan : Submodule ℂ S.Space :=
  ⨆ T : S.annihilatedMultiplicitySpace J L σ, T.val.range

theorem mem_multiplicityValueSpan (T : S.annihilatedMultiplicitySpace J L σ) (v : Fin m → ℂ) :
    T.val v ∈ S.multiplicityValueSpan J L σ :=
  Submodule.mem_iSup_of_mem T (LinearMap.mem_range_self T.val v)

theorem multiplicityValueSpan_le_fixedVectors :
    S.multiplicityValueSpan J L σ ≤ Langlands.fixedVectors S.finiteRepresentation L := by
  apply iSup_le
  rintro T _ ⟨v, rfl⟩
  exact ((S.mem_annihilatedMultiplicitySpace J L σ T.val).mp T.property).1.1 v

theorem multiplicityValueSpan_le_ker (z : EnvelopingCenter F n) (hz : z ∈ J) :
    S.multiplicityValueSpan J L σ ≤
      LinearMap.ker (S.envelopingAction (z : EnvelopingAlgebra F n)) := by
  apply iSup_le
  rintro T _ ⟨v, rfl⟩
  exact ((S.mem_annihilatedMultiplicitySpace J L σ T.val).mp T.property).2 v z hz

/-- A realized vector's archimedean slice at a fixed finite adelic point. -/
def derivativeSlice (b : FiniteAdelicGL F n) : S.Space →ₗ[ℂ] DerivativeSmoothFunctions F n :=
  (toSmooth F n).symm.toLinearMap.comp
    ((finiteSmoothSlice F n b).comp
      ((automorphicOperatorCore F n).toSubmodule.subtype.comp S.toSubmodule.subtype))

@[simp]
theorem derivativeSlice_apply (b : FiniteAdelicGL F n) (f : S.Space) :
    S.derivativeSlice b f = (toSmooth F n).symm (finiteSmoothSlice F n b (S.ambient f)) := rfl

set_option maxHeartbeats 600000 in
theorem derivativeSlice_compactRepresentation (b : FiniteAdelicGL F n)
    (k : standardInfiniteCompact F n) (f : S.Space) :
    S.derivativeSlice b (S.compactRepresentation k f) =
      compactAction F n k (S.derivativeSlice b f) := by
  apply (toSmooth F n).injective
  rw [toSmooth_compactAction]
  simp only [derivativeSlice_apply, LinearEquiv.apply_symm_apply]
  apply Subtype.ext
  funext x
  change (finiteSmoothSlice F n b (S.ambient (S.compactRepresentation k f))).val x =
    (finiteSmoothSlice F n b (S.ambient f)).val (x * k.val)
  have he : (AdelicGL.ofInfinite F n x * AdelicGL.ofFinite F n b) * AdelicGL.ofInfinite F n k.val =
      AdelicGL.ofInfinite F n (x * k.val) * AdelicGL.ofFinite F n b := by
    simp only [map_mul, mul_assoc]
    rw [AdelicGL.ofInfinite_commute F n k.val b]
  rw [S.finiteSmoothSlice_ambient_apply, S.finiteSmoothSlice_ambient_apply,
    S.evaluate_compactRepresentation, he]

theorem derivativeSlice_envelopingAction (b : FiniteAdelicGL F n)
    (a : EnvelopingAlgebra F n) (f : S.Space) :
    S.derivativeSlice b (S.envelopingAction a f) = a • S.derivativeSlice b f := by
  apply (toSmooth F n).injective
  simp only [derivativeSlice_apply, enveloping_smul_eq_operator, toSmooth_operator,
    LinearEquiv.apply_symm_apply, S.ambient_envelopingAction, finiteSmoothSlice_envelopingAction]

variable [MeasurableSpace (InfiniteAdelicGL F n)] [BorelSpace (InfiniteAdelicGL F n)]
variable (μ : Measure (InfiniteAdelicGL F n)) [μ.IsHaarMeasure]

set_option maxHeartbeats 600000 in
/-- One kernel gives reproduction at every adelic point for all values in the fixed
multiplicity space and their linear span. -/
theorem exists_reproducingKernel_multiplicityValueSpan
    [Module.Finite ℂ (EnvelopingCenter F n ⧸ J.restrictScalars ℂ)] :
    ∃ κ : SmoothCompactKernel F n, ∀ f ∈ S.multiplicityValueSpan J L σ,
      ∀ g : AdelicGL F n, S.ReproducesAt μ κ.val.val f g := by
  let I := S.annihilatedMultiplicitySpace J L σ × FiniteAdelicGL F n
  let ρ : Representation ℂ (standardInfiniteCompact F n) (SmoothFamily F n I) :=
    SmoothFamily.compactRepresentation
  let j₀ : (Fin m → ℂ) →ₗ[ℂ] SmoothFamily F n I :=
    LinearMap.pi fun p => (S.derivativeSlice p.2).comp p.1.val
  have hj (k : standardInfiniteCompact F n) (v : Fin m → ℂ) :
      j₀ (σ k v) = ρ k (j₀ v) := by
    funext p
    change S.derivativeSlice p.2 (p.1.val (σ k v)) =
      compactAction F n k (S.derivativeSlice p.2 (p.1.val v))
    have hp := (S.mem_annihilatedMultiplicitySpace J L σ p.1.val).mp p.1.property
    exact (congrArg (S.derivativeSlice p.2) (hp.1.2 k v)).trans
      (S.derivativeSlice_compactRepresentation p.2 k (p.1.val v))
  let j : σ.IntertwiningMap ρ := j₀.intertwiningMap_of_isIntertwiningMap σ ρ hj
  have hJ (z : EnvelopingCenter F n) (hz : z ∈ J) (v : Fin m → ℂ) :
      (z : EnvelopingAlgebra F n) • j v = 0 := by
    funext p
    change (z : EnvelopingAlgebra F n) • S.derivativeSlice p.2 (p.1.val v) = 0
    rw [← S.derivativeSlice_envelopingAction,
      ((S.mem_annihilatedMultiplicitySpace J L σ p.1.val).mp p.1.property).2 v z hz, map_zero]
  obtain ⟨κ, hκ⟩ := SmoothFamily.exists_centralKernel_reproduces μ J j hJ
  let A (b : FiniteAdelicGL F n) : S.Space →ₗ[ℂ] DerivativeSmoothFunctions F n :=
    (CompactKernelAverage.smoothingLM μ κ.val).comp (S.derivativeSlice b) - S.derivativeSlice b
  have hle (b : FiniteAdelicGL F n) :
      S.multiplicityValueSpan J L σ ≤ LinearMap.ker (A b) := by
    apply iSup_le
    rintro T _ ⟨v, rfl⟩
    apply LinearMap.mem_ker.mpr
    change CompactKernelAverage.smoothingLM μ κ.val (S.derivativeSlice b (T.val v)) -
      S.derivativeSlice b (T.val v) = 0
    exact sub_eq_zero.mpr (hκ v (T, b))
  refine ⟨κ.val, fun f hf g => ?_⟩
  have hs (b : FiniteAdelicGL F n) :
      CompactKernelAverage.smoothingLM μ κ.val (S.derivativeSlice b f) = S.derivativeSlice b f :=
    sub_eq_zero.mp (LinearMap.mem_ker.mp (hle b hf))
  have H := reproducesAt_ofFinite (S := S) (μ := μ) κ.val f (AdelicGL.finite F n g)
    (hs (AdelicGL.finite F n g))
  have hg : AdelicGL.ofFinite F n (AdelicGL.finite F n g) *
      AdelicGL.ofInfinite F n (AdelicGL.infinite F n g) = g := by
    rw [← AdelicGL.ofInfinite_commute, ← AdelicGL.eq_ofInfinite_mul_ofFinite]
  simpa only [hg] using H.mul_ofInfinite (AdelicGL.infinite F n g)

end Langlands.Automorphic.OperatorRealization
