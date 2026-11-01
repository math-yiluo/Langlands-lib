import Langlands.Global.ArchimedeanCompactTypes
import Langlands.Global.ArchimedeanCompactGroupFiniteProof
import Langlands.Global.ArchimedeanCovarianceProof

/-! # The actual finite compact orbit as a stable continuous source -/

noncomputable section
universe u
set_option autoImplicit false

namespace Langlands.Global.ArchimedeanGL

variable (K : Type u) [Field K] [NumberField K] (n : ℕ)

namespace DerivativeSmoothFunctions

/-- The genuine enveloping algebra action transported to the derivative carrier. -/
def envelopingRepresentation :
    EnvelopingAlgebra K n →ₐ[ℂ] Module.End ℂ (DerivativeSmoothFunctions K n) :=
  ((toSmooth K n).symm.conjAlgEquiv ℂ).toAlgHom.comp (envelopingAction K n)

instance derivativeEnvelopingModule :
    Module (EnvelopingAlgebra K n) (DerivativeSmoothFunctions K n) :=
  Module.compHom _ (envelopingRepresentation K n).toRingHom

instance derivativeEnvelopingTower :
    IsScalarTower ℂ (EnvelopingAlgebra K n) (DerivativeSmoothFunctions K n) :=
  IsScalarTower.of_algebraMap_smul fun z f => by
    change envelopingRepresentation K n (algebraMap ℂ (EnvelopingAlgebra K n) z) f = z • f
    rw [AlgHom.commutes]
    rfl

@[simp]
theorem enveloping_smul_eq_operator (a : EnvelopingAlgebra K n)
    (f : DerivativeSmoothFunctions K n) :
    a • f = operator K n a f := rfl

/-- The actual compact and differential actions satisfy the genuine conjugation law. -/
theorem compactAction_enveloping_smul (k : standardInfiniteCompact K n)
    (a : EnvelopingAlgebra K n) (f : DerivativeSmoothFunctions K n) :
    compactAction K n k (a • f) =
      envelopingConjugation K n k.val a • compactAction K n k f := by
  apply (toSmooth K n).injective
  change smoothRightAction K n k.val (envelopingAction K n a (toSmooth K n f)) =
    envelopingAction K n (envelopingConjugation K n k.val a)
      (smoothRightAction K n k.val (toSmooth K n f))
  exact envelopingRightCovariance K n k.val a (toSmooth K n f)

/-- Finite compact-invariant derivative subspaces are stable under actual compact
Lie generators, using the already proved actual compact tangent curves. -/
theorem compactGenerator_smul_mem_of_finite_invariant
    (S : Submodule ℂ (DerivativeSmoothFunctions K n)) [Module.Finite ℂ S]
    (hS : ∀ k : standardInfiniteCompact K n, ∀ f ∈ S, compactAction K n k f ∈ S)
    (X : CompactComplexLieAlgebra K n)
    (f : DerivativeSmoothFunctions K n) (hf : f ∈ S) :
    compactEnvelopingGenerator K n X • f ∈ S := by
  let T := S.map (toSmooth K n).toLinearMap
  have hT : ∀ k : standardInfiniteCompact K n, ∀ v ∈ T,
      smoothRightAction K n k.val v ∈ T := by
    rintro k _ ⟨v, hv, rfl⟩
    exact ⟨compactAction K n k v, hS k v hv, toSmooth_compactAction K n k v⟩
  have hreal : ∀ Y : compactLieSubalgebra K n, ∀ v ∈ T,
      smoothDifferential K n (Y : RealLieAlgebra K n) v ∈ T := by
    intro Y v hv
    obtain ⟨c, hc0, hc⟩ := compactTangentCurve K n Y
    exact compactCurve_differential_mem K n T hT Y c hc0 hc v hv
  have hact := compactGenerator_preserves K n T hreal X (toSmooth K n f)
    (show toSmooth K n f ∈ T from ⟨f, hf, rfl⟩)
  obtain ⟨g, hg, heq⟩ := hact
  have hgf : g = compactEnvelopingGenerator K n X • f := by
    apply (toSmooth K n).injective
    change toSmooth K n g =
      envelopingAction K n (compactEnvelopingGenerator K n X) (toSmooth K n f)
    exact heq
  exact hgf ▸ hg

end DerivativeSmoothFunctions

open DerivativeSmoothFunctions

/-- Coordinates on the actual compact orbit of a compact-finite smooth vector. -/
def compactOrbitModelEquiv (f : DerivativeSmoothFunctions K n)
    (hf : Langlands.FiniteVectors.IsFiniteVector (compactAction K n) f) :
    (Fin (Module.finrank ℂ (Langlands.FiniteVectors.orbitSpan (compactAction K n) f)) → ℂ)
      ≃ₗ[ℂ] Langlands.FiniteVectors.orbitSpan (compactAction K n) f := by
  letI : Module.Finite ℂ (Langlands.FiniteVectors.orbitSpan (compactAction K n) f) := hf
  exact (Module.finBasis ℂ (Langlands.FiniteVectors.orbitSpan (compactAction K n) f)).equivFun.symm

theorem continuous_compactOrbitModelEquiv (f : DerivativeSmoothFunctions K n)
    (hf : Langlands.FiniteVectors.IsFiniteVector (compactAction K n) f) :
    Continuous (compactOrbitModelEquiv K n f hf) :=
  (compactOrbitModelEquiv K n f hf).toLinearMap.continuous_of_finiteDimensional

theorem continuous_compactOrbitModelEquiv_symm (f : DerivativeSmoothFunctions K n)
    (hf : Langlands.FiniteVectors.IsFiniteVector (compactAction K n) f) :
    Continuous (compactOrbitModelEquiv K n f hf).symm := by
  have : Module.Finite ℂ (Langlands.FiniteVectors.orbitSpan (compactAction K n) f) := hf
  exact (compactOrbitModelEquiv K n f hf).symm.toLinearMap.continuous_of_finiteDimensional

theorem continuous_compactOrbitAction (f : DerivativeSmoothFunctions K n) :
    Continuous fun p : standardInfiniteCompact K n ×
        Langlands.FiniteVectors.orbitSpan (compactAction K n) f =>
      (Langlands.FiniteVectors.orbitSubrepresentation (compactAction K n) f).toRepresentation
        p.1 p.2 := by
  have hpair : Continuous fun p : standardInfiniteCompact K n ×
      Langlands.FiniteVectors.orbitSpan (compactAction K n) f =>
      (p.1, (p.2 : DerivativeSmoothFunctions K n)) :=
    continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)
  exact ((continuous_compactAction K n).comp hpair).subtype_mk _

def compactOrbitCoordinateAction (f : DerivativeSmoothFunctions K n)
    (hf : Langlands.FiniteVectors.IsFiniteVector (compactAction K n) f) :
    _root_.Representation ℂ (standardInfiniteCompact K n)
      (Fin (Module.finrank ℂ (Langlands.FiniteVectors.orbitSpan (compactAction K n) f)) → ℂ) :=
  (((compactOrbitModelEquiv K n f hf).symm.conjAlgEquiv ℂ :
    Module.End ℂ (Langlands.FiniteVectors.orbitSpan (compactAction K n) f) →*
      Module.End ℂ
        (Fin (Module.finrank ℂ (Langlands.FiniteVectors.orbitSpan (compactAction K n) f)) → ℂ))).comp
    (Langlands.FiniteVectors.orbitSubrepresentation (compactAction K n) f).toRepresentation

theorem compactOrbitCoordinateAction_apply (f : DerivativeSmoothFunctions K n)
    (hf : Langlands.FiniteVectors.IsFiniteVector (compactAction K n) f)
    (k : standardInfiniteCompact K n)
    (v : Fin (Module.finrank ℂ (Langlands.FiniteVectors.orbitSpan (compactAction K n) f)) → ℂ) :
    compactOrbitCoordinateAction K n f hf k v =
      (compactOrbitModelEquiv K n f hf).symm
        ((Langlands.FiniteVectors.orbitSubrepresentation (compactAction K n) f).toRepresentation
          k (compactOrbitModelEquiv K n f hf v)) := rfl

theorem continuous_compactOrbitCoordinateAction (f : DerivativeSmoothFunctions K n)
    (hf : Langlands.FiniteVectors.IsFiniteVector (compactAction K n) f) :
    Continuous fun p : standardInfiniteCompact K n ×
        (Fin (Module.finrank ℂ (Langlands.FiniteVectors.orbitSpan (compactAction K n) f)) → ℂ) =>
      compactOrbitCoordinateAction K n f hf p.1 p.2 := by
  simp only [compactOrbitCoordinateAction_apply]
  have hpair : Continuous fun p : standardInfiniteCompact K n ×
      (Fin (Module.finrank ℂ (Langlands.FiniteVectors.orbitSpan (compactAction K n) f)) → ℂ) =>
      (p.1, compactOrbitModelEquiv K n f hf p.2) :=
    continuous_fst.prodMk ((continuous_compactOrbitModelEquiv K n f hf).comp continuous_snd)
  have hact := (continuous_compactOrbitAction K n f).comp hpair
  exact (continuous_compactOrbitModelEquiv_symm K n f hf).comp hact

/-- The whole actual compact orbit is a finite continuous compact source. -/
def compactOrbitSource (f : DerivativeSmoothFunctions K n)
    (hf : Langlands.FiniteVectors.IsFiniteVector (compactAction K n) f) :
    ContinuousCompactRep K n where
  dim := Module.finrank ℂ (Langlands.FiniteVectors.orbitSpan (compactAction K n) f)
  toRepresentation := compactOrbitCoordinateAction K n f hf
  continuous_action := continuous_compactOrbitCoordinateAction K n f hf

/-- The actual equivariant inclusion of the finite compact orbit source. -/
def compactOrbitSourceMap (f : DerivativeSmoothFunctions K n)
    (hf : Langlands.FiniteVectors.IsFiniteVector (compactAction K n) f) :
    (Fin (compactOrbitSource K n f hf).dim → ℂ) →ₗ[ℂ] DerivativeSmoothFunctions K n :=
  (Langlands.FiniteVectors.orbitSpan (compactAction K n) f).subtype.comp
    (compactOrbitModelEquiv K n f hf).toLinearMap

theorem range_compactOrbitSourceMap (f : DerivativeSmoothFunctions K n)
    (hf : Langlands.FiniteVectors.IsFiniteVector (compactAction K n) f) :
    LinearMap.range (compactOrbitSourceMap K n f hf) =
      Langlands.FiniteVectors.orbitSpan (compactAction K n) f := by
  apply le_antisymm
  · rintro _ ⟨v, rfl⟩
    exact (compactOrbitModelEquiv K n f hf v).property
  · intro v hv
    refine ⟨(compactOrbitModelEquiv K n f hf).symm ⟨v, hv⟩, ?_⟩
    change (compactOrbitModelEquiv K n f hf
      ((compactOrbitModelEquiv K n f hf).symm ⟨v, hv⟩)).val = v
    rw [LinearEquiv.apply_symm_apply]

theorem compactOrbitSourceMap_equivariant (f : DerivativeSmoothFunctions K n)
    (hf : Langlands.FiniteVectors.IsFiniteVector (compactAction K n) f)
    (k : standardInfiniteCompact K n) (v : Fin (compactOrbitSource K n f hf).dim → ℂ) :
    compactOrbitSourceMap K n f hf ((compactOrbitSource K n f hf).toRepresentation k v) =
      compactAction K n k (compactOrbitSourceMap K n f hf v) := by
  change (compactOrbitModelEquiv K n f hf
    ((compactOrbitModelEquiv K n f hf).symm _)).val = _
  rw [LinearEquiv.apply_symm_apply]
  rfl

/-- The finite orbit source has the exact compact-generator stability required
by the actual fixed-vector and Hom central-generation constructions. -/
theorem compactOrbitSourceMap_range_stable (f : DerivativeSmoothFunctions K n)
    (hf : Langlands.FiniteVectors.IsFiniteVector (compactAction K n) f)
    (X : CompactComplexLieAlgebra K n)
    (v : DerivativeSmoothFunctions K n) (hv : v ∈ LinearMap.range (compactOrbitSourceMap K n f hf)) :
    compactEnvelopingGenerator K n X • v ∈ LinearMap.range (compactOrbitSourceMap K n f hf) := by
  rw [range_compactOrbitSourceMap K n f hf] at hv ⊢
  have : Module.Finite ℂ (Langlands.FiniteVectors.orbitSpan (compactAction K n) f) := hf
  apply compactGenerator_smul_mem_of_finite_invariant K n
    (Langlands.FiniteVectors.orbitSpan (compactAction K n) f)
    (fun k w hw =>
      (Langlands.FiniteVectors.orbitSubrepresentation (compactAction K n) f).apply_mem_toSubmodule k hw)
    X v hv

end Langlands.Global.ArchimedeanGL
