import Langlands.Global.ArchimedeanCartanTensorAction
import Mathlib.Topology.Instances.Matrix

/-! # Actual compact Hom sources for fixed-vector generation -/

noncomputable section
universe u w
set_option autoImplicit false

namespace Langlands.Global.ArchimedeanGL

variable (K : Type u) [Field K] [NumberField K] (n : ℕ)

/-- Coordinates on the finite Hom space, without a topology on linear maps. -/
def compactHomModelEquiv (σ τ : ContinuousCompactRep K n) :
    (Fin (Module.finrank ℂ ((Fin σ.dim → ℂ) →ₗ[ℂ] (Fin τ.dim → ℂ))) → ℂ) ≃ₗ[ℂ]
      ((Fin σ.dim → ℂ) →ₗ[ℂ] (Fin τ.dim → ℂ)) :=
  (Module.finBasis ℂ ((Fin σ.dim → ℂ) →ₗ[ℂ] (Fin τ.dim → ℂ))).equivFun.symm

/-- The natural conjugation action on a finite Hom space, in the canonical
finite-dimensional continuous compact representation model. -/
def ContinuousCompactRep.linHom (σ τ : ContinuousCompactRep K n) :
    ContinuousCompactRep K n where
  dim := Module.finrank ℂ ((Fin σ.dim → ℂ) →ₗ[ℂ] (Fin τ.dim → ℂ))
  toRepresentation :=
    (((compactHomModelEquiv K n σ τ).symm.conjAlgEquiv ℂ :
      Module.End ℂ ((Fin σ.dim → ℂ) →ₗ[ℂ] (Fin τ.dim → ℂ)) →*
        Module.End ℂ
          (Fin (Module.finrank ℂ ((Fin σ.dim → ℂ) →ₗ[ℂ] (Fin τ.dim → ℂ))) → ℂ))).comp
      (_root_.Representation.linHom σ.toRepresentation τ.toRepresentation)
  continuous_action := by
    let e := compactHomModelEquiv K n σ τ
    let L : Matrix (Fin τ.dim) (Fin σ.dim) ℂ →ₗ[ℂ]
        (Fin (Module.finrank ℂ ((Fin σ.dim → ℂ) →ₗ[ℂ] (Fin τ.dim → ℂ))) → ℂ) :=
      e.symm.toLinearMap.comp LinearMap.toMatrix'.symm.toLinearMap
    let R :
        (Fin (Module.finrank ℂ ((Fin σ.dim → ℂ) →ₗ[ℂ] (Fin τ.dim → ℂ))) → ℂ) →ₗ[ℂ]
          Matrix (Fin τ.dim) (Fin σ.dim) ℂ :=
      LinearMap.toMatrix'.toLinearMap.comp e.toLinearMap
    have hmat : Continuous fun p : standardInfiniteCompact K n ×
        (Fin (Module.finrank ℂ ((Fin σ.dim → ℂ) →ₗ[ℂ] (Fin τ.dim → ℂ))) → ℂ) =>
        LinearMap.toMatrix' (τ.toRepresentation p.1) * R p.2 *
          LinearMap.toMatrix' (σ.toRepresentation p.1⁻¹) :=
      ((τ.continuous_toMatrix'.comp continuous_fst).matrix_mul
        (R.continuous_of_finiteDimensional.comp continuous_snd)).matrix_mul
          (σ.continuous_toMatrix'.comp (continuous_inv.comp continuous_fst))
    convert L.continuous_of_finiteDimensional.comp hmat using 1
    funext p
    change e.symm
      (τ.toRepresentation p.1 ∘ₗ e p.2 ∘ₗ σ.toRepresentation p.1⁻¹) = L _
    change e.symm _ = e.symm (LinearMap.toMatrix'.symm _)
    congr 1
    apply LinearMap.toMatrix'.injective
    simp only [LinearMap.toMatrix'_comp, LinearEquiv.apply_symm_apply, R,
      LinearMap.comp_apply, LinearEquiv.coe_toLinearMap, Matrix.mul_assoc]

omit [NumberField K] in
@[simp]
theorem compactHomModelEquiv_action (σ τ : ContinuousCompactRep K n)
    (k : standardInfiniteCompact K n) (v : Fin (σ.linHom K n τ).dim → ℂ) :
    compactHomModelEquiv K n σ τ ((σ.linHom K n τ).toRepresentation k v) =
      _root_.Representation.linHom σ.toRepresentation τ.toRepresentation k
        (compactHomModelEquiv K n σ τ v) := by
  change (compactHomModelEquiv K n σ τ)
    ((compactHomModelEquiv K n σ τ).symm _) = _
  exact (compactHomModelEquiv K n σ τ).apply_symm_apply _

section Target

variable {V : Type w} [AddCommGroup V] [Module ℂ V]

/-- Postcomposition with a compact source map, in the finite Hom model. -/
def compactHomSourceMap (σ τ : ContinuousCompactRep K n)
    (j : (Fin τ.dim → ℂ) →ₗ[ℂ] V) :
    (Fin (σ.linHom K n τ).dim → ℂ) →ₗ[ℂ] ((Fin σ.dim → ℂ) →ₗ[ℂ] V) where
  toFun v := j.comp (compactHomModelEquiv K n σ τ v)
  map_add' v w :=
    (congrArg (fun F : (Fin σ.dim → ℂ) →ₗ[ℂ] (Fin τ.dim → ℂ) => j.comp F)
      ((compactHomModelEquiv K n σ τ).map_add v w)).trans (LinearMap.comp_add _ _ _)
  map_smul' c v :=
    (congrArg (fun F : (Fin σ.dim → ℂ) →ₗ[ℂ] (Fin τ.dim → ℂ) => j.comp F)
      ((compactHomModelEquiv K n σ τ).map_smul c v)).trans (LinearMap.comp_smul _ _ _)

omit [NumberField K] in
@[simp]
theorem compactHomSourceMap_apply (σ τ : ContinuousCompactRep K n)
    (j : (Fin τ.dim → ℂ) →ₗ[ℂ] V) (v : Fin (σ.linHom K n τ).dim → ℂ)
    (x : Fin σ.dim → ℂ) :
    compactHomSourceMap K n σ τ j v x = j (compactHomModelEquiv K n σ τ v x) := rfl

omit [NumberField K] in
/-- A map lies in the finite Hom source image exactly when all its values lie
in the original source image. No injectivity of that source map is required. -/
theorem mem_range_compactHomSourceMap_iff (σ τ : ContinuousCompactRep K n)
    (j : (Fin τ.dim → ℂ) →ₗ[ℂ] V) (F : (Fin σ.dim → ℂ) →ₗ[ℂ] V) :
    F ∈ LinearMap.range (compactHomSourceMap K n σ τ j) ↔
      ∀ x, F x ∈ LinearMap.range j := by
  classical
  constructor
  · rintro ⟨v, rfl⟩ x
    exact LinearMap.mem_range_self j _
  · intro hF
    let b := Pi.basisFun ℂ (Fin σ.dim)
    choose v hv using fun i => hF (b i)
    let F' : (Fin σ.dim → ℂ) →ₗ[ℂ] (Fin τ.dim → ℂ) := b.constr ℂ v
    refine ⟨(compactHomModelEquiv K n σ τ).symm F', ?_⟩
    change j.comp (compactHomModelEquiv K n σ τ
      ((compactHomModelEquiv K n σ τ).symm F')) = F
    rw [LinearEquiv.apply_symm_apply]
    apply b.ext
    intro i
    simpa only [LinearMap.comp_apply, F', b.constr_basis] using hv i

omit [NumberField K] in
/-- The finite Hom source map intertwines the two conjugation actions. -/
theorem compactHomSourceMap_equivariant (σ τ : ContinuousCompactRep K n)
    (j : (Fin τ.dim → ℂ) →ₗ[ℂ] V)
    (ρ : _root_.Representation ℂ (standardInfiniteCompact K n) V)
    (hj : ∀ k v, j (τ.toRepresentation k v) = ρ k (j v))
    (k : standardInfiniteCompact K n) (v : Fin (σ.linHom K n τ).dim → ℂ) :
    compactHomSourceMap K n σ τ j ((σ.linHom K n τ).toRepresentation k v) =
      _root_.Representation.linHom σ.toRepresentation ρ k
        (compactHomSourceMap K n σ τ j v) := by
  ext x
  simp only [compactHomSourceMap_apply, compactHomModelEquiv_action,
    _root_.Representation.linHom_apply, LinearMap.comp_apply, hj]

variable [Module (EnvelopingAlgebra K n) V] [IsScalarTower ℂ (EnvelopingAlgebra K n) V]

omit [NumberField K] in
/-- Pointwise enveloping action and the Hom compact action satisfy the same
actual conjugation law as the original compatible actions. -/
theorem compactHomAction_enveloping_compatible (σ : ContinuousCompactRep K n)
    (ρ : _root_.Representation ℂ (standardInfiniteCompact K n) V)
    (hρ : ∀ k a v, ρ k (a • v) = envelopingConjugation K n k.val a • ρ k v)
    (k : standardInfiniteCompact K n) (a : EnvelopingAlgebra K n)
    (F : (Fin σ.dim → ℂ) →ₗ[ℂ] V) :
    _root_.Representation.linHom σ.toRepresentation ρ k (a • F) =
      envelopingConjugation K n k.val a •
        _root_.Representation.linHom σ.toRepresentation ρ k F := by
  ext x
  simp only [_root_.Representation.linHom_apply, LinearMap.comp_apply,
    LinearMap.smul_apply, hρ]

omit [NumberField K] in
/-- Compact-generator stability passes from the original source image to the
finite Hom source image. -/
theorem compactHomSourceMap_range_stable (σ τ : ContinuousCompactRep K n)
    (j : (Fin τ.dim → ℂ) →ₗ[ℂ] V)
    (hstable : ∀ X : CompactComplexLieAlgebra K n, ∀ v ∈ LinearMap.range j,
      compactEnvelopingGenerator K n X • v ∈ LinearMap.range j)
    (X : CompactComplexLieAlgebra K n)
    (F : (Fin σ.dim → ℂ) →ₗ[ℂ] V)
    (hF : F ∈ LinearMap.range (compactHomSourceMap K n σ τ j)) :
    compactEnvelopingGenerator K n X • F ∈
      LinearMap.range (compactHomSourceMap K n σ τ j) := by
  apply (mem_range_compactHomSourceMap_iff K n σ τ j _).mpr
  intro x
  exact hstable X (F x) ((mem_range_compactHomSourceMap_iff K n σ τ j F).mp hF x)

end Target

end Langlands.Global.ArchimedeanGL
