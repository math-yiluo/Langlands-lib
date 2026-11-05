import Langlands.Automorphic.FiniteTensorHilbertSpherical
import Langlands.Automorphic.FiniteTensorHilbertHeckeProjection
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! # The closed joint spectral subspace of actual completed tensor slices -/

noncomputable section
open scoped Classical TensorProduct
universe uF uV uI
set_option autoImplicit false
set_option maxHeartbeats 40000

namespace Langlands.TensorHilbertHeckeAux

universe uH uJ

variable {ι : Type uI}
variable {H : Type uH} [NormedAddCommGroup H] [NormedSpace ℂ H]
variable {J : Type uJ} [NormedAddCommGroup J] [NormedSpace ℂ J]

/-- The closure of the span of all original ordinary joint eigenvectors.
It is not assumed to be the entire carrier. -/
def jointSpectralClosure (T : ι → H →L[ℂ] H) : Submodule ℂ H :=
  (⨆ c, jointEigenspace (fun i => (T i).toLinearMap) c).topologicalClosure

theorem jointSpectralClosure_isClosed (T : ι → H →L[ℂ] H) :
    IsClosed (jointSpectralClosure T : Set H) :=
  Submodule.isClosed_topologicalClosure _

theorem jointEigenspace_le_jointSpectralClosure (T : ι → H →L[ℂ] H) (c : ι → ℂ) :
    jointEigenspace (fun i => (T i).toLinearMap) c ≤ jointSpectralClosure T :=
  (le_iSup (jointEigenspace (fun i => (T i).toLinearMap)) c).trans
    (Submodule.le_topologicalClosure _)

/-- Each original bounded operator preserves the closed spectral subspace. -/
theorem jointSpectralClosure_map_le (T : ι → H →L[ℂ] H) (j : ι) :
    (jointSpectralClosure T).map (T j).toLinearMap ≤ jointSpectralClosure T := by
  refine (Submodule.topologicalClosure_map (T j) _).trans
    (Submodule.topologicalClosure_mono ?_)
  rw [Submodule.map_iSup]
  refine iSup_le fun c => ?_
  rintro _ ⟨x, hx, rfl⟩
  rw [(mem_jointEigenspace_iff _ c x).mp hx j]
  exact (⨆ a, jointEigenspace (fun i => (T i).toLinearMap) a).smul_mem _
    ((le_iSup (jointEigenspace (fun i => (T i).toLinearMap)) c) hx)

/-- Restrict the original operator with the inherited subspace norm. -/
def jointSpectralClosureAction (T : ι → H →L[ℂ] H) (i : ι) :
    jointSpectralClosure T →L[ℂ] jointSpectralClosure T :=
  (T i).restrict (fun _ hx =>
    jointSpectralClosure_map_le T i (Submodule.mem_map_of_mem hx))

theorem jointSpectralClosureAction_apply_val (T : ι → H →L[ℂ] H) (i : ι)
    (x : jointSpectralClosure T) :
    (jointSpectralClosureAction T i x).val = T i x := rfl

/-- Every commutator vanishes on the closed spectral subspace, even if it
does not vanish on the ambient space. -/
theorem jointSpectralClosure_le_commutator_ker (T : ι → H →L[ℂ] H) (i j : ι) :
    jointSpectralClosure T ≤ ((T i).comp (T j) - (T j).comp (T i)).ker := by
  apply Submodule.topologicalClosure_minimal
  · refine iSup_le fun c => ?_
    intro x hx
    have he : ∀ k, T k x = c k • x :=
      (mem_jointEigenspace_iff (fun k => (T k).toLinearMap) c x).mp hx
    change T i (T j x) - T j (T i x) = 0
    rw [he j, he i, map_smul, map_smul, he i, he j, smul_smul, smul_smul,
      mul_comm (c j) (c i), sub_self]
  · exact ContinuousLinearMap.isClosed_ker _

/-- On the actual closed joint-eigenvector span the original restrictions
commute, with no commutation premise on the original family. -/
theorem jointSpectralClosureAction_commute (T : ι → H →L[ℂ] H) (i j : ι) :
    Commute (jointSpectralClosureAction T i) (jointSpectralClosureAction T j) := by
  apply ContinuousLinearMap.ext
  intro x
  apply Subtype.ext
  exact sub_eq_zero.mp (jointSpectralClosure_le_commutator_ker T i j x.property)

/-- A genuine continuous intertwining equivalence maps precisely the closed
joint spectral subspace onto the corresponding one. -/
theorem jointSpectralClosure_map_equiv (e : H ≃L[ℂ] J)
    (T : ι → H →L[ℂ] H) (U : ι → J →L[ℂ] J)
    (h : ∀ i x, e (T i x) = U i (e x)) :
    (jointSpectralClosure T).map e.toLinearMap = jointSpectralClosure U := by
  have hsum : (⨆ c, jointEigenspace (fun i => (T i).toLinearMap) c).map
      e.toLinearMap = ⨆ c, jointEigenspace (fun i => (U i).toLinearMap) c := by
    rw [Submodule.map_iSup]
    apply iSup_congr
    intro c
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact (mem_jointEigenspace_equiv_iff e.toLinearEquiv _ _ c h x).mpr hx
    · intro hy
      refine ⟨e.symm y, ?_, e.apply_symm_apply y⟩
      exact (mem_jointEigenspace_equiv_iff e.toLinearEquiv _ _ c h (e.symm y)).mp
        (by
          change e (e.symm y) ∈ _
          simpa only [e.apply_symm_apply] using hy)
  apply SetLike.ext'
  change e '' closure _ = closure _
  rw [e.image_closure]
  exact congrArg (fun s : Submodule ℂ J => closure (s : Set J)) hsum

/-- Transport uses the same original equivalence and inherited norms. -/
def jointSpectralClosureTransport (e : H ≃L[ℂ] J)
    (T : ι → H →L[ℂ] H) (U : ι → J →L[ℂ] J)
    (h : ∀ i x, e (T i x) = U i (e x)) :
    jointSpectralClosure T ≃L[ℂ] jointSpectralClosure U :=
  e.ofSubmodules _ _ (jointSpectralClosure_map_equiv e T U h)

theorem jointSpectralClosureTransport_apply_val (e : H ≃L[ℂ] J)
    (T : ι → H →L[ℂ] H) (U : ι → J →L[ℂ] J)
    (h : ∀ i x, e (T i x) = U i (e x)) (x : jointSpectralClosure T) :
    (jointSpectralClosureTransport e T U h x).val = e x := rfl

/-- In finite dimension the algebraic span is already closed. This does not
assert that it is the whole carrier. -/
theorem jointSpectralClosure_eq_iSup [FiniteDimensional ℂ H]
    (T : ι → H →L[ℂ] H) :
      jointSpectralClosure T = ⨆ c, jointEigenspace (fun i => (T i).toLinearMap) c :=
  (Submodule.closed_of_finiteDimensional
    (⨆ c, jointEigenspace (fun i => (T i).toLinearMap) c)).submodule_topologicalClosure_eq

/-- Density of the actual algebraic eigenvector span is exactly the remaining
top-subspace obligation. -/
theorem jointSpectralClosure_eq_top_iff (T : ι → H →L[ℂ] H) :
    jointSpectralClosure T = ⊤ ↔
      Dense (((⨆ c, jointEigenspace (fun i => (T i).toLinearMap) c) :
        Submodule ℂ H) : Set H) :=
  Submodule.dense_iff_topologicalClosure_eq_top.symm

section Projection

variable {X : Type uH} [NormedAddCommGroup X] [InnerProductSpace ℂ X]
variable [CompleteSpace X]

local instance jointSpectralClosureComplete (T : ι → X →L[ℂ] X) :
    CompleteSpace (jointSpectralClosure T) :=
  (jointSpectralClosure_isClosed T).completeSpace_coe

/-- The orthogonal projection onto the closed span of actual common
eigenvectors, defined on the entire original Hilbert space. -/
def jointSpectralClosureProjection (T : ι → X →L[ℂ] X) : X →L[ℂ] X :=
  (jointSpectralClosure T).starProjection

theorem jointSpectralClosureProjection_range (T : ι → X →L[ℂ] X) :
    (jointSpectralClosureProjection T).range = jointSpectralClosure T :=
  Submodule.range_starProjection _

theorem jointSpectralClosureProjection_ker (T : ι → X →L[ℂ] X) :
    (jointSpectralClosureProjection T).ker = (jointSpectralClosure T)ᗮ :=
  Submodule.ker_starProjection _

theorem jointSpectralClosureProjection_eq_self_iff (T : ι → X →L[ℂ] X) (x : X) :
    jointSpectralClosureProjection T x = x ↔ x ∈ jointSpectralClosure T :=
  Submodule.starProjection_eq_self_iff

theorem jointSpectralClosureProjection_idempotent (T : ι → X →L[ℂ] X) :
    IsIdempotentElem (jointSpectralClosureProjection T) :=
  (jointSpectralClosure T).isIdempotentElem_starProjection

theorem jointSpectralClosureProjection_isSymmetric (T : ι → X →L[ℂ] X) :
    (jointSpectralClosureProjection T).toLinearMap.IsSymmetric :=
  (jointSpectralClosure T).starProjection_isSymmetric

theorem jointSpectralClosureProjection_norm_le (T : ι → X →L[ℂ] X) :
    ‖jointSpectralClosureProjection T‖ ≤ 1 :=
  (jointSpectralClosure T).starProjection_norm_le

theorem sub_jointSpectralClosureProjection_mem_orthogonal
    (T : ι → X →L[ℂ] X) (x : X) :
    x - jointSpectralClosureProjection T x ∈ (jointSpectralClosure T)ᗮ :=
  Submodule.sub_starProjection_mem_orthogonal (K := jointSpectralClosure T) x

/-- The spectral projection is the identity exactly when the actual
eigenvector span is dense. No density theorem is assumed. -/
theorem jointSpectralClosureProjection_eq_id_iff (T : ι → X →L[ℂ] X) :
    jointSpectralClosureProjection T = ContinuousLinearMap.id ℂ X ↔
      jointSpectralClosure T = ⊤ := by
  constructor
  · intro hp
    rw [← jointSpectralClosureProjection_range T, hp]
    exact LinearMap.range_id
  · intro htop
    apply ContinuousLinearMap.ext
    intro x
    exact (jointSpectralClosureProjection_eq_self_iff T x).mpr (by rw [htop]; trivial)

end Projection
end Langlands.TensorHilbertHeckeAux

namespace Langlands.Automorphic

open Langlands.Global Langlands.Global.FiniteAdelicGL Langlands.RestrictedTensor

variable {F : Type uF} [Field F] [NumberField F] {r : ℕ}
variable {V : FinitePlace F → Type uV}
variable [∀ v, AddCommGroup (V v)] [∀ v, Module ℂ (V v)]

local instance spectralClosureRationalGroup :
    AddCommGroup (RationalInvariantFunctions F (r + 1)) := Submodule.addCommGroup _
local instance spectralClosureContinuousGroup :
    AddCommGroup (ContinuousRationalFunctions F (r + 1)) := Submodule.addCommGroup _
local instance spectralClosureSmoothGroup :
    AddCommGroup (FiniteSmoothRationalFunctions F (r + 1)) := Submodule.addCommGroup _
local instance spectralClosureFormsGroup :
    AddCommGroup (AutomorphicForms F (r + 1)) := Submodule.addCommGroup _
local instance spectralClosureFiniteSpaceGroup (S : FiniteRealization F (r + 1)) :
    AddCommGroup S.Space := Submodule.addCommGroup _
local instance spectralClosureLocalSpaceGroup (v : FinitePlace F)
    (L : LocalRealization F (r + 1) v) : AddCommGroup L.Space := Submodule.addCommGroup _

namespace FiniteTensorPresentation

variable {ρ : ∀ v, Representation ℂ (FiniteLocalGL F (r + 1) v) (V v)}
variable {E : Finset (FinitePlace F)} {e : ∀ v, V v}
variable {he : ∀ v ∉ E, ∀ g ∈ localIntegral F (r + 1) v, ρ v g (e v) = e v}
variable {S : FiniteRealization F (r + 1)}
variable (P : FiniteTensorPresentation F (r + 1) ρ E e he S)
variable (b : Langlands.InvariantPositiveForm S.representation)

/-- The closed span of all ordinary common eigenvectors of the unchanged
standard spherical operators on the actual completed slice. -/
def hilbertSphericalSpectralClosure (v : FinitePlace F)
    (y : LocalTensorTail (K := ℂ) F E v e) :
    Submodule ℂ (P.SliceHilbertSphericalVectors b v y) :=
  TensorHilbertHeckeAux.jointSpectralClosure
    (H := P.SliceHilbertSphericalVectors b v y)
    (P.sliceHilbertStandardContinuousHeckeOperator b v y)

/-- The original bounded standard operator restricted to the actual closed
spectral subspace, with its inherited global Hilbert norm. -/
def hilbertSphericalSpectralClosureAction (v : FinitePlace F)
    (y : LocalTensorTail (K := ℂ) F E v e) (i : Fin (r + 2)) :=
  @TensorHilbertHeckeAux.jointSpectralClosureAction
    (Fin (r + 2)) (P.SliceHilbertSphericalVectors b v y) inferInstance inferInstance
    (P.sliceHilbertStandardContinuousHeckeOperator b v y) i

local instance spectralClosureSphericalComplete (v : FinitePlace F)
    (y : LocalTensorTail (K := ℂ) F E v e) :
    CompleteSpace (P.SliceHilbertSphericalVectors b v y) :=
  TensorHilbertHeckeAux.fullFixed_completeSpace
    (b.completedRepresentation.comp (localInclusion F (r + 1) v).toMonoidHom)
    (fun g x => b.completedRepresentation_norm (localInclusion F (r + 1) v g) x)
    (P.sliceHilbertRange b v y) (P.isClosed_sliceHilbertRange b v y)
    (Correspondence.sphericalSubgroup (CompletionPadic.padicField v) r)

/-- Orthogonal projection from the entire spherical fixed space onto its
actual closed joint-eigenvector span. Zero tails are allowed. -/
def hilbertSphericalSpectralClosureProjection (v : FinitePlace F)
    (y : LocalTensorTail (K := ℂ) F E v e) :
    P.SliceHilbertSphericalVectors b v y →L[ℂ] P.SliceHilbertSphericalVectors b v y :=
  TensorHilbertHeckeAux.jointSpectralClosureProjection
    (X := P.SliceHilbertSphericalVectors b v y)
    (P.sliceHilbertStandardContinuousHeckeOperator b v y)

end FiniteTensorPresentation
end Langlands.Automorphic
