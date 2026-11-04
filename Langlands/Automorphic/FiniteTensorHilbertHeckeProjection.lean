import Langlands.Automorphic.FiniteTensorHilbertHeckeEigenspace
import Mathlib.Analysis.InnerProductSpace.Projection.Basic

/-! # Orthogonal joint Hecke projections on full completed tensor slices -/

noncomputable section
open scoped Classical TensorProduct
universe uF uV uI
set_option autoImplicit false
set_option maxHeartbeats 40000

namespace Langlands.TensorHilbertHeckeAux

universe uG uH

section FixedCompleteness

variable {G : Type uG} [Group G]
variable {H : Type uH} [NormedAddCommGroup H] [NormedSpace ℂ H]
variable (τ : Representation ℂ G H)
variable (hτ : ∀ (g : G) (x : H), ‖τ g x‖ = ‖x‖)

include hτ in
/-- Norm-preserving group operators have a closed common fixed subspace.
No topology or continuity in the group variable is required. -/
theorem fixedVectors_isClosed (K : Subgroup G) :
    IsClosed (fixedVectors τ K : Set H) := by
  have heq : (fixedVectors τ K : Set H) = ⋂ g : K, {x : H | τ (g : G) x = x} := by
    ext x
    simp only [Set.mem_iInter, Set.mem_ofPred_eq]
    rfl
  rw [heq]
  apply isClosed_iInter
  intro g
  let T : H →L[ℂ] H := (τ (g : G)).mkContinuous 1
    (fun x => by simpa only [one_mul] using (hτ g x).le)
  exact isClosed_eq T.continuous continuous_id

include hτ in
/-- Closed invariant subspaces of a complete ambient space have complete
full subgroup-fixed spaces, with their inherited ambient norms. -/
theorem fullFixed_completeSpace [CompleteSpace H] (S : Subrepresentation τ)
    (hS : IsClosed (S : Set H)) (K : Subgroup G) :
    CompleteSpace (fixedVectors S.toRepresentation K) := by
  let : CompleteSpace S.toSubmodule := hS.completeSpace_coe
  exact (fixedVectors_isClosed S.toRepresentation
    (fun g x => hτ g x.val) K).completeSpace_coe

end FixedCompleteness

section JointProjection

variable {ι : Type uI}
variable {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable [CompleteSpace H]
variable (T : ι → H →L[ℂ] H) (c : ι → ℂ)

local instance jointEigenspaceComplete :
    CompleteSpace (jointEigenspace (fun i => (T i).toLinearMap) c) :=
  (isClosed_jointEigenspace T c).completeSpace_coe

/-- The actual orthogonal projection onto the closed ordinary joint eigenspace
of the specified bounded operators. The joint eigenspace may be zero. -/
def jointOrthogonalProjection : H →L[ℂ] H :=
  (jointEigenspace (fun i => (T i).toLinearMap) c).starProjection

/-- The projected vector satisfies every original eigen-equation. -/
theorem jointOrthogonalProjection_equation (i : ι) (x : H) :
    T i (jointOrthogonalProjection T c x) =
      c i • jointOrthogonalProjection T c x :=
  (mem_jointEigenspace_iff _ c _).mp
    ((jointEigenspace (fun i => (T i).toLinearMap) c).starProjection_apply_mem x) i

theorem jointOrthogonalProjection_eq_self_iff (x : H) :
    jointOrthogonalProjection T c x = x ↔ ∀ i, T i x = c i • x :=
  (Submodule.starProjection_eq_self_iff).trans (mem_jointEigenspace_iff _ c x)

theorem jointOrthogonalProjection_idempotent :
    IsIdempotentElem (jointOrthogonalProjection T c) :=
  (jointEigenspace (fun i => (T i).toLinearMap) c).isIdempotentElem_starProjection

theorem jointOrthogonalProjection_isSymmetric :
    (jointOrthogonalProjection T c).toLinearMap.IsSymmetric :=
  (jointEigenspace (fun i => (T i).toLinearMap) c).starProjection_isSymmetric

theorem jointOrthogonalProjection_norm_le :
    ‖jointOrthogonalProjection T c‖ ≤ 1 :=
  (jointEigenspace (fun i => (T i).toLinearMap) c).starProjection_norm_le

theorem norm_jointOrthogonalProjection_apply_le (x : H) :
    ‖jointOrthogonalProjection T c x‖ ≤ ‖x‖ :=
  (jointEigenspace (fun i => (T i).toLinearMap) c).norm_starProjection_apply_le x

theorem jointOrthogonalProjection_range :
    (jointOrthogonalProjection T c).range =
      jointEigenspace (fun i => (T i).toLinearMap) c :=
  Submodule.range_starProjection _

theorem jointOrthogonalProjection_ker :
    (jointOrthogonalProjection T c).ker =
      (jointEigenspace (fun i => (T i).toLinearMap) c)ᗮ :=
  Submodule.ker_starProjection _

/-- The discarded residual is perpendicular to all specified joint eigenvectors. -/
theorem sub_jointOrthogonalProjection_mem_orthogonal (x : H) :
    x - jointOrthogonalProjection T c x ∈
      (jointEigenspace (fun i => (T i).toLinearMap) c)ᗮ :=
  Submodule.sub_starProjection_mem_orthogonal
    (K := jointEigenspace (fun i => (T i).toLinearMap) c) x

end JointProjection

section CornerProjection

open MeasureTheory

variable {ι : Type uI}
variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable [MeasurableSpace G] [BorelSpace G]
variable {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable [CompleteSpace H]
variable (μ : Measure G) [μ.IsHaarMeasure]
variable (K : OpenSubgroup G) (hK : IsCompact (K : Set G))
variable (τ : Representation ℂ G H) (S : Subrepresentation τ)
variable (hS : IsClosed (S : Set H))
variable (hτ : ∀ (g : G) (x : H), ‖τ g x‖ = ‖x‖)

/-- Orthogonal projection on the entire fixed space of the closed invariant
subspace, using exactly the existing bounded corner operators. -/
def cornerJointOrthogonalProjection
    (f : ι → Hecke.HeckeAlgebra.Corner μ K hK) (c : ι → ℂ) :
    fixedVectors S.toRepresentation K.toSubgroup →L[ℂ]
      fixedVectors S.toRepresentation K.toSubgroup := by
  letI : CompleteSpace (fixedVectors S.toRepresentation K.toSubgroup) :=
    fullFixed_completeSpace τ hτ S hS K.toSubgroup
  exact jointOrthogonalProjection
    (H := fixedVectors S.toRepresentation K.toSubgroup)
    (fun i => cornerContinuousAction μ K hK τ S hτ (f i)) c

/-- Its range is the original algebraic corner joint eigenspace. -/
theorem cornerJointOrthogonalProjection_range
    (f : ι → Hecke.HeckeAlgebra.Corner μ K hK) (c : ι → ℂ) :
    (cornerJointOrthogonalProjection μ K hK τ S hS hτ f c).range =
      cornerJointEigenspace τ S μ K hK f c := by
  let : CompleteSpace (fixedVectors S.toRepresentation K.toSubgroup) :=
    fullFixed_completeSpace τ hτ S hS K.toSubgroup
  dsimp only [cornerJointOrthogonalProjection]
  rw [jointOrthogonalProjection_range]
  exact (cornerJointEigenspace_eq_continuous μ K hK τ S hτ f c).symm

/-- The exact fixed-vector criterion uses the unchanged algebraic operators. -/
theorem cornerJointOrthogonalProjection_eq_self_iff
    (f : ι → Hecke.HeckeAlgebra.Corner μ K hK) (c : ι → ℂ)
    (x : fixedVectors S.toRepresentation K.toSubgroup) :
    cornerJointOrthogonalProjection μ K hK τ S hS hτ f c x = x ↔
      ∀ i, cornerAction τ S μ K hK (f i) x = c i • x := by
  let : CompleteSpace (fixedVectors S.toRepresentation K.toSubgroup) :=
    fullFixed_completeSpace τ hτ S hS K.toSubgroup
  dsimp only [cornerJointOrthogonalProjection]
  rw [jointOrthogonalProjection_eq_self_iff]
  rfl

end CornerProjection
end Langlands.TensorHilbertHeckeAux

namespace Langlands.Automorphic

open MeasureTheory
open Langlands.Global Langlands.Global.FiniteAdelicGL Langlands.RestrictedTensor

variable {F : Type uF} [Field F] [NumberField F] {n : ℕ}
variable {V : FinitePlace F → Type uV}
variable [∀ v, AddCommGroup (V v)] [∀ v, Module ℂ (V v)]
variable {ι : Type uI}

local instance tensorHilbertProjectionRationalGroup :
    AddCommGroup (RationalInvariantFunctions F n) := Submodule.addCommGroup _
local instance tensorHilbertProjectionContinuousGroup :
    AddCommGroup (ContinuousRationalFunctions F n) := Submodule.addCommGroup _
local instance tensorHilbertProjectionSmoothGroup :
    AddCommGroup (FiniteSmoothRationalFunctions F n) := Submodule.addCommGroup _
local instance tensorHilbertProjectionFormsGroup :
    AddCommGroup (AutomorphicForms F n) := Submodule.addCommGroup _
local instance tensorHilbertProjectionFiniteSpaceGroup (S : FiniteRealization F n) :
    AddCommGroup S.Space := Submodule.addCommGroup _
local instance tensorHilbertProjectionLocalSpaceGroup (v : FinitePlace F)
    (L : LocalRealization F n v) : AddCommGroup L.Space := Submodule.addCommGroup _
local instance tensorHilbertProjectionMeasurable (v : FinitePlace F) :
    MeasurableSpace (FiniteLocalGL F n v) := borel _
local instance tensorHilbertProjectionBorel (v : FinitePlace F) :
    BorelSpace (FiniteLocalGL F n v) := ⟨rfl⟩

namespace FiniteTensorPresentation

variable {ρ : ∀ v, Representation ℂ (FiniteLocalGL F n v) (V v)}
variable {E : Finset (FinitePlace F)} {e : ∀ v, V v}
variable {he : ∀ v ∉ E, ∀ g ∈ localIntegral F n v, ρ v g (e v) = e v}
variable {S : FiniteRealization F n} (P : FiniteTensorPresentation F n ρ E e he S)
variable (b : Langlands.InvariantPositiveForm S.representation)

/-- The actual orthogonal joint Hecke projection on all subgroup-fixed vectors
of the full closed slice in the supplied global Hilbert completion.
Zero complementary tensors are allowed. -/
def sliceHilbertJointCornerProjection (v : FinitePlace F)
    (y : LocalTensorTail (K := ℂ) F E v e)
    (μ : Measure (FiniteLocalGL F n v)) [μ.IsHaarMeasure]
    (K : OpenSubgroup (FiniteLocalGL F n v))
    (hK : IsCompact (K : Set (FiniteLocalGL F n v)))
    (f : ι → Hecke.HeckeAlgebra.Corner μ K hK) (c : ι → ℂ) :=
  TensorHilbertHeckeAux.cornerJointOrthogonalProjection μ K hK
    _
    (P.sliceHilbertRange b v y) (P.isClosed_sliceHilbertRange b v y)
    (fun g x => b.completedRepresentation_norm (localInclusion F n v g) x) f c

end FiniteTensorPresentation
end Langlands.Automorphic
