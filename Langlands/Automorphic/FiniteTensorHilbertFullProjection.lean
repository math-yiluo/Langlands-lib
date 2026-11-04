import Langlands.Automorphic.FiniteTensorHilbertHeckeProjection

/-! # Joint Hecke projections defined on entire completed tensor slices -/

noncomputable section
open scoped Classical TensorProduct
universe uF uV uI
set_option autoImplicit false
set_option maxHeartbeats 40000

namespace Langlands.TensorHilbertHeckeAux

universe uH uG

section AmbientProjection

variable {ι : Type uI}
variable {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable (K : Submodule ℂ H)
variable (T : ι → K →L[ℂ] K) (c : ι → ℂ)

/-- The same joint eigenvectors, viewed as a submodule of the ambient space
through the inherited subtype inclusion. -/
def ambientJointEigenspace : Submodule ℂ H :=
  (jointEigenspace (fun i => (T i).toLinearMap) c).map K.subtype

theorem ambientJointEigenspace_le : ambientJointEigenspace K T c ≤ K := by
  rintro x ⟨y, _, rfl⟩
  exact y.property

theorem mem_ambientJointEigenspace_iff (x : H) :
    x ∈ ambientJointEigenspace K T c ↔
      ∃ y : K, (∀ i, T i y = c i • y) ∧ (y : H) = x := by
  simp only [ambientJointEigenspace, Submodule.mem_map, mem_jointEigenspace_iff,
    Submodule.subtype_apply]
  rfl

theorem ambientJointEigenspace_isClosed (hK : IsClosed (K : Set H)) :
    IsClosed (ambientJointEigenspace K T c : Set H) := by
  rw [ambientJointEigenspace, Submodule.map_coe]
  exact hK.isClosedMap_subtype_val _ (isClosed_jointEigenspace T c)

variable [CompleteSpace H] [CompleteSpace K]

local instance ambientJointEigenspaceComplete :
    CompleteSpace (ambientJointEigenspace K T c) :=
  (ambientJointEigenspace_isClosed K T c
    ((completeSpace_coe_iff_isComplete (s := (K : Set H))).mp inferInstance).isClosed).completeSpace_coe

/-- The actual orthogonal joint projection, defined on the entire ambient
space, rather than only on the closed subspace carrying the operators. -/
def ambientJointProjection : H →L[ℂ] H :=
  (ambientJointEigenspace K T c).starProjection

theorem ambientJointProjection_range :
    (ambientJointProjection K T c).range = ambientJointEigenspace K T c :=
  Submodule.range_starProjection _

theorem ambientJointProjection_eq_self_iff (x : H) :
    ambientJointProjection K T c x = x ↔
      ∃ y : K, (∀ i, T i y = c i • y) ∧ (y : H) = x :=
  Submodule.starProjection_eq_self_iff.trans (mem_ambientJointEigenspace_iff K T c x)

local instance ambientOriginalJointComplete :
    CompleteSpace (jointEigenspace (fun i => (T i).toLinearMap) c) :=
  (isClosed_jointEigenspace T c).completeSpace_coe

/-- Restriction to the original closed subspace gives exactly the previous
joint projection, with the same inherited vectors and norm. -/
theorem ambientJointProjection_subtype (x : K) :
    ambientJointProjection K T c (x : H) =
      (jointOrthogonalProjection T c x : H) := by
  let : (Submodule.map K.subtypeₗᵢ.toLinearMap
      (jointEigenspace (fun i => (T i).toLinearMap) c)).HasOrthogonalProjection :=
    (inferInstance : (ambientJointEigenspace K T c).HasOrthogonalProjection)
  exact (K.subtypeₗᵢ.map_starProjection
    (jointEigenspace (fun i => (T i).toLinearMap) c) x).symm

/-- On arbitrary ambient vectors, first project onto the closed subspace,
then apply the same joint projection there and include the result. -/
theorem ambientJointProjection_eq_comp :
    ambientJointProjection K T c =
      (K.subtypeL ∘L jointOrthogonalProjection T c) ∘L K.orthogonalProjectionOnto := by
  apply ContinuousLinearMap.ext
  intro x
  have h := DFunLike.congr_fun
    (Submodule.starProjection_comp_starProjection_of_le
      (ambientJointEigenspace_le K T c)) x
  exact h.symm.trans (ambientJointProjection_subtype K T c
    (K.orthogonalProjectionOnto x))

theorem ambientJointProjection_idempotent :
    IsIdempotentElem (ambientJointProjection K T c) :=
  (ambientJointEigenspace K T c).isIdempotentElem_starProjection

theorem ambientJointProjection_isSymmetric :
    (ambientJointProjection K T c).toLinearMap.IsSymmetric :=
  (ambientJointEigenspace K T c).starProjection_isSymmetric

theorem ambientJointProjection_norm_le : ‖ambientJointProjection K T c‖ ≤ 1 :=
  (ambientJointEigenspace K T c).starProjection_norm_le

theorem norm_ambientJointProjection_apply_le (x : H) :
    ‖ambientJointProjection K T c x‖ ≤ ‖x‖ :=
  (ambientJointEigenspace K T c).norm_starProjection_apply_le x

theorem ambientJointProjection_ker :
    (ambientJointProjection K T c).ker = (ambientJointEigenspace K T c)ᗮ :=
  Submodule.ker_starProjection _

theorem sub_ambientJointProjection_mem_orthogonal (x : H) :
    x - ambientJointProjection K T c x ∈ (ambientJointEigenspace K T c)ᗮ :=
  Submodule.sub_starProjection_mem_orthogonal
    (K := ambientJointEigenspace K T c) x

end AmbientProjection

section FullCornerProjection

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

/-- The original algebraic joint corner eigenspace, included in the entire
invariant subspace through the inherited fixed-vector inclusion. -/
def cornerFullJointEigenspace
    (f : ι → Hecke.HeckeAlgebra.Corner μ K hK) (c : ι → ℂ) :
    Submodule ℂ S.toSubmodule :=
  (cornerJointEigenspace τ S μ K hK f c).map
    (fixedVectors S.toRepresentation K.toSubgroup).subtype

/-- An endomorphism of the entire closed invariant subspace, projecting onto
its actual fixed joint eigenvectors for the unchanged corner action. -/
def cornerFullJointProjection
    (f : ι → Hecke.HeckeAlgebra.Corner μ K hK) (c : ι → ℂ) :
    S.toSubmodule →L[ℂ] S.toSubmodule := by
  letI : CompleteSpace S.toSubmodule := hS.completeSpace_coe
  letI : CompleteSpace (fixedVectors S.toRepresentation K.toSubgroup) :=
    fullFixed_completeSpace τ hτ S hS K.toSubgroup
  exact ambientJointProjection (fixedVectors S.toRepresentation K.toSubgroup)
    (fun i => cornerContinuousAction μ K hK τ S hτ (f i)) c

/-- The range retains exactly the original algebraic joint eigenvectors. -/
theorem cornerFullJointProjection_range
    (f : ι → Hecke.HeckeAlgebra.Corner μ K hK) (c : ι → ℂ) :
    (cornerFullJointProjection μ K hK τ S hS hτ f c).range =
      cornerFullJointEigenspace μ K hK τ S f c := by
  let : CompleteSpace S.toSubmodule := hS.completeSpace_coe
  let : CompleteSpace (fixedVectors S.toRepresentation K.toSubgroup) :=
    fullFixed_completeSpace τ hτ S hS K.toSubgroup
  dsimp only [cornerFullJointProjection]
  rw [ambientJointProjection_range]
  rfl

/-- Exact fixed-vector criterion in the entire invariant subspace. -/
theorem cornerFullJointProjection_eq_self_iff
    (f : ι → Hecke.HeckeAlgebra.Corner μ K hK) (c : ι → ℂ)
    (x : S.toSubmodule) :
    cornerFullJointProjection μ K hK τ S hS hτ f c x = x ↔
      ∃ z : fixedVectors S.toRepresentation K.toSubgroup,
        (∀ i, cornerAction τ S μ K hK (f i) z = c i • z) ∧
          (z : S.toSubmodule) = x := by
  let : CompleteSpace S.toSubmodule := hS.completeSpace_coe
  let : CompleteSpace (fixedVectors S.toRepresentation K.toSubgroup) :=
    fullFixed_completeSpace τ hτ S hS K.toSubgroup
  dsimp only [cornerFullJointProjection]
  rw [ambientJointProjection_eq_self_iff]
  rfl

/-- Restriction to all subgroup-fixed vectors gives exactly the existing
corner projection; no change of vectors or norm is made. -/
theorem cornerFullJointProjection_subtype
    (f : ι → Hecke.HeckeAlgebra.Corner μ K hK) (c : ι → ℂ)
    (x : fixedVectors S.toRepresentation K.toSubgroup) :
    cornerFullJointProjection μ K hK τ S hS hτ f c (x : S.toSubmodule) =
      (cornerJointOrthogonalProjection μ K hK τ S hS hτ f c x : S.toSubmodule) := by
  let : CompleteSpace S.toSubmodule := hS.completeSpace_coe
  let : CompleteSpace (fixedVectors S.toRepresentation K.toSubgroup) :=
    fullFixed_completeSpace τ hτ S hS K.toSubgroup
  dsimp only [cornerFullJointProjection, cornerJointOrthogonalProjection]
  exact ambientJointProjection_subtype _ _ c x

theorem cornerFullJointProjection_idempotent
    (f : ι → Hecke.HeckeAlgebra.Corner μ K hK) (c : ι → ℂ) :
    IsIdempotentElem (cornerFullJointProjection μ K hK τ S hS hτ f c) := by
  let : CompleteSpace S.toSubmodule := hS.completeSpace_coe
  let : CompleteSpace (fixedVectors S.toRepresentation K.toSubgroup) :=
    fullFixed_completeSpace τ hτ S hS K.toSubgroup
  dsimp only [cornerFullJointProjection]
  exact ambientJointProjection_idempotent _ _ c

theorem cornerFullJointProjection_norm_le
    (f : ι → Hecke.HeckeAlgebra.Corner μ K hK) (c : ι → ℂ) :
    ‖cornerFullJointProjection μ K hK τ S hS hτ f c‖ ≤ 1 := by
  let : CompleteSpace S.toSubmodule := hS.completeSpace_coe
  let : CompleteSpace (fixedVectors S.toRepresentation K.toSubgroup) :=
    fullFixed_completeSpace τ hτ S hS K.toSubgroup
  dsimp only [cornerFullJointProjection]
  exact ambientJointProjection_norm_le _ _ c

end FullCornerProjection
end Langlands.TensorHilbertHeckeAux

namespace Langlands.Automorphic

open MeasureTheory
open Langlands.Global Langlands.Global.FiniteAdelicGL Langlands.RestrictedTensor

variable {F : Type uF} [Field F] [NumberField F] {n : ℕ}
variable {V : FinitePlace F → Type uV}
variable [∀ v, AddCommGroup (V v)] [∀ v, Module ℂ (V v)]
variable {ι : Type uI}

local instance tensorHilbertFullProjectionRationalGroup :
    AddCommGroup (RationalInvariantFunctions F n) := Submodule.addCommGroup _
local instance tensorHilbertFullProjectionContinuousGroup :
    AddCommGroup (ContinuousRationalFunctions F n) := Submodule.addCommGroup _
local instance tensorHilbertFullProjectionSmoothGroup :
    AddCommGroup (FiniteSmoothRationalFunctions F n) := Submodule.addCommGroup _
local instance tensorHilbertFullProjectionFormsGroup :
    AddCommGroup (AutomorphicForms F n) := Submodule.addCommGroup _
local instance tensorHilbertFullProjectionFiniteSpaceGroup (S : FiniteRealization F n) :
    AddCommGroup S.Space := Submodule.addCommGroup _
local instance tensorHilbertFullProjectionLocalSpaceGroup (v : FinitePlace F)
    (L : LocalRealization F n v) : AddCommGroup L.Space := Submodule.addCommGroup _
local instance tensorHilbertFullProjectionMeasurable (v : FinitePlace F) :
    MeasurableSpace (FiniteLocalGL F n v) := borel _
local instance tensorHilbertFullProjectionBorel (v : FinitePlace F) :
    BorelSpace (FiniteLocalGL F n v) := ⟨rfl⟩

namespace FiniteTensorPresentation

variable {ρ : ∀ v, Representation ℂ (FiniteLocalGL F n v) (V v)}
variable {E : Finset (FinitePlace F)} {e : ∀ v, V v}
variable {he : ∀ v ∉ E, ∀ g ∈ localIntegral F n v, ρ v g (e v) = e v}
variable {S : FiniteRealization F n} (P : FiniteTensorPresentation F n ρ E e he S)
variable (b : Langlands.InvariantPositiveForm S.representation)

/-- The actual orthogonal joint corner projection on the entire completed
slice, with its inherited global Hilbert norm. Zero tails are allowed. -/
def sliceHilbertFullJointCornerProjection (v : FinitePlace F)
    (y : LocalTensorTail (K := ℂ) F E v e)
    (μ : Measure (FiniteLocalGL F n v)) [μ.IsHaarMeasure]
    (K : OpenSubgroup (FiniteLocalGL F n v))
    (hK : IsCompact (K : Set (FiniteLocalGL F n v)))
    (f : ι → Hecke.HeckeAlgebra.Corner μ K hK) (c : ι → ℂ) :=
  TensorHilbertHeckeAux.cornerFullJointProjection μ K hK
    _
    (P.sliceHilbertRange b v y) (P.isClosed_sliceHilbertRange b v y)
    (fun g x => b.completedRepresentation_norm (localInclusion F n v g) x) f c

end FiniteTensorPresentation
end Langlands.Automorphic
