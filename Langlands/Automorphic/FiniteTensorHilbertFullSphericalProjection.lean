import Langlands.Automorphic.FiniteTensorHilbertFullProjection
import Langlands.Automorphic.FiniteTensorHilbertSphericalProjection

/-! # Canonical spherical projections on entire completed tensor slices -/

noncomputable section
open scoped Classical TensorProduct
universe uF uV uI
set_option autoImplicit false
set_option maxHeartbeats 40000

namespace Langlands.TensorHilbertHeckeAux

universe uG uH

section AmbientScalarCriterion

variable {ι : Type uI}
variable {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable (K : Submodule ℂ H)
variable (T : ι → K →L[ℂ] K) (c : ι → ℂ)

/-- The included ordinary joint eigenspace is the whole original submodule
exactly when all original operators have the prescribed scalar action. -/
theorem ambientJointEigenspace_eq_submodule_iff :
    ambientJointEigenspace K T c = K ↔ ∀ i x, T i x = c i • x := by
  constructor
  · intro h i x
    have hx : (x : H) ∈ ambientJointEigenspace K T c := by
      rw [h]
      exact x.property
    obtain ⟨y, hy, hyx⟩ := (mem_ambientJointEigenspace_iff K T c (x : H)).mp
      hx
    have heq : y = x := Subtype.ext hyx
    exact heq ▸ hy i
  · intro h
    apply le_antisymm (ambientJointEigenspace_le K T c)
    intro x hx
    exact (mem_ambientJointEigenspace_iff K T c x).mpr
      ⟨⟨x, hx⟩, fun i => h i ⟨x, hx⟩, rfl⟩

variable [CompleteSpace H] [CompleteSpace K]

/-- Equality with the original submodule projection characterizes scalar
action on that submodule, including when it is zero. -/
theorem ambientJointProjection_eq_starProjection_iff :
    ambientJointProjection K T c = K.starProjection ↔ ∀ i x, T i x = c i • x := by
  constructor
  · intro h
    have heq := congrArg (fun U : H →L[ℂ] H => U.range) h
    rw [ambientJointProjection_range, Submodule.range_starProjection] at heq
    exact (ambientJointEigenspace_eq_submodule_iff K T c).mp heq
  · intro h
    rw [ambientJointProjection_eq_comp,
      (jointOrthogonalProjection_eq_id_iff T c).mpr h]
    rfl

/-- Equality of projections does not by itself assert nontriviality of the
submodule carrying the scalar equations. -/
theorem hasScalarSpectrum_iff_ambientJointProjection :
    HasScalarSpectrum (fun i => (T i).toLinearMap) c ↔
      Nontrivial K ∧ ambientJointProjection K T c = K.starProjection :=
  and_congr Iff.rfl (ambientJointProjection_eq_starProjection_iff K T c).symm

end AmbientScalarCriterion

section FullFixedProjection

open MeasureTheory

variable {G : Type uG} [Group G]
variable {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable [CompleteSpace H]
variable (τ : Representation ℂ G H) (S : Subrepresentation τ)
variable (hS : IsClosed (S : Set H))
variable (hτ : ∀ (g : G) (x : H), ‖τ g x‖ = ‖x‖)

/-- Orthogonal projection from the entire closed invariant subspace onto
all its subgroup-fixed vectors, with the inherited norm. -/
def fullFixedOrthogonalProjection (K : Subgroup G) :
    S.toSubmodule →L[ℂ] S.toSubmodule := by
  letI : CompleteSpace S.toSubmodule := hS.completeSpace_coe
  letI : CompleteSpace (fixedVectors S.toRepresentation K) :=
    fullFixed_completeSpace τ hτ S hS K
  exact (fixedVectors S.toRepresentation K).starProjection

theorem fullFixedOrthogonalProjection_range (K : Subgroup G) :
    (fullFixedOrthogonalProjection τ S hS hτ K).range =
      fixedVectors S.toRepresentation K := by
  let : CompleteSpace S.toSubmodule := hS.completeSpace_coe
  let : CompleteSpace (fixedVectors S.toRepresentation K) :=
    fullFixed_completeSpace τ hτ S hS K
  exact Submodule.range_starProjection _

theorem fullFixedOrthogonalProjection_eq_self_iff (K : Subgroup G)
    (x : S.toSubmodule) :
    fullFixedOrthogonalProjection τ S hS hτ K x = x ↔
      x ∈ fixedVectors S.toRepresentation K := by
  let : CompleteSpace S.toSubmodule := hS.completeSpace_coe
  let : CompleteSpace (fixedVectors S.toRepresentation K) :=
    fullFixed_completeSpace τ hτ S hS K
  exact Submodule.starProjection_eq_self_iff

variable [TopologicalSpace G] [IsTopologicalGroup G]
variable [MeasurableSpace G] [BorelSpace G]
variable {ι : Type uI} (μ : Measure G) [μ.IsHaarMeasure]
variable (K : OpenSubgroup G) (hK : IsCompact (K : Set G))

/-- All original corner scalar equations hold on the whole fixed subspace
exactly when the full joint projection is the fixed-subspace projection. -/
theorem cornerFullJointProjection_eq_fixedProjection_iff
    (f : ι → Hecke.HeckeAlgebra.Corner μ K hK) (c : ι → ℂ) :
    cornerFullJointProjection μ K hK τ S hS hτ f c =
        fullFixedOrthogonalProjection τ S hS hτ K.toSubgroup ↔
      ∀ i x, cornerAction τ S μ K hK (f i) x = c i • x := by
  let : CompleteSpace S.toSubmodule := hS.completeSpace_coe
  let : CompleteSpace (fixedVectors S.toRepresentation K.toSubgroup) :=
    fullFixed_completeSpace τ hτ S hS K.toSubgroup
  dsimp only [cornerFullJointProjection, fullFixedOrthogonalProjection]
  rw [ambientJointProjection_eq_starProjection_iff]
  rfl

theorem hasScalarSpectrum_iff_cornerFullJointProjection
    (f : ι → Hecke.HeckeAlgebra.Corner μ K hK) (c : ι → ℂ) :
    HasScalarSpectrum (fun i => cornerAction τ S μ K hK (f i)) c ↔
      Nontrivial (fixedVectors S.toRepresentation K.toSubgroup) ∧
        cornerFullJointProjection μ K hK τ S hS hτ f c =
          fullFixedOrthogonalProjection τ S hS hτ K.toSubgroup :=
  and_congr Iff.rfl
    (cornerFullJointProjection_eq_fixedProjection_iff τ S hS hτ μ K hK f c).symm

end FullFixedProjection
end Langlands.TensorHilbertHeckeAux

namespace Langlands.TensorHilbertSphericalAux

universe uH uA

variable {p : ℕ} [Fact p.Prime] (L : PadicField.{uF} p) (r : ℕ)

local instance fullSphericalProjectionTopology (n : ℕ) :
    TopologicalSpace (GeneralLinear n L.Carrier) :=
  L.canonicalGeneralLinearTopology n
local instance fullSphericalProjectionTopologicalGroup (n : ℕ) :
    IsTopologicalGroup (GeneralLinear n L.Carrier) :=
  L.canonicalGeneralLinearTopologicalGroup n
local instance fullSphericalProjectionMeasurable (n : ℕ) :
    MeasurableSpace (GeneralLinear n L.Carrier) := borel _
local instance fullSphericalProjectionBorel (n : ℕ) :
    BorelSpace (GeneralLinear n L.Carrier) := ⟨rfl⟩
local instance fullSphericalProjectionHaar :
    (Unramified.sphericalHaar L r).IsHaarMeasure := Unramified.sphericalHaar_isHaar L r

variable {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable [CompleteSpace H]
variable (τ : Representation ℂ (GeneralLinear (r + 1) L.Carrier) H)
variable (S : Subrepresentation τ) (hS : IsClosed (S : Set H))
variable (hτ : ∀ (g : GeneralLinear (r + 1) L.Carrier) (x : H), ‖τ g x‖ = ‖x‖)

/-- Canonical spherical joint projection defined on every vector of the
closed invariant subspace, with the existing Haar and scalar normalization. -/
def sphericalFullJointProjection (s : Unramified.Eigenvalues (r + 1)) :=
  TensorHilbertHeckeAux.cornerFullJointProjection
    (Unramified.sphericalHaar L r) (Unramified.sphericalOpenSubgroup L r)
    (Unramified.sphericalOpenSubgroup_isCompact L r) τ S hS hτ
    (Unramified.standardHeckeElement L r) (Unramified.standardHeckeScalar L s)

theorem sphericalFullJointProjection_range (s : Unramified.Eigenvalues (r + 1)) :
    (sphericalFullJointProjection L r τ S hS hτ s).range =
      TensorHilbertHeckeAux.cornerFullJointEigenspace
        (Unramified.sphericalHaar L r) (Unramified.sphericalOpenSubgroup L r)
        (Unramified.sphericalOpenSubgroup_isCompact L r) τ S
        (Unramified.standardHeckeElement L r) (Unramified.standardHeckeScalar L s) := by
  dsimp only [sphericalFullJointProjection]
  exact TensorHilbertHeckeAux.cornerFullJointProjection_range
    (Unramified.sphericalHaar L r) (Unramified.sphericalOpenSubgroup L r)
    (Unramified.sphericalOpenSubgroup_isCompact L r) τ S hS hτ
    (Unramified.standardHeckeElement L r) (Unramified.standardHeckeScalar L s)

/-- Restriction is exactly the earlier canonical spherical projection on
the whole spherical fixed space. -/
theorem sphericalFullJointProjection_subtype
    (s : Unramified.Eigenvalues (r + 1))
    (x : fixedVectors S.toRepresentation (Correspondence.sphericalSubgroup L r)) :
    sphericalFullJointProjection L r τ S hS hτ s (x : S.toSubmodule) =
      (sphericalJointProjection L r τ S hS hτ s x : S.toSubmodule) := by
  dsimp only [sphericalFullJointProjection, sphericalJointProjection]
  exact TensorHilbertHeckeAux.cornerFullJointProjection_subtype
    (Unramified.sphericalHaar L r) (Unramified.sphericalOpenSubgroup L r)
    (Unramified.sphericalOpenSubgroup_isCompact L r) τ S hS hτ
    (Unramified.standardHeckeElement L r) (Unramified.standardHeckeScalar L s) x

/-- Whole spherical scalar spectrum is nontriviality together with equality
of the full joint projection and the full spherical-fixed projection. -/
theorem hasScalarSpectrum_iff_sphericalFullJointProjection
    (s : Unramified.Eigenvalues (r + 1)) :
    TensorHilbertHeckeAux.HasScalarSpectrum
      (fun i => TensorHilbertHeckeAux.cornerAction τ S (Unramified.sphericalHaar L r)
        (Unramified.sphericalOpenSubgroup L r)
        (Unramified.sphericalOpenSubgroup_isCompact L r)
        (Unramified.standardHeckeElement L r i)) (Unramified.standardHeckeScalar L s) ↔
      Nontrivial (fixedVectors S.toRepresentation (Correspondence.sphericalSubgroup L r)) ∧
        sphericalFullJointProjection L r τ S hS hτ s =
          TensorHilbertHeckeAux.fullFixedOrthogonalProjection τ S hS hτ
            (Correspondence.sphericalSubgroup L r) :=
  TensorHilbertHeckeAux.hasScalarSpectrum_iff_cornerFullJointProjection
    τ S hS hτ (Unramified.sphericalHaar L r) (Unramified.sphericalOpenSubgroup L r)
    (Unramified.sphericalOpenSubgroup_isCompact L r)
    (Unramified.standardHeckeElement L r) (Unramified.standardHeckeScalar L s)

end Langlands.TensorHilbertSphericalAux

namespace Langlands.Automorphic

open Langlands.Global Langlands.Global.FiniteAdelicGL Langlands.RestrictedTensor

variable {F : Type uF} [Field F] [NumberField F] {r : ℕ}
variable {V : FinitePlace F → Type uV}
variable [∀ v, AddCommGroup (V v)] [∀ v, Module ℂ (V v)]

local instance tensorFullSphericalProjectionRationalGroup :
    AddCommGroup (RationalInvariantFunctions F (r + 1)) := Submodule.addCommGroup _
local instance tensorFullSphericalProjectionContinuousGroup :
    AddCommGroup (ContinuousRationalFunctions F (r + 1)) := Submodule.addCommGroup _
local instance tensorFullSphericalProjectionSmoothGroup :
    AddCommGroup (FiniteSmoothRationalFunctions F (r + 1)) := Submodule.addCommGroup _
local instance tensorFullSphericalProjectionFormsGroup :
    AddCommGroup (AutomorphicForms F (r + 1)) := Submodule.addCommGroup _
local instance tensorFullSphericalProjectionFiniteSpaceGroup (S : FiniteRealization F (r + 1)) :
    AddCommGroup S.Space := Submodule.addCommGroup _
local instance tensorFullSphericalProjectionLocalSpaceGroup (v : FinitePlace F)
    (L : LocalRealization F (r + 1) v) : AddCommGroup L.Space := Submodule.addCommGroup _

namespace FiniteTensorPresentation

variable {ρ : ∀ v, Representation ℂ (FiniteLocalGL F (r + 1) v) (V v)}
variable {E : Finset (FinitePlace F)} {e : ∀ v, V v}
variable {he : ∀ v ∉ E, ∀ g ∈ localIntegral F (r + 1) v, ρ v g (e v) = e v}
variable {S : FiniteRealization F (r + 1)}
variable (P : FiniteTensorPresentation F (r + 1) ρ E e he S)
variable (b : Langlands.InvariantPositiveForm S.representation)

/-- The canonical spherical joint projection on the entire actual completed
tensor slice, including vectors outside its spherical fixed subspace. -/
def sliceHilbertFullSphericalProjection (v : FinitePlace F)
    (y : LocalTensorTail (K := ℂ) F E v e) (s : Unramified.Eigenvalues (r + 1)) :=
  TensorHilbertSphericalAux.sphericalFullJointProjection (CompletionPadic.padicField v) r
    _ (P.sliceHilbertRange b v y) (P.isClosed_sliceHilbertRange b v y)
    (fun g x => b.completedRepresentation_norm (localInclusion F (r + 1) v g) x) s

end FiniteTensorPresentation
end Langlands.Automorphic
