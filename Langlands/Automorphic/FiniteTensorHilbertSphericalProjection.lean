import Langlands.Automorphic.FiniteTensorHilbertHeckeProjection
import Langlands.Automorphic.FiniteTensorHilbertSphericalComparison

/-! # Canonical spherical projections on full completed tensor slices -/

noncomputable section
open scoped Classical TensorProduct
universe uF uV uI
set_option autoImplicit false
set_option maxHeartbeats 40000

namespace Langlands.TensorHilbertHeckeAux

universe uG uH

section JointIdentity

variable {ι : Type uI}
variable {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable [CompleteSpace H]
variable (T : ι → H →L[ℂ] H) (c : ι → ℂ)

/-- The joint projection is identity exactly when every original operator
acts by its prescribed scalar on the whole space. -/
theorem jointOrthogonalProjection_eq_id_iff :
    jointOrthogonalProjection T c = ContinuousLinearMap.id ℂ H ↔
      ∀ i x, T i x = c i • x := by
  constructor
  · intro h i x
    have hx : jointOrthogonalProjection T c x = x :=
      congrArg (fun U : H →L[ℂ] H => U x) h
    exact (jointOrthogonalProjection_eq_self_iff T c x).mp hx i
  · intro h
    ext x
    exact (jointOrthogonalProjection_eq_self_iff T c x).mpr (fun i => h i x)

/-- Nontriviality is retained separately: identity of the projection alone
does not assert that the Hilbert space is nonzero. -/
theorem hasScalarSpectrum_iff_jointOrthogonalProjection :
    HasScalarSpectrum (fun i => (T i).toLinearMap) c ↔
      Nontrivial H ∧ jointOrthogonalProjection T c = ContinuousLinearMap.id ℂ H :=
  and_congr Iff.rfl (jointOrthogonalProjection_eq_id_iff T c).symm

end JointIdentity

section CornerIdentity

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

/-- The entire-fixed-space projection is identity exactly when all original
algebraic corner operators act by their prescribed scalars. -/
theorem cornerJointOrthogonalProjection_eq_id_iff
    (f : ι → Hecke.HeckeAlgebra.Corner μ K hK) (c : ι → ℂ) :
    cornerJointOrthogonalProjection μ K hK τ S hS hτ f c =
        ContinuousLinearMap.id ℂ (fixedVectors S.toRepresentation K.toSubgroup) ↔
      ∀ i x, cornerAction τ S μ K hK (f i) x = c i • x := by
  constructor
  · intro h i x
    have hx : cornerJointOrthogonalProjection μ K hK τ S hS hτ f c x = x :=
      congrArg
        (fun U : fixedVectors S.toRepresentation K.toSubgroup →L[ℂ]
          fixedVectors S.toRepresentation K.toSubgroup => U x) h
    exact (cornerJointOrthogonalProjection_eq_self_iff μ K hK τ S hS hτ f c x).mp hx i
  · intro h
    apply ContinuousLinearMap.ext
    intro x
    exact (cornerJointOrthogonalProjection_eq_self_iff μ K hK τ S hS hτ f c x).mpr
      (fun i => h i x)

theorem hasScalarSpectrum_iff_cornerJointOrthogonalProjection
    (f : ι → Hecke.HeckeAlgebra.Corner μ K hK) (c : ι → ℂ) :
    HasScalarSpectrum (fun i => cornerAction τ S μ K hK (f i)) c ↔
      Nontrivial (fixedVectors S.toRepresentation K.toSubgroup) ∧
        cornerJointOrthogonalProjection μ K hK τ S hS hτ f c =
          ContinuousLinearMap.id ℂ (fixedVectors S.toRepresentation K.toSubgroup) :=
  and_congr Iff.rfl
    (cornerJointOrthogonalProjection_eq_id_iff μ K hK τ S hS hτ f c).symm

end CornerIdentity
end Langlands.TensorHilbertHeckeAux

namespace Langlands.TensorHilbertSphericalAux

universe uH

variable {p : ℕ} [Fact p.Prime] (L : PadicField.{uF} p) (r : ℕ)

local instance sphericalProjectionTopology (n : ℕ) :
    TopologicalSpace (GeneralLinear n L.Carrier) :=
  L.canonicalGeneralLinearTopology n
local instance sphericalProjectionTopologicalGroup (n : ℕ) :
    IsTopologicalGroup (GeneralLinear n L.Carrier) :=
  L.canonicalGeneralLinearTopologicalGroup n
local instance sphericalProjectionMeasurable (n : ℕ) :
    MeasurableSpace (GeneralLinear n L.Carrier) := borel _
local instance sphericalProjectionBorel (n : ℕ) :
    BorelSpace (GeneralLinear n L.Carrier) := ⟨rfl⟩
local instance sphericalProjectionHaar :
    (Unramified.sphericalHaar L r).IsHaarMeasure := Unramified.sphericalHaar_isHaar L r

variable {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable [CompleteSpace H]
variable (τ : Representation ℂ (GeneralLinear (r + 1) L.Carrier) H)
variable (S : Subrepresentation τ) (hS : IsClosed (S : Set H))
variable (hτ : ∀ (g : GeneralLinear (r + 1) L.Carrier) (x : H), ‖τ g x‖ = ‖x‖)

/-- The canonical spherical joint projection, using the existing mass-one
Haar measure, integral subgroup, standard double cosets and normalized scalars. -/
def sphericalJointProjection (s : Unramified.Eigenvalues (r + 1)) :=
  TensorHilbertHeckeAux.cornerJointOrthogonalProjection
    (Unramified.sphericalHaar L r) (Unramified.sphericalOpenSubgroup L r)
    (Unramified.sphericalOpenSubgroup_isCompact L r) τ S hS hτ
    (Unramified.standardHeckeElement L r) (Unramified.standardHeckeScalar L s)

/-- Its range is the joint eigenspace for the unchanged algebraic standard
operators and normalized scalars. -/
theorem sphericalJointProjection_range (s : Unramified.Eigenvalues (r + 1)) :
    (sphericalJointProjection L r τ S hS hτ s).range =
      TensorHilbertHeckeAux.cornerJointEigenspace τ S (Unramified.sphericalHaar L r)
        (Unramified.sphericalOpenSubgroup L r)
        (Unramified.sphericalOpenSubgroup_isCompact L r)
        (Unramified.standardHeckeElement L r) (Unramified.standardHeckeScalar L s) := by
  dsimp only [sphericalJointProjection]
  exact TensorHilbertHeckeAux.cornerJointOrthogonalProjection_range
    (Unramified.sphericalHaar L r) (Unramified.sphericalOpenSubgroup L r)
    (Unramified.sphericalOpenSubgroup_isCompact L r) τ S hS hτ
    (Unramified.standardHeckeElement L r) (Unramified.standardHeckeScalar L s)

/-- Whole-space scalar spectrum means precisely nontriviality together with
identity of the actual spherical projection. -/
theorem hasScalarSpectrum_iff_sphericalJointProjection
    (s : Unramified.Eigenvalues (r + 1)) :
    TensorHilbertHeckeAux.HasScalarSpectrum
      (fun i => TensorHilbertHeckeAux.cornerAction τ S (Unramified.sphericalHaar L r)
        (Unramified.sphericalOpenSubgroup L r)
        (Unramified.sphericalOpenSubgroup_isCompact L r)
        (Unramified.standardHeckeElement L r i)) (Unramified.standardHeckeScalar L s) ↔
      Nontrivial (fixedVectors S.toRepresentation (Correspondence.sphericalSubgroup L r)) ∧
        sphericalJointProjection L r τ S hS hτ s =
          ContinuousLinearMap.id ℂ
            (fixedVectors S.toRepresentation (Correspondence.sphericalSubgroup L r)) :=
  TensorHilbertHeckeAux.hasScalarSpectrum_iff_cornerJointOrthogonalProjection
    (Unramified.sphericalHaar L r) (Unramified.sphericalOpenSubgroup L r)
    (Unramified.sphericalOpenSubgroup_isCompact L r) τ S hS hτ
    (Unramified.standardHeckeElement L r) (Unramified.standardHeckeScalar L s)

end Langlands.TensorHilbertSphericalAux

namespace Langlands.Automorphic

open Langlands.Global Langlands.Global.FiniteAdelicGL Langlands.RestrictedTensor

variable {F : Type uF} [Field F] [NumberField F] {r : ℕ}
variable {V : FinitePlace F → Type uV}
variable [∀ v, AddCommGroup (V v)] [∀ v, Module ℂ (V v)]

local instance tensorSphericalProjectionRationalGroup :
    AddCommGroup (RationalInvariantFunctions F (r + 1)) := Submodule.addCommGroup _
local instance tensorSphericalProjectionContinuousGroup :
    AddCommGroup (ContinuousRationalFunctions F (r + 1)) := Submodule.addCommGroup _
local instance tensorSphericalProjectionSmoothGroup :
    AddCommGroup (FiniteSmoothRationalFunctions F (r + 1)) := Submodule.addCommGroup _
local instance tensorSphericalProjectionFormsGroup :
    AddCommGroup (AutomorphicForms F (r + 1)) := Submodule.addCommGroup _
local instance tensorSphericalProjectionFiniteSpaceGroup (S : FiniteRealization F (r + 1)) :
    AddCommGroup S.Space := Submodule.addCommGroup _
local instance tensorSphericalProjectionLocalSpaceGroup (v : FinitePlace F)
    (L : LocalRealization F (r + 1) v) : AddCommGroup L.Space := Submodule.addCommGroup _

namespace FiniteTensorPresentation

variable {ρ : ∀ v, Representation ℂ (FiniteLocalGL F (r + 1) v) (V v)}
variable {E : Finset (FinitePlace F)} {e : ∀ v, V v}
variable {he : ∀ v ∉ E, ∀ g ∈ localIntegral F (r + 1) v, ρ v g (e v) = e v}
variable {S : FiniteRealization F (r + 1)}
variable (P : FiniteTensorPresentation F (r + 1) ρ E e he S)
variable (b : Langlands.InvariantPositiveForm S.representation)

/-- The canonical spherical projection on all spherical fixed vectors of the
actual full closed tensor slice in the supplied global Hilbert completion. -/
def sliceHilbertSphericalProjection (v : FinitePlace F)
    (y : LocalTensorTail (K := ℂ) F E v e) (s : Unramified.Eigenvalues (r + 1)) :=
  TensorHilbertSphericalAux.sphericalJointProjection (CompletionPadic.padicField v) r
    _ (P.sliceHilbertRange b v y) (P.isClosed_sliceHilbertRange b v y)
    (fun g x => b.completedRepresentation_norm (localInclusion F (r + 1) v g) x) s

end FiniteTensorPresentation
end Langlands.Automorphic
