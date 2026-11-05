import Langlands.Automorphic.FiniteTensorHilbertCompactProjection

/-! # Canonical-object spectra and full Hilbert projections -/

noncomputable section
open scoped Classical TensorProduct
universe uF uV
set_option autoImplicit false
set_option maxHeartbeats 40000

namespace Langlands.TensorHilbertSphericalAux

universe uH uA

variable {p : ℕ} [Fact p.Prime] (L : PadicField.{uF} p) (r : ℕ)

local instance objectProjectionTopology (n : ℕ) :
    TopologicalSpace (GeneralLinear n L.Carrier) :=
  L.canonicalGeneralLinearTopology n
local instance objectProjectionTopologicalGroup (n : ℕ) :
    IsTopologicalGroup (GeneralLinear n L.Carrier) :=
  L.canonicalGeneralLinearTopologicalGroup n
local instance objectProjectionMeasurable (n : ℕ) :
    MeasurableSpace (GeneralLinear n L.Carrier) := borel _
local instance objectProjectionBorel (n : ℕ) :
    BorelSpace (GeneralLinear n L.Carrier) := ⟨rfl⟩
local instance objectProjectionHaar :
    (Unramified.sphericalHaar L r).IsHaarMeasure := Unramified.sphericalHaar_isHaar L r

variable {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable [CompleteSpace H]
variable (τ : Representation ℂ (GeneralLinear (r + 1) L.Carrier) H)
variable (S : Subrepresentation τ) (hS : IsClosed (S : Set H))
variable (hτ : ∀ (g : GeneralLinear (r + 1) L.Carrier) (x : H), ‖τ g x‖ = ‖x‖)

/-- A concrete whole-spectrum relation on the full Hilbert domain. Its
nontriviality clause is separate from equality of the two actual projections. -/
def HasFullSphericalProjectionSpectrum (s : Unramified.Eigenvalues (r + 1)) : Prop :=
  Nontrivial (fixedVectors S.toRepresentation (Correspondence.sphericalSubgroup L r)) ∧
    sphericalFullJointProjection L r τ S hS hτ s =
      TensorHilbertHeckeAux.fullFixedOrthogonalProjection τ S hS hτ
        (Correspondence.sphericalSubgroup L r)

theorem hasFullSphericalProjectionSpectrum_iff_scalar
    (s : Unramified.Eigenvalues (r + 1)) :
    HasFullSphericalProjectionSpectrum L r τ S hS hτ s ↔
      TensorHilbertHeckeAux.HasScalarSpectrum
        (fun i => TensorHilbertHeckeAux.cornerAction τ S (Unramified.sphericalHaar L r)
          (Unramified.sphericalOpenSubgroup L r)
          (Unramified.sphericalOpenSubgroup_isCompact L r)
          (Unramified.standardHeckeElement L r i)) (Unramified.standardHeckeScalar L s) :=
  (hasScalarSpectrum_iff_sphericalFullJointProjection L r τ S hS hτ s).symm

variable (A : Correspondence.AutomorphicObject.{uF, uA} L r.succPNat)
variable (e : A.obj.representation.Equiv
  (S ⊓ Langlands.smoothSubrepresentation τ).toRepresentation)

include e

/-- A genuine smooth-model equivalence identifies the canonical object's
whole spherical spectrum with the concrete full-domain projection relation. -/
theorem objectHasSpectrum_iff_fullProjection
    (s : Unramified.Eigenvalues (r + 1)) :
    Unramified.HasSphericalHeckeSpectrum L A s ↔
      HasFullSphericalProjectionSpectrum L r τ S hS hτ s :=
  (objectHasSpectrum_iff L r τ S A e s).symm.trans
    (hasScalarSpectrum_iff_sphericalFullJointProjection L r τ S hS hτ s)

/-- Passing to the existing actual isomorphism class preserves the same
projection criterion; no representative is chosen for an arbitrary class. -/
theorem objectClassHasSpectrum_iff_fullProjection
    (s : Unramified.Eigenvalues (r + 1)) :
    Unramified.HasSphericalHeckeSpectrumClass L
      (Correspondence.automorphicClassOf L A) s ↔
        HasFullSphericalProjectionSpectrum L r τ S hS hτ s :=
  (Unramified.hasSphericalHeckeSpectrumClass_classOf L A s).trans
    (objectHasSpectrum_iff_fullProjection L r τ S hS hτ A e s)

/-- The existing object's admissibility gives finite rank for the exact
range of the canonical full-domain projection, with no spectral assumption. -/
theorem objectFullProjection_finite (s : Unramified.Eigenvalues (r + 1)) :
    FiniteDimensional ℂ (sphericalFullJointProjection L r τ S hS hτ s).range :=
  TensorHilbertHeckeAux.factorCornerFullJointProjection_finite τ S hS hτ
    (Unramified.sphericalHaar L r) (Unramified.sphericalOpenSubgroup L r)
    (Unramified.sphericalOpenSubgroup_isCompact L r) e A.property.2
    (Unramified.standardHeckeElement L r) (Unramified.standardHeckeScalar L s)

theorem objectFullProjection_finrank_le (s : Unramified.Eigenvalues (r + 1)) :
    Module.finrank ℂ (sphericalFullJointProjection L r τ S hS hτ s).range ≤
      Module.finrank ℂ
        (fixedVectors A.obj.representation (Correspondence.sphericalSubgroup L r)) :=
  TensorHilbertHeckeAux.factorCornerFullJointProjection_finrank_le τ S hS hτ
    (Unramified.sphericalHaar L r) (Unramified.sphericalOpenSubgroup L r)
    (Unramified.sphericalOpenSubgroup_isCompact L r) e A.property.2
    (Unramified.standardHeckeElement L r) (Unramified.standardHeckeScalar L s)

theorem objectFullProjection_isCompact (s : Unramified.Eigenvalues (r + 1)) :
    IsCompactOperator (sphericalFullJointProjection L r τ S hS hτ s) :=
  TensorHilbertHeckeAux.factorCornerFullJointProjection_isCompact τ S hS hτ
    (Unramified.sphericalHaar L r) (Unramified.sphericalOpenSubgroup L r)
    (Unramified.sphericalOpenSubgroup_isCompact L r) e A.property.2
    (Unramified.standardHeckeElement L r) (Unramified.standardHeckeScalar L s)

/-- When the actual object has this whole spectrum, the full-domain
projection range is precisely the full spherical fixed submodule. -/
theorem objectFullProjection_range_of_spectrum
    (s : Unramified.Eigenvalues (r + 1))
    (hs : Unramified.HasSphericalHeckeSpectrum L A s) :
    (sphericalFullJointProjection L r τ S hS hτ s).range =
      fixedVectors S.toRepresentation (Correspondence.sphericalSubgroup L r) := by
  rw [((objectHasSpectrum_iff_fullProjection L r τ S hS hτ A e s).mp hs).2]
  exact TensorHilbertHeckeAux.fullFixedOrthogonalProjection_range τ S hS hτ _

theorem objectFullProjection_finrank_of_spectrum
    (s : Unramified.Eigenvalues (r + 1))
    (hs : Unramified.HasSphericalHeckeSpectrum L A s) :
    Module.finrank ℂ (sphericalFullJointProjection L r τ S hS hτ s).range =
      Module.finrank ℂ
        (fixedVectors A.obj.representation (Correspondence.sphericalSubgroup L r)) := by
  rw [objectFullProjection_range_of_spectrum L r τ S hS hτ A e s hs]
  exact TensorHilbertFixedAux.factorFixed_finrank τ S e
    (Unramified.sphericalOpenSubgroup L r)

end Langlands.TensorHilbertSphericalAux

namespace Langlands.Automorphic

open Langlands.Global Langlands.Global.FiniteAdelicGL Langlands.RestrictedTensor

variable {F : Type uF} [Field F] [NumberField F] {r : ℕ}
variable {V : FinitePlace F → Type uV}
variable [∀ v, AddCommGroup (V v)] [∀ v, Module ℂ (V v)]

local instance tensorObjectProjectionRationalGroup :
    AddCommGroup (RationalInvariantFunctions F (r + 1)) := Submodule.addCommGroup _
local instance tensorObjectProjectionContinuousGroup :
    AddCommGroup (ContinuousRationalFunctions F (r + 1)) := Submodule.addCommGroup _
local instance tensorObjectProjectionSmoothGroup :
    AddCommGroup (FiniteSmoothRationalFunctions F (r + 1)) := Submodule.addCommGroup _
local instance tensorObjectProjectionFormsGroup :
    AddCommGroup (AutomorphicForms F (r + 1)) := Submodule.addCommGroup _
local instance tensorObjectProjectionFiniteSpaceGroup (S : FiniteRealization F (r + 1)) :
    AddCommGroup S.Space := Submodule.addCommGroup _
local instance tensorObjectProjectionLocalSpaceGroup (v : FinitePlace F)
    (L : LocalRealization F (r + 1) v) : AddCommGroup L.Space := Submodule.addCommGroup _

namespace FiniteTensorPresentation

variable {ρ : ∀ v, Representation ℂ (FiniteLocalGL F (r + 1) v) (V v)}
variable {E : Finset (FinitePlace F)} {e : ∀ v, V v}
variable {he : ∀ v ∉ E, ∀ g ∈ localIntegral F (r + 1) v, ρ v g (e v) = e v}
variable {S : FiniteRealization F (r + 1)}
variable (P : FiniteTensorPresentation F (r + 1) ρ E e he S)
variable (b : Langlands.InvariantPositiveForm S.representation)

/-- The full-domain projection spectrum of the actual closed tensor slice.
The definition permits zero tails and retains nontriviality explicitly. -/
def HasHilbertFullProjectionSpectrum (v : FinitePlace F)
    (y : LocalTensorTail (K := ℂ) F E v e) (s : Unramified.Eigenvalues (r + 1)) : Prop :=
  TensorHilbertSphericalAux.HasFullSphericalProjectionSpectrum
    (CompletionPadic.padicField v) r _ (P.sliceHilbertRange b v y)
    (P.isClosed_sliceHilbertRange b v y)
    (fun g x => b.completedRepresentation_norm (localInclusion F (r + 1) v g) x) s

end FiniteTensorPresentation
end Langlands.Automorphic
