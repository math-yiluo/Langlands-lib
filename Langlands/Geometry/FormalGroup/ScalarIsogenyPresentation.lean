import Langlands.Geometry.FormalGroup.LocalQuasiIsogeny

/-! # Global scalar-denominator presentations and local quasi-isogenies -/

noncomputable section

universe u v

namespace Langlands.FormalGroup.ModuleLaw

open CategoryTheory Opposite TopologicalSpace

attribute [local instance] coefficientAlgebra coefficientScalarTower

variable {O : Type u} [CommRing O]
variable {R S : Type v} [CommRing R] [CommRing S] [Algebra O R] [Algebra O S]
variable {F : Type v} [Field F] [Algebra O F]
variable {σ τ : Type} [Finite σ] [Finite τ]
variable {M : ModuleLaw O R σ} {N : ModuleLaw O R τ}

namespace RationalHom

/-- A single global integral isogeny represents a scalar power of the actual
tensor Hom. This is stronger than the pointwise local sheaf condition. -/
structure ScalarIsogenyPresentation (π : O) (z : RationalHom F M N) where
  exponent : ℕ
  representative : Hom M N
  isIsogeny : representative.IsIsogeny
  represents : (algebraMap O F π) ^ exponent • z = ofHom representative

namespace ScalarIsogenyPresentation

variable {π : O} {z : RationalHom F M N}

/-- Apply actual coefficient base change to the global integral numerator. -/
def map (P : ScalarIsogenyPresentation π z) (φ : R →ₐ[O] S) :
    ScalarIsogenyPresentation π (RationalHom.map φ z) where
  exponent := P.exponent
  representative := P.representative.map φ
  isIsogeny := P.isIsogeny.map φ
  represents := by
    have h := congrArg (RationalHom.map (F := F) φ) P.represents
    simpa only [map_smul, map_ofHom] using h

/-- Division by a nonzero scalar power gives a global rational presentation. -/
def ofDenominator (π : O) (hπ : algebraMap O F π ≠ 0) (n : ℕ)
    (f : Hom M N) (hf : f.IsIsogeny) :
    ScalarIsogenyPresentation π
      (((algebraMap O F π) ^ n)⁻¹ • (ofHom f : RationalHom F M N)) where
  exponent := n
  representative := f
  isIsogeny := hf
  represents := by rw [smul_smul, mul_inv_cancel₀ (pow_ne_zero n hπ), one_smul]

/-- Integral isogenies supply presentations with exponent zero. -/
def ofIsogeny (π : O) (f : Hom M N) (hf : f.IsIsogeny) :
    ScalarIsogenyPresentation π (ofHom (F := F) f) where
  exponent := 0
  representative := f
  isIsogeny := hf
  represents := by rw [pow_zero, one_smul]

end ScalarIsogenyPresentation

end RationalHom

namespace RationalSection

@[simp]
theorem ofGlobal_smul (a : F) (z : RationalHom F M N) :
    ofGlobal (a • z) = a • ofGlobal z := by
  simp only [ofGlobal, map_smul]
  exact (ofRational (F := F) (M := M) (N := N) ⊤).map_smul a _

/-- Integral global tensors map to the same sections as their actual
structural coefficient extensions to Γ(Spec R). -/
theorem ofGlobal_ofHom (f : Hom M N) :
    ofGlobal (RationalHom.ofHom (F := F) f) =
      (ofIntegral ⊤ (f.map
        (IsScalarTower.toAlgHom O R ((coefficientStructurePresheaf R).obj (op ⊤)))) :
        RationalSection F M N ⊤) := by
  change ofRational ⊤ (RationalHom.map _ (RationalHom.ofHom f)) = _
  rw [RationalHom.map_ofHom]
  rfl

end RationalSection

namespace RationalHom.ScalarIsogenyPresentation

variable {π : O} {z : RationalHom F M N}

/-- A single global denominator implies the local rational-sheaf condition. -/
theorem isLocallyScalarIsogeny (P : ScalarIsogenyPresentation π z) :
    RationalSection.IsLocallyScalarIsogeny π (RationalSection.ofGlobal z) := by
  intro x hx
  let φ : R →ₐ[O] ((coefficientStructurePresheaf R).obj (op ⊤)) :=
    IsScalarTower.toAlgHom O R _
  refine ⟨⊤, hx, 𝟙 _, P.exponent, P.representative.map φ, P.isIsogeny.map φ, ?_⟩
  rw [RationalSection.restrict_id, ← RationalSection.ofGlobal_smul, P.represents]
  exact RationalSection.ofGlobal_ofHom P.representative

/-- Construct the genuine local quasi-isogeny with its nilpotent-base hypotheses. -/
def toLocalQuasiIsogeny (P : ScalarIsogenyPresentation π z)
    (hπ : algebraMap O F π ≠ 0)
    (hM : M.IsPiDivisible π) (hN : N.IsPiDivisible π) :
    LocalQuasiIsogeny F π M N ⊤ where
  scalar_ne_zero := hπ
  source_divisible := hM
  target_divisible := hN
  val := RationalSection.ofGlobal z
  isLocal := P.isLocallyScalarIsogeny

end RationalHom.ScalarIsogenyPresentation

namespace LocalQuasiIsogeny

/-- An actual integral isomorphism gives a local quasi-isogeny. -/
def ofIso (π : O) (hπ : algebraMap O F π ≠ 0) (e : Iso M N)
    (hM : M.IsPiDivisible π) : LocalQuasiIsogeny F π M N ⊤ :=
  (RationalHom.ScalarIsogenyPresentation.ofIsogeny (F := F) π e.hom e.isIsogeny).toLocalQuasiIsogeny
    hπ hM (e.isPiDivisible π hM)

/-- The identity local quasi-isogeny on a π-divisible formal module. -/
def refl (π : O) (hπ : algebraMap O F π ≠ 0) (M : ModuleLaw O R σ)
    (hM : M.IsPiDivisible π) : LocalQuasiIsogeny F π M M ⊤ :=
  ofIso π hπ (Iso.refl M) hM

end LocalQuasiIsogeny

end Langlands.FormalGroup.ModuleLaw
