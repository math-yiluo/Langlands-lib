import Langlands.Geometry.FormalGroup.DeligneShiftBaseChange
import Langlands.Geometry.FormalGroup.DeligneProjectiveAction
import Langlands.Geometry.FormalGroup.DeligneNilpFunctor

/-! # Base-change naturality of the actual Deligne class actions -/

noncomputable section

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace Langlands.DeligneFormalSpace

open CategoryTheory _root_.AlgebraicGeometry
open scoped MatrixGroups

variable {O : Type u} [CommRing O] {d : ℕ} [NeZero d] {π : O}
  {F : Type u} [Field F] [Algebra O F] {S S' : Scheme.{u}}
  {φ : O →+* Γ(S, ⊤)}

namespace SheafPreDatum.IsoClass

/-- The genuine integer-shift comparison descends to preliminary classes. -/
theorem pullback_shiftInt (hπ : algebraMap O F π ≠ 0) (f : S' ⟶ S) (k : ℤ)
    (q : IsoClass (d := d) (π := π) (F := F) (φ := φ)) :
    pullback f (shiftInt hπ k q) = shiftInt hπ k (pullback f q) := by
  induction q using Quotient.inductionOn with
  | h D => exact Quotient.sound ⟨D.pullbackShiftIntIso f hπ k⟩

/-- Actual rational reframing commutes with base change on preliminary classes. -/
theorem pullback_reframe (f : S' ⟶ S)
    (g : (Fin d → F) ≃ₗ[F] (Fin d → F))
    (q : IsoClass (d := d) (π := π) (F := F) (φ := φ)) :
    pullback f (reframe g q) = reframe g (pullback f q) := by
  induction q using Quotient.inductionOn with
  | h D => exact congrArg mk (D.pullback_reframe f g)

/-- The combined preliminary operation commutes with arbitrary scheme base change. -/
theorem pullback_shiftReframe (hπ : algebraMap O F π ≠ 0) (f : S' ⟶ S)
    (g : (Fin d → F) ≃ₗ[F] (Fin d → F)) (k : ℤ)
    (q : IsoClass (d := d) (π := π) (F := F) (φ := φ)) :
    pullback f (shiftReframe hπ g k q) =
      shiftReframe hπ g k (pullback f q) := by
  unfold shiftReframe
  rw [pullback_reframe, pullback_shiftInt]

end SheafPreDatum.IsoClass

namespace SheafDatum.IsoClass

variable (hπ : algebraMap O F π ≠ 0)

/-- The determinant-unit frame operation is natural on actual admissible classes. -/
theorem pullback_reframe (f : S' ⟶ S) (g : determinantUnitSubgroup O d F)
    (q : IsoClass (d := d) (π := π) (φ := φ) hπ) :
    pullback hπ f (reframe hπ g q) = reframe hπ g (pullback hπ f q) := by
  apply toPreliminary_injective hπ
  simp only [toPreliminary_pullback, toPreliminary_reframe]
  exact SheafPreDatum.IsoClass.pullback_reframe f g.val _

/-- Arithmetic correction and actual pullback commute on admissible classes. -/
theorem pullback_shiftReframe (f : S' ⟶ S) (p : shiftReframeSubgroup (d := d) hπ)
    (q : IsoClass (d := d) (π := π) (φ := φ) hπ) :
    pullback hπ f (shiftReframe hπ p q) =
      shiftReframe hπ p (pullback hπ f q) := by
  apply toPreliminary_injective hπ
  simp only [toPreliminary_pullback, toPreliminary_shiftReframe]
  exact SheafPreDatum.IsoClass.pullback_shiftReframe hπ f p.val.1 p.val.2.toAdd _

/-- Scalar identification transports the determinant-unit naturality square. -/
theorem pullbackTo_reframe (f : S' ⟶ S) {φ' : O →+* Γ(S', ⊤)}
    (hf : pulledGlobalScalar f φ = φ') (g : determinantUnitSubgroup O d F)
    (q : IsoClass (d := d) (π := π) (φ := φ) hπ) :
    pullbackTo hπ f hf (reframe hπ g q) =
      reframe hπ g (pullbackTo hπ f hf q) := by
  subst φ'
  exact pullback_reframe hπ f g q

/-- Scalar identification transports the corrected shift-and-frame square. -/
theorem pullbackTo_shiftReframe (f : S' ⟶ S) {φ' : O →+* Γ(S', ⊤)}
    (hf : pulledGlobalScalar f φ = φ') (p : shiftReframeSubgroup (d := d) hπ)
    (q : IsoClass (d := d) (π := π) (φ := φ) hπ) :
    pullbackTo hπ f hf (shiftReframe hπ p q) =
      shiftReframe hπ p (pullbackTo hπ f hf q) := by
  subst φ'
  exact pullback_shiftReframe hπ f p q

end SheafDatum.IsoClass

variable {B B' : FormalGroup.Nilp.{u, u} O π}

/-- The actual Nilp class map commutes with every determinant-corrected pair. -/
theorem nilpSheafClassMap_shiftReframe (hπ : algebraMap O F π ≠ 0) (f : B ⟶ B')
    (p : shiftReframeSubgroup (d := d) hπ)
    (q : NilpSheafIsoClass d π F hπ B) :
    nilpSheafClassMap d π F hπ f (SheafDatum.IsoClass.shiftReframe hπ p q) =
      SheafDatum.IsoClass.shiftReframe hπ p (nilpSheafClassMap d π F hπ f q) :=
  SheafDatum.IsoClass.pullbackTo_shiftReframe hπ (nilpSpecMap f)
    (nilpGlobalScalar_naturality f) p q

/-- Corrected pairs give natural automorphisms of the constructed Nilp class functor. -/
def nilpSheafShiftReframeAut (hπ : algebraMap O F π ≠ 0)
    (p : shiftReframeSubgroup (d := d) hπ) :
    Aut (nilpSheafClassFunctor d π F hπ) :=
  NatIso.ofComponents
    (fun B => (SheafDatum.IsoClass.shiftReframeEquiv
      (φ := nilpGlobalScalar π B) hπ p).toIso) (by
        intro B B' f
        ext q
        exact (nilpSheafClassMap_shiftReframe hπ f p q).symm)

/-- The natural component is precisely the published corrected class operation. -/
@[simp]
theorem nilpSheafShiftReframeAut_hom_app (hπ : algebraMap O F π ≠ 0)
    (p : shiftReframeSubgroup (d := d) hπ) (B : FormalGroup.Nilp.{u, u} O π)
    (q : NilpSheafIsoClass d π F hπ B) :
    (nilpSheafShiftReframeAut hπ p).hom.app B q =
      SheafDatum.IsoClass.shiftReframe hπ p q := rfl

section Valued

variable [IsDomain O] [IsDiscreteValuationRing O] [IsFractionRing O F]

namespace SheafDatum.IsoClass

variable (hπ : Irreducible π)

/-- The DVR-normalized general linear operation commutes with actual pullback. -/
theorem pullback_normalizedReframe (f : S' ⟶ S)
    (g : (Fin d → F) ≃ₗ[F] (Fin d → F))
    (q : IsoClass (d := d) (π := π) (φ := φ)
      (coefficientUniformizer_ne_zero (F := F) hπ)) :
    pullback _ f (normalizedReframe hπ g q) =
      normalizedReframe hπ g (pullback _ f q) :=
  pullback_shiftReframe _ f (normalizedReframeHom hπ g) q

/-- Naturality descends through the actual matrix projective quotient. -/
theorem pullback_projectiveReframe (f : S' ⟶ S) (g : PGL(d, F))
    (q : IsoClass (d := d) (π := π) (φ := φ)
      (coefficientUniformizer_ne_zero (F := F) hπ)) :
    pullback _ f (projectiveReframe hπ g q) =
      projectiveReframe hπ g (pullback _ f q) := by
  induction g using Matrix.ProjGenLinGroup.induction_on with
  | mk g =>
    simp only [projectiveReframe_mk]
    exact pullback_normalizedReframe hπ f (matrixReframeEquiv d F g) q

/-- The normalized general linear square respects an actual scalar identification. -/
theorem pullbackTo_normalizedReframe (f : S' ⟶ S) {φ' : O →+* Γ(S', ⊤)}
    (hf : pulledGlobalScalar f φ = φ') (g : (Fin d → F) ≃ₗ[F] (Fin d → F))
    (q : IsoClass (d := d) (π := π) (φ := φ)
      (coefficientUniformizer_ne_zero (F := F) hπ)) :
    pullbackTo _ f hf (normalizedReframe hπ g q) =
      normalizedReframe hπ g (pullbackTo _ f hf q) :=
  pullbackTo_shiftReframe _ f hf (normalizedReframeHom hπ g) q

/-- The projective naturality square includes the actual scalar transport. -/
theorem pullbackTo_projectiveReframe (f : S' ⟶ S) {φ' : O →+* Γ(S', ⊤)}
    (hf : pulledGlobalScalar f φ = φ') (g : PGL(d, F))
    (q : IsoClass (d := d) (π := π) (φ := φ)
      (coefficientUniformizer_ne_zero (F := F) hπ)) :
    pullbackTo _ f hf (projectiveReframe hπ g q) =
      projectiveReframe hπ g (pullbackTo _ f hf q) := by
  subst φ'
  exact pullback_projectiveReframe hπ f g q

end SheafDatum.IsoClass

/-- The normalized GL operation commutes with the actual Nilp class maps. -/
theorem nilpSheafClassMap_normalizedReframe (hπ : Irreducible π) (f : B ⟶ B')
    (g : (Fin d → F) ≃ₗ[F] (Fin d → F))
    (q : NilpSheafIsoClass d π F (coefficientUniformizer_ne_zero (F := F) hπ) B) :
    nilpSheafClassMap d π F _ f (SheafDatum.IsoClass.normalizedReframe hπ g q) =
      SheafDatum.IsoClass.normalizedReframe hπ g (nilpSheafClassMap d π F _ f q) :=
  nilpSheafClassMap_shiftReframe _ f (normalizedReframeHom hπ g) q

/-- The actual PGL operation commutes with the scalar-aware Nilp class maps. -/
theorem nilpSheafClassMap_projectiveReframe (hπ : Irreducible π) (f : B ⟶ B')
    (g : PGL(d, F))
    (q : NilpSheafIsoClass d π F (coefficientUniformizer_ne_zero (F := F) hπ) B) :
    nilpSheafClassMap d π F _ f (SheafDatum.IsoClass.projectiveReframe hπ g q) =
      SheafDatum.IsoClass.projectiveReframe hπ g (nilpSheafClassMap d π F _ f q) :=
  SheafDatum.IsoClass.pullbackTo_projectiveReframe hπ (nilpSpecMap f)
    (nilpGlobalScalar_naturality f) g q

/-- Every normalized frame change is a natural automorphism on actual Nilp points. -/
def nilpSheafNormalizedReframeAut (hπ : Irreducible π)
    (g : (Fin d → F) ≃ₗ[F] (Fin d → F)) :
    Aut (nilpSheafClassFunctor d π F (coefficientUniformizer_ne_zero (F := F) hπ)) :=
  nilpSheafShiftReframeAut _ (normalizedReframeHom hπ g)

/-- The normalized natural component is the already constructed GL operation. -/
@[simp]
theorem nilpSheafNormalizedReframeAut_hom_app (hπ : Irreducible π)
    (g : (Fin d → F) ≃ₗ[F] (Fin d → F)) (B : FormalGroup.Nilp.{u, u} O π)
    (q : NilpSheafIsoClass d π F (coefficientUniformizer_ne_zero (F := F) hπ) B) :
    (nilpSheafNormalizedReframeAut hπ g).hom.app B q =
      SheafDatum.IsoClass.normalizedReframe hπ g q := rfl

/-- Actual projective elements give natural automorphisms of the Nilp point functor. -/
def nilpSheafProjectiveReframeAut (hπ : Irreducible π) (g : PGL(d, F)) :
    Aut (nilpSheafClassFunctor d π F (coefficientUniformizer_ne_zero (F := F) hπ)) :=
  NatIso.ofComponents
    (fun B => (SheafDatum.IsoClass.projectiveReframeEquiv
      (φ := nilpGlobalScalar π B) hπ g).toIso) (by
        intro B B' f
        ext q
        exact (nilpSheafClassMap_projectiveReframe hπ f g q).symm)

/-- The projective natural component is the published action of the actual quotient. -/
@[simp]
theorem nilpSheafProjectiveReframeAut_hom_app (hπ : Irreducible π)
    (g : PGL(d, F)) (B : FormalGroup.Nilp.{u, u} O π)
    (q : NilpSheafIsoClass d π F (coefficientUniformizer_ne_zero (F := F) hπ) B) :
    (nilpSheafProjectiveReframeAut hπ g).hom.app B q =
      SheafDatum.IsoClass.projectiveReframe hπ g q := rfl

end Valued

end Langlands.DeligneFormalSpace
