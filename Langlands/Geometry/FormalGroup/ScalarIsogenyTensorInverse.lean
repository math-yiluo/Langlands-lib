import Langlands.Geometry.FormalGroup.IsogenyDual
import Langlands.Geometry.FormalGroup.LocalQuasiIsogenyGroupoid
import Langlands.Geometry.FormalGroup.ScalarIsogenyPresentation

/-! # Scalar-denominator isogenies in the tensor Hom and the rational Hom sheaf -/

noncomputable section
universe u v

namespace Langlands.FormalGroup.ModuleLaw
open TopologicalSpace

variable {O : Type u} [CommRing O]
variable {R : Type v} [CommRing R] [Algebra O R]
variable {F : Type v} [Field F] [Algebra O F]
variable {σ τ : Type} [Finite σ] [Finite τ]
variable {M : ModuleLaw O R σ} {N : ModuleLaw O R τ}

namespace RationalHom

/-- The tensor of a scalar endomorphism is the corresponding multiple of the tensor identity. -/
theorem ofHom_scalarHom (a : O) :
    ofHom (F := F) (M.scalarHom a) = (algebraMap O F a) • id M := by
  rw [scalarHom, map_smul, ← IsScalarTower.algebraMap_smul F a, ofHom_id]

namespace ScalarIsogenyPresentation

variable [IsDomain O] [IsFractionRing O F]
variable {π : O} {z : RationalHom F M N}

/-- A scalar-denominator tensor of an integral isogeny has a two-sided tensor inverse,
with a scalar-denominator presentation furnished by an integral dual isogeny. -/
theorem exists_quasiIsogeny (P : ScalarIsogenyPresentation π z)
    (hπ : algebraMap O F π ≠ 0) (hM : M.IsPiDivisible π) (hN : N.IsPiDivisible π) :
    ∃ e : QuasiIsogeny F M N, e.hom = z ∧ Nonempty (ScalarIsogenyPresentation π e.inv) := by
  obtain ⟨k, hdual⟩ := P.isIsogeny.exists_dual hM hN
  let n := P.exponent
  obtain ⟨g, hg, hgf, hfg⟩ := hdual (n + k) (Nat.le_add_left k n)
  let c := algebraMap O F π
  have hcn : c ^ n ≠ 0 := pow_ne_zero n hπ
  have hck : c ^ k ≠ 0 := pow_ne_zero k hπ
  have hz : z = (c ^ n)⁻¹ • ofHom P.representative := by
    change z = (c ^ P.exponent)⁻¹ • ofHom P.representative
    rw [← P.represents, inv_smul_smul₀ hcn]
  have hc : (c ^ k)⁻¹ * ((c ^ n)⁻¹ * c ^ (n + k)) = 1 := by
    rw [pow_add, inv_mul_cancel_left₀ hcn, inv_mul_cancel₀ hck]
  let w : RationalHom F N M := (c ^ k)⁻¹ • ofHom g
  have hleft : comp w z = id M := by
    change comp ((c ^ k)⁻¹ • ofHom g) z = id M
    rw [hz, smul_comp, comp_smul, ← ofHom_comp, hgf, ofHom_scalarHom,
      map_pow, smul_smul, smul_smul, mul_assoc]
    change ((c ^ k)⁻¹ * ((c ^ n)⁻¹ * c ^ (n + k))) • id M = _
    rw [hc, one_smul]
  have hright : comp z w = id N := by
    change comp z ((c ^ k)⁻¹ • ofHom g) = id N
    rw [hz, smul_comp, comp_smul, ← ofHom_comp, hfg, ofHom_scalarHom,
      map_pow, smul_smul, smul_smul, mul_assoc]
    change ((c ^ n)⁻¹ * ((c ^ k)⁻¹ * c ^ (n + k))) • id N = _
    rw [mul_left_comm, hc, one_smul]
  exact ⟨⟨z, w, hleft, hright⟩, rfl, ⟨ofDenominator π hπ k g hg⟩⟩

/-- The actual invertible tensor associated to a global scalar-denominator presentation. -/
def toQuasiIsogeny (P : ScalarIsogenyPresentation π z)
    (hπ : algebraMap O F π ≠ 0) (hM : M.IsPiDivisible π) (hN : N.IsPiDivisible π) :
    QuasiIsogeny F M N := (P.exists_quasiIsogeny hπ hM hN).choose

@[simp]
theorem toQuasiIsogeny_hom (P : ScalarIsogenyPresentation π z)
    (hπ : algebraMap O F π ≠ 0) (hM : M.IsPiDivisible π) (hN : N.IsPiDivisible π) :
    (P.toQuasiIsogeny hπ hM hN).hom = z := (P.exists_quasiIsogeny hπ hM hN).choose_spec.1

/-- The chosen inverse in the tensor Hom has a global scalar-denominator presentation. -/
def inversePresentation (P : ScalarIsogenyPresentation π z)
    (hπ : algebraMap O F π ≠ 0) (hM : M.IsPiDivisible π) (hN : N.IsPiDivisible π) :
    ScalarIsogenyPresentation π (P.toQuasiIsogeny hπ hM hN).inv :=
  Classical.choice (P.exists_quasiIsogeny hπ hM hN).choose_spec.2

/-- The two actual rational sections furnished by the tensor and the local construction agree. -/
theorem toSectionIso_toLocalQuasiIsogeny (P : ScalarIsogenyPresentation π z)
    (hπ : algebraMap O F π ≠ 0) (hM : M.IsPiDivisible π) (hN : N.IsPiDivisible π) :
    (P.toLocalQuasiIsogeny hπ hM hN).toSectionIso =
      RationalSectionIso.ofQuasiIsogeny (P.toQuasiIsogeny hπ hM hN) ⊤ := by
  apply RationalSectionIso.ext
  change (P.toLocalQuasiIsogeny hπ hM hN).toSectionIso.hom =
    RationalSection.ofGlobalOn ⊤ (P.toQuasiIsogeny hπ hM hN).hom
  rw [LocalQuasiIsogeny.toSectionIso_hom, toQuasiIsogeny_hom, RationalSection.ofGlobalOn_top]
  rfl

/-- The global presented inverse maps to the actual inverse local quasi-isogeny. -/
theorem toLocalQuasiIsogeny_inversePresentation (P : ScalarIsogenyPresentation π z)
    (hπ : algebraMap O F π ≠ 0) (hM : M.IsPiDivisible π) (hN : N.IsPiDivisible π) :
    (P.inversePresentation hπ hM hN).toLocalQuasiIsogeny hπ hN hM =
      (P.toLocalQuasiIsogeny hπ hM hN).inv := by
  apply LocalQuasiIsogeny.ext
  change RationalSection.ofGlobal (P.toQuasiIsogeny hπ hM hN).inv =
    (P.toLocalQuasiIsogeny hπ hM hN).toSectionIso.inv
  rw [toSectionIso_toLocalQuasiIsogeny]
  rfl

end ScalarIsogenyPresentation
end RationalHom
end Langlands.FormalGroup.ModuleLaw
