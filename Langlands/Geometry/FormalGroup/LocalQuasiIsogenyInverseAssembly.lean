import Langlands.Geometry.FormalGroup.RationalSectionIsoGluing
import Langlands.Geometry.FormalGroup.LocalQuasiIsogenyInverseStatement

/-! # Local inverse assembly from integral scalar-power duals -/

noncomputable section
universe u v
namespace Langlands.FormalGroup.ModuleLaw
open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry
attribute [local instance] coefficientAlgebra coefficientScalarTower

variable {O : Type u} [CommRing O]
variable {R : Type v} [CommRing R] [Algebra O R]
variable {F : Type v} [Field F] [Algebra O F]
variable {σ τ : Type} [Finite σ] [Finite τ]
variable {M : ModuleLaw O R σ} {N : ModuleLaw O R τ}
variable {U : Opens (PrimeSpectrum R)}

namespace RationalSection

/-- Integral scalar multiplication agrees with multiplication by the image
of that scalar in the rational coefficient field. -/
@[simp]
theorem ofIntegral_smul (a : O) (f : OpenIntegralHom M N U) :
    ofIntegral U (a • f) =
      (algebraMap O F a) • (ofIntegral U f : RationalSection F M N U) := by
  change ofRational U (RationalHom.ofHom (a • f)) = _
  rw [map_smul, ← IsScalarTower.algebraMap_smul F a]
  erw [map_smul]
  rfl

/-- The actual scalar endomorphism gives the scalar multiple of the actual
identity section. -/
@[simp]
theorem ofIntegral_scalarHom (a : O) :
    ofIntegral U ((M.overAlgebra ((coefficientStructurePresheaf R).obj (op U))).scalarHom a) =
      (algebraMap O F a) • (id M U : RationalSection F M M U) := by
  rw [scalarHom, ofIntegral_smul]
  rfl

/-- A scalar-power denominator of an actual integral isogeny satisfies
the pointwise local scalar-isogeny condition. -/
theorem IsLocallyScalarIsogeny.inv_pow_smul_ofIntegral (π : O)
    (hc : algebraMap O F π ≠ 0) (n : ℕ)
    (f : OpenIntegralHom M N U) (hf : f.IsIsogeny) :
    IsLocallyScalarIsogeny π
      (((algebraMap O F π) ^ n)⁻¹ •
        (RationalSection.ofIntegral U f : RationalSection F M N U)) := by
  intro x hx
  refine ⟨U, hx, 𝟙 U, n, f, hf, ?_⟩
  rw [restrict_id, smul_smul, mul_inv_cancel₀ (pow_ne_zero n hc), one_smul]

end RationalSection

namespace RationalSectionIso

/-- Scalar-power dual integral isogenies give a two-sided inverse to an
actual section presented with a scalar-power denominator. -/
theorem exists_locallyScalar_of_integralDual (π : O)
    (hc : algebraMap O F π ≠ 0) (n k : ℕ)
    (z : RationalSection F M N U)
    (f : OpenIntegralHom M N U) (g : OpenIntegralHom N M U)
    (hg : g.IsIsogeny)
    (hz : (algebraMap O F π) ^ n • z = RationalSection.ofIntegral U f)
    (hgf : g.comp f =
      (M.overAlgebra ((coefficientStructurePresheaf R).obj (op U))).scalarHom (π ^ (n + k)))
    (hfg : f.comp g =
      (N.overAlgebra ((coefficientStructurePresheaf R).obj (op U))).scalarHom (π ^ (n + k))) :
    ∃ e : RationalSectionIso F M N U,
      e.hom = z ∧ RationalSection.IsLocallyScalarIsogeny π e.inv := by
  let c := algebraMap O F π
  have hcn : c ^ n ≠ 0 := pow_ne_zero n hc
  have hck : c ^ k ≠ 0 := pow_ne_zero k hc
  have hz' : z = (c ^ n)⁻¹ • RationalSection.ofIntegral U f := by
    rw [← hz, inv_smul_smul₀ hcn]
  have hsc : (c ^ k)⁻¹ * ((c ^ n)⁻¹ * c ^ (n + k)) = 1 := by
    rw [pow_add, inv_mul_cancel_left₀ hcn, inv_mul_cancel₀ hck]
  let w : RationalSection F N M U :=
    (c ^ k)⁻¹ • RationalSection.ofIntegral U g
  have hleft : RationalSection.comp w z = RationalSection.id M U := by
    rw [show w = (c ^ k)⁻¹ • RationalSection.ofIntegral U g from rfl,
      hz', RationalSection.smul_comp, RationalSection.comp_smul,
      RationalSection.comp_ofIntegral, hgf, RationalSection.ofIntegral_scalarHom,
      map_pow, smul_smul, smul_smul, mul_assoc]
    change ((c ^ k)⁻¹ * ((c ^ n)⁻¹ * c ^ (n + k))) •
      RationalSection.id M U = _
    rw [hsc, one_smul]
  have hright : RationalSection.comp z w = RationalSection.id N U := by
    rw [hz', show w = (c ^ k)⁻¹ • RationalSection.ofIntegral U g from rfl,
      RationalSection.smul_comp, RationalSection.comp_smul,
      RationalSection.comp_ofIntegral, hfg, RationalSection.ofIntegral_scalarHom,
      map_pow, smul_smul, smul_smul, mul_assoc]
    have hsc' : (c ^ n)⁻¹ * ((c ^ k)⁻¹ * c ^ (n + k)) = 1 := by
      rw [mul_left_comm, hsc]
    change ((c ^ n)⁻¹ * ((c ^ k)⁻¹ * c ^ (n + k))) •
      RationalSection.id N U = _
    rw [hsc', one_smul]
  exact ⟨⟨z, w, hleft, hright⟩, rfl,
    RationalSection.IsLocallyScalarIsogeny.inv_pow_smul_ofIntegral π hc k g hg⟩

end RationalSectionIso

/-- The eventual integral scalar-power dual theorem over the actual open
section algebras implies the complete published inverse-section target. -/
theorem localQuasiIsogenyInverse_of_integralDuals (π : O)
    (hdual : ∀ (V : Opens (PrimeSpectrum R)),
      (M.overAlgebra ((coefficientStructurePresheaf R).obj (op V))).IsPiDivisible π →
      (N.overAlgebra ((coefficientStructurePresheaf R).obj (op V))).IsPiDivisible π →
      ∀ (f : OpenIntegralHom M N V), f.IsIsogeny →
        ∃ j₀ : ℕ, ∀ j, j₀ ≤ j → ∃ g : OpenIntegralHom N M V,
          g.IsIsogeny ∧
          g.comp f =
            (M.overAlgebra ((coefficientStructurePresheaf R).obj (op V))).scalarHom (π ^ j) ∧
          f.comp g =
            (N.overAlgebra ((coefficientStructurePresheaf R).obj (op V))).scalarHom (π ^ j)) :
    LocalQuasiIsogenyInverseStatement F π M N := by
  intro U z
  apply RationalSectionIso.existsUnique_locallyScalar_of_locally π z.val
  intro x hx
  obtain ⟨V, hxV, i, n, f, hf, heq⟩ := z.isLocal x hx
  obtain ⟨j₀, hj₀⟩ := hdual V
    (z.source_divisible.map (IsScalarTower.toAlgHom O R _))
    (z.target_divisible.map (IsScalarTower.toAlgHom O R _)) f hf
  obtain ⟨g, hg, hgf, hfg⟩ := hj₀ (max j₀ n) (le_max_left _ _)
  have hj : n + (max j₀ n - n) = max j₀ n :=
    Nat.add_sub_of_le (le_max_right _ _)
  obtain ⟨e, he, hl⟩ := RationalSectionIso.exists_locallyScalar_of_integralDual π
    z.scalar_ne_zero n (max j₀ n - n) (RationalSection.restrict i z.val) f g hg heq
    (by simpa only [hj] using hgf) (by simpa only [hj] using hfg)
  exact ⟨V, hxV, i, e, he, hl⟩

end Langlands.FormalGroup.ModuleLaw
