import Langlands.BaseChange.OrbitalIntegral
import Langlands.BaseChange.SatakeCharacterStatement
import Langlands.Group.GL.UnramifiedCharacter
import Langlands.LocalField.SmoothCharacterNormProof
import Langlands.Representation.Hecke.CharacterTwist
import Langlands.Representation.Unramified.EigenvalueScaling
import Langlands.Representation.Unramified.StandardHeckeSum
import Langlands.Representation.Unramified.StandardMonomialSupport
import Mathlib.RingTheory.RootsOfUnity.Complex

/-! # Determinant support of the unramified base-change map -/

noncomputable section

namespace Langlands.BaseChange

open Correspondence Langlands.Unramified Langlands.TraceFormula
open Langlands.QuotientIntegration MeasureTheory

universe u v

attribute [local instance] heckeFieldTopology heckeFieldValuativeRel heckeFieldLocalField
  heckeGeneralLinearTopology heckeGeneralLinearTopologicalGroup heckeGeneralLinearT2
  heckeGeneralLinearMeasurable heckeGeneralLinearBorel
attribute [local instance high] leftQuotientMeasurableSpace

section Twist

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{u} p) (r : ℕ)

private theorem determinantCharacter_spherical (z : ℂˣ) (k : sphericalOpenSubgroup F r) :
    F.canonicalTopologicalData.determinantUnramifiedCharacter (r + 1) z k = 1 := by
  let T := F.canonicalTopologicalData
  have hdet := (T.normalizedAbs_eq_one_iff_valuation_eq_one
    (GeneralLinear.determinant (k : GeneralLinear (r + 1) F.Carrier))).2
      (valuation_det_of_mem_spherical k.property)
  rw [T.determinantUnramifiedCharacter_apply,
    (T.ord_eq_zero_iff_normalizedAbs _).2 hdet, zpow_zero]

/-- The spherical algebra endomorphism given by the unramified determinant character
with uniformizer value `z`. -/
def determinantTwist (z : ℂˣ) : SphericalHeckeAlgebra F r →ₐ[ℂ] SphericalHeckeAlgebra F r :=
  Hecke.HeckeAlgebra.Corner.characterTwist (sphericalOpenSubgroup F r)
    (sphericalOpenSubgroup_isCompact F r) (sphericalHaar F r)
    (F.canonicalTopologicalData.determinantUnramifiedCharacter (r + 1) z)
    (determinantCharacter_spherical F r z)

@[simp]
theorem determinantTwist_apply (z : ℂˣ) (f : SphericalHeckeAlgebra F r)
    (g : GeneralLinear (r + 1) F.Carrier) :
    determinantTwist F r z f g =
      ((z ^ F.canonicalTopologicalData.ord (GeneralLinear.determinant g : F.Carrier) :
        ℂˣ) : ℂ) * f g := rfl

theorem determinantTwist_standardHeckeElement (z : ℂˣ) (i : Fin (r + 2)) :
    determinantTwist F r z (standardHeckeElement F r i) =
      (z : ℂ) ^ i.val • standardHeckeElement F r i := by
  let T := F.canonicalTopologicalData
  have hdet : GeneralLinear.determinant (standardDiagonal F r i) = T.uniformizerUnit ^ i.val := by
    apply Units.ext
    rw [standardDiagonal_eq_subsetTorus]
    change (MinusculeCosets.subsetTorus T.uniformizerUnit (initialSegment r i) :
      Matrix (Fin (r + 1)) (Fin (r + 1)) F.Carrier).det = _
    rw [MinusculeCosets.det_subsetTorus, card_initialSegment, Units.val_pow_eq_pow_val]
  have hχ : T.determinantUnramifiedCharacter (r + 1) z (standardDiagonal F r i) =
      z ^ i.val := by
    change T.unramifiedCharacter z (GeneralLinear.determinant (standardDiagonal F r i)) = _
    rw [hdet, map_pow, T.unramifiedCharacter_uniformizer]
  rw [determinantTwist, standardHeckeElement, Hecke.HeckeAlgebra.Corner.characterTwist_doubleCoset,
    hχ, Units.val_pow_eq_pow_val]

theorem IsSatakeCharacter.comp_determinantTwist {s : Eigenvalues (r + 1)}
    {ω : SphericalHeckeAlgebra F r →ₐ[ℂ] ℂ} (hω : IsSatakeCharacter F r s ω) (z : ℂˣ) :
    IsSatakeCharacter F r (Eigenvalues.scale z s) (ω.comp (determinantTwist F r z)) := by
  intro i
  rw [AlgHom.comp_apply, determinantTwist_standardHeckeElement, map_smul, smul_eq_mul, hω i,
    standardHeckeScalar_scale]

end Twist

section Support

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{u} p} {E : PadicField.{v} p} {l r : ℕ}
variable {b : SphericalHeckeAlgebra E r →ₐ[ℂ] SphericalHeckeAlgebra F r}

/-- The image of base change is fixed by the determinant twist of every `l`-th root of unity. -/
theorem IsUnramifiedBaseChangeHom.determinantTwist_eq (hb : IsUnramifiedBaseChangeHom F E l r b)
    (hSatakeF : SatakeCharacterStatement.{u}) (hSatakeE : SatakeCharacterStatement.{v})
    (φ : SphericalHeckeAlgebra E r) {z : ℂˣ} (hz : z ^ l = 1) :
    determinantTwist F r z (b φ) = b φ := by
  apply sub_eq_zero.mp
  apply (hSatakeF p F r).2
  intro s ω hω
  obtain ⟨η, hη⟩ := (hSatakeE p E r).1 (Eigenvalues.power s l)
  have hpow : Eigenvalues.power (Eigenvalues.scale z s) l = Eigenvalues.power s l := by
    rw [Eigenvalues.power_scale, hz, Eigenvalues.scale_one]
  have hη' : IsSatakeCharacter E r (Eigenvalues.power (Eigenvalues.scale z s) l) η :=
    hpow.symm ▸ hη
  have h₁ := DFunLike.congr_fun (hb s ω η hω hη) φ
  have h₂ := DFunLike.congr_fun
    (hb (Eigenvalues.scale z s) (ω.comp (determinantTwist F r z)) η
      (hω.comp_determinantTwist F r z) hη') φ
  rw [map_sub, sub_eq_zero]
  exact h₂.trans h₁.symm

private theorem exists_complexUnit_isPrimitiveRoot (hl : l ≠ 0) :
    ∃ z : ℂˣ, IsPrimitiveRoot z l := by
  have h := Complex.isPrimitiveRoot_exp l hl
  let z : ℂˣ := Units.mk0 _ (h.ne_zero hl)
  exact ⟨z, IsPrimitiveRoot.of_map_of_injective (f := Units.coeHom ℂ) h Units.val_injective⟩

/-- Base-changed functions vanish pointwise when the determinant order is outside `lℤ`. -/
theorem IsUnramifiedBaseChangeHom.apply_eq_zero_of_not_dvd_det
    (hb : IsUnramifiedBaseChangeHom F E l r b)
    (hSatakeF : SatakeCharacterStatement.{u}) (hSatakeE : SatakeCharacterStatement.{v})
    (hl : l ≠ 0) (φ : SphericalHeckeAlgebra E r) (g : GeneralLinear (r + 1) F.Carrier)
    (hg : ¬ (l : ℤ) ∣ F.canonicalTopologicalData.ord (GeneralLinear.determinant g : F.Carrier)) :
    b φ g = 0 := by
  obtain ⟨z, hz⟩ := exists_complexUnit_isPrimitiveRoot hl
  have h := congrArg (fun f : SphericalHeckeAlgebra F r => f g)
    (hb.determinantTwist_eq hSatakeF hSatakeE φ hz.pow_eq_one)
  change ((z ^ F.canonicalTopologicalData.ord (GeneralLinear.determinant g : F.Carrier) :
    ℂˣ) : ℂ) * b φ g = b φ g at h
  by_contra hne
  have he := mul_right_cancel₀ hne (h.trans (one_mul _).symm)
  exact hg ((hz.zpow_eq_one_iff_dvd _).1 (Units.val_injective he))

end Support

/-- The determinant-support branch of the fundamental lemma, from Satake existence
over the extension and separation over the base. -/
def DeterminantSupportReductionStatement : Prop :=
  SatakeCharacterStatement.{u} → SatakeCharacterStatement.{v} →
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{u} p) (E : PadicField.{v} p) (l r : ℕ),
    l ≠ 0 →
    ∀ (b : SphericalHeckeAlgebra E r →ₐ[ℂ] SphericalHeckeAlgebra F r),
      IsUnramifiedBaseChangeHom F E l r b →
      ∀ (φ : SphericalHeckeAlgebra E r) (γ : GeneralLinear (r + 1) F.Carrier),
        (¬ (l : ℤ) ∣ F.canonicalTopologicalData.ord (GeneralLinear.determinant γ : F.Carrier)) →
        ∀ (ν : Measure (LeftQuotient (glCentralizer γ))), orbitalIntegral γ ν ⇑(b φ) = 0

theorem determinantSupportReduction : DeterminantSupportReductionStatement.{u, v} := by
  intro hSatakeF hSatakeE p hp F E l r hl b hb φ γ hγ ν
  have hzero : twistedOrbitFunction (MonoidHom.id _) γ ⇑(b φ) = 0 := by
    funext q
    refine Quotient.inductionOn q fun x => ?_
    rw [twistedOrbitFunction_mk, MonoidHom.id_apply, Pi.zero_apply]
    apply hb.apply_eq_zero_of_not_dvd_det hSatakeF hSatakeE hl φ
    have hdet : GeneralLinear.determinant (x⁻¹ * γ * x) = GeneralLinear.determinant γ := by
      simp only [map_mul, map_inv]
      rw [mul_right_comm, inv_mul_cancel, one_mul]
    simpa only [hdet] using hγ
  rw [orbitalIntegral, twistedOrbitalIntegral, hzero]
  simp only [Pi.zero_apply, integral_zero]

end Langlands.BaseChange
