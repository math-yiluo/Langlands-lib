import Langlands.Representation.Archimedean.TransposePairing
import Langlands.Representation.Archimedean.ComplexReverseIntertwinerTied
import Langlands.Representation.Archimedean.ComplexContragredientProof

/-! # Inverse-transpose duality of complex standard modules -/

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped TensorProduct Matrix MonoidAlgebra

namespace Langlands.Archimedean.ComplexTransposeStandardDuality

attribute [local instance 100] LieRing.ofAssociativeRing

open Langlands.GeneralLinear Langlands.LocalFactor.Archimedean ComplexDuality
  ComplexReverseTwist ComplexStandardHomTransposeProof KFiniteDual

abbrev Standard (n : ℕ) (ds : List ComplexCharacterData) :=
  kFiniteFunctions (complexStandardModule n ds) (unitaryCompact ℂ n)

abbrev Principal (n : ℕ) (χ : ℕ → ℂˣ → ℂ) :=
  kFiniteFunctions (principalSeries ℂ n χ) (unitaryCompact ℂ n)

variable {n : ℕ}

/-- Pointwise inverse characters, with the order unchanged. -/
lemma positionCharacter_map_inv : ∀ (ds : List ComplexCharacterData) (i : ℕ) (z : ℂˣ),
    complexPositionCharacter (ds.map complexCharacterDataInv) i z =
      (complexPositionCharacter ds i z)⁻¹
  | [], _, _ => by simp [complexPositionCharacter]
  | d :: _, 0, z => by
      change ((d.character z)⁻¹ : ℂˣ).val = (d.character z : ℂ)⁻¹
      exact Units.val_inv_eq_inv_val _
  | _ :: ds, i + 1, z => positionCharacter_map_inv ds i z

/-- Pullback by `g ↦ w₀ (gᵀ)⁻¹`, restricted to the compact-finite principal series. -/
def twistEquiv {χ χ' : ℕ → ℂˣ → ℂ}
    (hχ : ∀ (j : Fin n) (z : ℂˣ), χ' j z = χ (Fin.rev j) z⁻¹) :
    Principal n χ ≃ₗ[ℂ] Principal n χ' where
  toFun f := ⟨twistLin n f, twistLin_mem_kFiniteFunctions hχ f.2⟩
  invFun f := ⟨twistLin n f, twistLin_mem_kFiniteFunctions
    (fun j z => by simpa only [Fin.rev_rev, inv_inv] using (hχ (Fin.rev j) z⁻¹).symm) f.2⟩
  left_inv f := Subtype.ext (twistLin_twistLin (f : Langlands.GeneralLinear n ℂ → ℂ))
  right_inv f := Subtype.ext (twistLin_twistLin (f : Langlands.GeneralLinear n ℂ → ℂ))
  map_add' f g := Subtype.ext (map_add (twistLin n) (f : Langlands.GeneralLinear n ℂ → ℂ) (g : Langlands.GeneralLinear n ℂ → ℂ))
  map_smul' c f := Subtype.ext (map_smul (twistLin n) c (f : Langlands.GeneralLinear n ℂ → ℂ))

@[simp]
lemma twistEquiv_apply {χ χ' : ℕ → ℂˣ → ℂ}
    (hχ : ∀ (j : Fin n) (z : ℂˣ), χ' j z = χ (Fin.rev j) z⁻¹)
    (f : Principal n χ) (g : Langlands.GeneralLinear n ℂ) :
    (twistEquiv hχ f : Langlands.GeneralLinear n ℂ → ℂ) g =
      (f : Langlands.GeneralLinear n ℂ → ℂ) (ComplexReverseTwist.twist g) := rfl

lemma toUnits_compactIota (k : Matrix.unitaryGroup (Fin n) ℂ) :
    Unitary.toUnits (compactIota ℂ n k) = conjAut (Unitary.toUnits k) := Units.ext rfl

lemma twistEquiv_rep {χ χ' : ℕ → ℂˣ → ℂ}
    (hχ : ∀ (j : Fin n) (z : ℂˣ), χ' j z = χ (Fin.rev j) z⁻¹)
    (k : Matrix.unitaryGroup (Fin n) ℂ) (f : Principal n χ) :
    twistEquiv hχ (principalSeriesRep ℂ n χ (compactIota ℂ n k) f) =
      principalSeriesRep ℂ n χ' k (twistEquiv hχ f) := by
  apply Subtype.ext
  change twistLin n (principalSeriesRep ℂ n χ (compactIota ℂ n k) f :
      Langlands.GeneralLinear n ℂ → ℂ) =
    (principalSeriesRep ℂ n χ' k (twistEquiv hχ f) : Langlands.GeneralLinear n ℂ → ℂ)
  rw [principalSeriesRep_apply_coe, principalSeriesRep_apply_coe, toUnits_compactIota]
  exact (rightTranslation_twistLin (f : Langlands.GeneralLinear n ℂ → ℂ)
    (Unitary.toUnits k)).symm

lemma twistEquiv_lie_one_tmul {χ χ' : ℕ → ℂˣ → ℂ}
    (hχ : ∀ (j : Fin n) (z : ℂˣ), χ' j z = χ (Fin.rev j) z⁻¹)
    (X : Matrix (Fin n) (Fin n) ℂ) (f : Principal n χ) :
    twistEquiv hχ (principalSeriesLie ℂ n χ (1 ⊗ₜ[ℝ] (-X.transpose)) f) =
      principalSeriesLie ℂ n χ' (1 ⊗ₜ[ℝ] X) (twistEquiv hχ f) := by
  apply Subtype.ext
  funext g
  change (principalSeriesLie ℂ n χ (1 ⊗ₜ[ℝ] (-X.transpose)) f :
      Langlands.GeneralLinear n ℂ → ℂ) (ComplexReverseTwist.twist g) = _
  rw [principalSeriesLie_one_tmul_apply_coe, principalSeriesLie_one_tmul_apply_coe]
  exact (ComplexReverseIntertwinerTied.rightDerivative_twistLin f.2.1.1 X g).symm

lemma twistEquiv_lie {χ χ' : ℕ → ℂˣ → ℂ}
    (hχ : ∀ (j : Fin n) (z : ℂˣ), χ' j z = χ (Fin.rev j) z⁻¹)
    (X : ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℂ) (f : Principal n χ) :
    twistEquiv hχ (principalSeriesLie ℂ n χ (complexifiedMatrixLieIota ℂ n X) f) =
      principalSeriesLie ℂ n χ' X (twistEquiv hχ f) := by
  induction X using TensorProduct.inductionOn with
  | tmul c X =>
    rw [complexifiedMatrixLieIota_tmul]
    have ht (Y : Matrix (Fin n) (Fin n) ℂ) :
        (c ⊗ₜ[ℝ] Y : ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℂ) = c • (1 ⊗ₜ[ℝ] Y) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [ht, ht, map_smul, map_smul, LinearMap.smul_apply, LinearMap.smul_apply,
      map_smul, twistEquiv_lie_one_tmul]
  | add X Y hX hY => simp only [map_add, LinearMap.add_apply, hX, hY]

/-- The integration map from the inverse-character standard module to the algebraic dual. -/
def inversePairing (n : ℕ) (ds : List ComplexCharacterData) :
    Standard n (ds.map complexCharacterDataInv) →ₗ[ℂ] Module.Dual ℂ (Standard n ds) :=
  integralPairing n (complexPositionCharacter (ds.map complexCharacterDataInv))
    (complexPositionCharacter ds)

lemma inversePairing_rep (ds : List ComplexCharacterData)
    (k : Matrix.unitaryGroup (Fin n) ℂ) (f : Standard n (ds.map complexCharacterDataInv)) :
    inversePairing n ds (complexStandardRep n (ds.map complexCharacterDataInv) k f) =
      (complexStandardRep n ds).dual k (inversePairing n ds f) := by
  ext g
  rw [dual_apply_apply]
  have h := integralPairing_principalSeriesRep
    (complexPositionCharacter (ds.map complexCharacterDataInv)) (complexPositionCharacter ds)
    k f (complexStandardRep n ds k⁻¹ g)
  rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply] at h
  exact h

lemma inversePairing_finite (ds : List ComplexCharacterData)
    (f : Standard n (ds.map complexCharacterDataInv)) :
    FiniteVectors.IsFiniteVector (complexStandardRep n ds).dual (inversePairing n ds f) :=
  isFiniteVector_dual_of_equivariant (inversePairing n ds) (inversePairing_rep ds)
    ((isComplexGKModule_complexStandardModule n (ds.map complexCharacterDataInv)).1 f)

lemma inversePairing_injective (ds : List ComplexCharacterData) :
    Function.Injective (inversePairing n ds) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro f hf
  by_contra hne
  obtain ⟨s, hs⟩ := exists_normSq_complexPositionCharacter ds
  obtain ⟨g, hg⟩ := exists_integralPairing_ne_zero_right
    (complexPositionCharacter_map_inv_mul ds) hs f hne
  exact hg (by change inversePairing n ds f g = 0; rw [hf, LinearMap.zero_apply])

lemma inversePairing_surjective (ds : List ComplexCharacterData)
    (ℓ : kDual (complexStandardRep n ds)) :
    ∃ f : Standard n (ds.map complexCharacterDataInv), inversePairing n ds f = ℓ := by
  have hgk := isComplexGKModule_complexStandardModule n ds
  have : IsSemisimpleModule ℂ[Matrix.unitaryGroup (Fin n) ℂ]
      (complexStandardRep n ds).asModule := KFiniteDual.isSemisimpleModule hgk.1 hgk.2.1
  have hblock := KFiniteDual.finiteDimensional_block hgk.1 hgk.2.1
    (isAdmissibleGKModule_principalSeriesRep (n := n) (complexPositionCharacter ds))
  let W : Subrepresentation (complexStandardRep n ds).dual :=
    { toSubmodule := LinearMap.range (inversePairing n ds)
      apply_mem_toSubmodule := by
        rintro k _ ⟨f, rfl⟩
        exact ⟨complexStandardRep n (ds.map complexCharacterDataInv) k f,
          inversePairing_rep ds k f⟩ }
  have hfin : ∀ w ∈ W, FiniteVectors.IsFiniteVector (complexStandardRep n ds).dual w := by
    rintro _ ⟨f, rfl⟩
    exact inversePairing_finite ds f
  have hsep : ∀ g : Standard n ds, (∀ w ∈ W, w g = 0) → g = 0 := by
    intro g hg
    by_contra hne
    obtain ⟨s, hs⟩ := exists_normSq_complexPositionCharacter (ds.map complexCharacterDataInv)
    obtain ⟨f, hf⟩ := exists_integralPairing_ne_zero_left
      (complexPositionCharacter_map_inv_mul ds) hs g hne
    exact hf (hg _ ⟨f, rfl⟩)
  exact KFiniteDual.mem_of_separating hblock W hfin hsep ℓ.2

/-- The compact-finite dual of the actual standard module is the inverse-character module. -/
def dualEquiv (n : ℕ) (ds : List ComplexCharacterData) :
    Standard n (ds.map complexCharacterDataInv) ≃ₗ[ℂ] kDual (complexStandardRep n ds) :=
  LinearEquiv.ofBijective
    ((inversePairing n ds).codRestrict (kDual (complexStandardRep n ds))
      (inversePairing_finite ds))
    ⟨fun f g h => inversePairing_injective ds (congrArg Subtype.val h), fun ℓ => by
      obtain ⟨f, hf⟩ := inversePairing_surjective ds ℓ
      exact ⟨f, Subtype.ext hf⟩⟩

@[simp]
lemma dualEquiv_apply (ds : List ComplexCharacterData)
    (f : Standard n (ds.map complexCharacterDataInv)) :
    (dualEquiv n ds f : Module.Dual ℂ (Standard n ds)) = inversePairing n ds f := rfl

lemma dualEquiv_rep (ds : List ComplexCharacterData)
    (k : Matrix.unitaryGroup (Fin n) ℂ) (f : Standard n (ds.map complexCharacterDataInv)) :
    dualEquiv n ds (complexStandardRep n (ds.map complexCharacterDataInv) k f) =
      kDualRep (complexStandardRep n ds) k (dualEquiv n ds f) :=
  Subtype.ext (inversePairing_rep ds k f)

lemma inversePairing_lie (ds : List ComplexCharacterData)
    (X : ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℂ)
    (f : Standard n (ds.map complexCharacterDataInv)) (g : Standard n ds) :
    inversePairing n ds (complexStandardLie n (ds.map complexCharacterDataInv) X f) g +
      inversePairing n ds f (complexStandardLie n ds X g) = 0 := by
  induction X using TensorProduct.inductionOn with
  | tmul c X =>
    have ht : (c ⊗ₜ[ℝ] X : ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℂ) =
        c • (1 ⊗ₜ[ℝ] X) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [ht, map_smul, LinearMap.smul_apply, map_smul, LinearMap.smul_apply]
    change _ = _
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
    rw [← mul_add]
    have h := integralPairing_principalSeriesLie (complexPositionCharacter_map_inv_mul ds) X f g
    change inversePairing n ds _ g + inversePairing n ds f _ = 0 at h
    rw [h, mul_zero]
  | add X Y hX hY =>
    simp only [map_add, LinearMap.add_apply]
    linear_combination hX + hY

lemma dualEquiv_lie (ds : List ComplexCharacterData)
    (X : ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℂ)
    (f : Standard n (ds.map complexCharacterDataInv)) :
    dualEquiv n ds (complexStandardLie n (ds.map complexCharacterDataInv) X f) =
      ComplexContragredient.dualLie (isComplexGKModule_complexStandardModule n ds) X
        (dualEquiv n ds f) := by
  apply Subtype.ext
  ext g
  change inversePairing n ds (complexStandardLie n (ds.map complexCharacterDataInv) X f) g =
    -inversePairing n ds f (complexStandardLie n ds X g)
  exact eq_neg_of_add_eq_zero_left (inversePairing_lie ds X f g)

lemma reverse_inverse_character (ds : List ComplexCharacterData) (hn : ds.length = n)
    (j : Fin n) (z : ℂˣ) :
    complexPositionCharacter (ds.map complexCharacterDataInv) j z =
      complexPositionCharacter ds.reverse (Fin.rev j) z⁻¹ := by
  rw [positionCharacter_map_inv,
    ComplexReverseIntertwinerStrict.complexPositionCharacter_reverse hn,
    ComplexReverseIntertwinerStrict.complexPositionCharacter_inv]

/-- Reversing a standard-module list realizes the inverse-transpose twist of its finite dual. -/
def transposeDualEquiv (n : ℕ) (ds : List ComplexCharacterData) (hn : ds.length = n) :
    Standard n ds.reverse ≃ₗ[ℂ] kDual (complexStandardRep n ds) :=
  (twistEquiv (reverse_inverse_character ds hn)).trans (dualEquiv n ds)

lemma transposeDualEquiv_rep (ds : List ComplexCharacterData) (hn : ds.length = n)
    (k : Matrix.unitaryGroup (Fin n) ℂ) (f : Standard n ds.reverse) :
    transposeDualEquiv n ds hn (complexStandardRep n ds.reverse k f) =
      kDualRep (complexStandardRep n ds) (compactIota ℂ n k)
        (transposeDualEquiv n ds hn f) := by
  change dualEquiv n ds (twistEquiv _ (complexStandardRep n ds.reverse k f)) = _
  rw [← compactIota_involutive ℂ n k, twistEquiv_rep, dualEquiv_rep]
  simp only [compactIota_involutive]
  rfl

lemma transposeDualEquiv_lie (ds : List ComplexCharacterData) (hn : ds.length = n)
    (X : ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℂ) (f : Standard n ds.reverse) :
    transposeDualEquiv n ds hn (complexStandardLie n ds.reverse X f) =
      ComplexContragredient.dualLie (isComplexGKModule_complexStandardModule n ds)
        (complexifiedMatrixLieIota ℂ n X) (transposeDualEquiv n ds hn f) := by
  change dualEquiv n ds (twistEquiv _ (complexStandardLie n ds.reverse X f)) = _
  rw [← complexifiedMatrixLieIota_involutive ℂ n X, twistEquiv_lie, dualEquiv_lie]
  simp only [complexifiedMatrixLieIota_involutive]
  rfl

end Langlands.Archimedean.ComplexTransposeStandardDuality
