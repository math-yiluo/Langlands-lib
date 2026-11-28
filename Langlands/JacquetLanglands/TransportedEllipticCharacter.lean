import Langlands.Algebra.ReducedCharpolyRegularElements
import Langlands.BaseChange.CharacterLocalValueConjugation
import Langlands.BaseChange.EllipticCharacterCentralProduct
import Langlands.JacquetLanglands.RegularCorrespondentTopology

/-! # Transport of regular elliptic character values to the division algebra -/

noncomputable section

open scoped TensorProduct

namespace Langlands.JacquetLanglands

open Langlands.BaseChange Langlands.CentralSimple _root_.Polynomial
open SigmaLiftCharacterIdentity (coefficients)

universe u uV

section Correspondence

variable {F D : Type u} [Field F] [DivisionRing D] [Algebra F D]
  [FiniteDimensional F D] [Algebra.IsCentral F D] {n : ℕ}
  {g : GeneralLinear n F} {g' : Dˣ}

private theorem reducedCharpoly_conjugate (a g' : Dˣ) :
    reducedCharpoly F D (↑(a⁻¹ * g' * a) : D) = reducedCharpoly F D (g' : D) := by
  let L := finiteGaloisSplittingField F D
  let e := finiteGaloisSplittingChart F D
  let f := (e.toAlgHom.restrictScalars F).comp
    (Algebra.TensorProduct.includeRight (R := F) (A := L) (B := D))
  apply (Polynomial.map_injective (algebraMap F L) (algebraMap F L).injective)
  rw [reducedCharpoly_map_chart F D e, reducedCharpoly_map_chart F D e]
  let m := Units.map f.toMonoidHom
  change (m (a⁻¹ * g' * a)).val.charpoly = (m g').val.charpoly
  rw [map_mul, map_mul, map_inv]
  simp only [Units.val_mul, Matrix.coe_units_inv, Matrix.charpoly_units_conj']

/-- Conjugation in the division unit group preserves regularity. -/
theorem IsRegular.conjugate (h : IsRegular F D g') (a : Dˣ) :
    IsRegular F D (a⁻¹ * g' * a) := by
  unfold IsRegular at *
  rwa [reducedCharpoly_conjugate (F := F)]

/-- Conjugating the division unit preserves its correspondence with a split element. -/
theorem Corresponds.conjugate_division (h : Corresponds F D g g') (a : Dˣ) :
    Corresponds F D g (a⁻¹ * g' * a) :=
  ⟨h.1, h.2.1.conjugate a, h.2.2.trans (reducedCharpoly_conjugate (F := F) a g').symm⟩

/-- Multiplication by a nonzero central scalar preserves regularity. -/
theorem IsRegular.scalar_mul (h : IsRegular F D g') (z : Fˣ) :
    IsRegular F D (Units.map (algebraMap F D : F →* D) z * g') := by
  change (reducedCharpoly F D (algebraMap F D (z : F) * (g' : D))).Separable
  rw [← Algebra.smul_def]
  exact reducedCharpoly_separable_smul z.ne_zero h

variable [CharZero F]

/-- Multiplying both elements by the same nonzero scalar preserves correspondence. -/
theorem Corresponds.scalar_mul (h : Corresponds F D g g') (z : Fˣ) :
    Corresponds F D (GeneralLinear.scalar z * g)
      (Units.map (algebraMap F D : F →* D) z * g') := by
  have hz : (↑(Units.map (algebraMap F D : F →* D) z * g') : D) = (z : F) • (g' : D) :=
    (Algebra.smul_def _ _).symm
  have hp : (GeneralLinear.scalar z * g).val.charpoly =
      reducedCharpoly F D ((z : F) • (g' : D)) := by
    rw [reducedCharpoly_smul _ z.ne_zero, ← h.2.2, ← h.eq_reducedDegree]
    have : Infinite F := Infinite.of_injective (fun k : ℕ => (k : F)) Nat.cast_injective
    apply Polynomial.eq_of_infinite_eval_eq
    have he (x : F) : (GeneralLinear.scalar z * g).val.charpoly.eval x =
        (C ((z : F) ^ n) * g.val.charpoly.comp (C (↑z : F)⁻¹ * X)).eval x := by
      have hm : (GeneralLinear.scalar z * g).val = (z : F) • g.val := by
        change Matrix.scalar _ (z : F) * _ = _
        rw [Matrix.scalar_apply, Matrix.smul_eq_diagonal_mul]
      rw [hm, eval_mul, eval_C, eval_comp, eval_mul, eval_C, eval_X, Matrix.eval_charpoly,
        Matrix.eval_charpoly]
      have hdet := Matrix.det_smul (Matrix.scalar (Fin n) ((↑z : F)⁻¹ * x) - g.val) (z : F)
      rw [Fintype.card_fin, smul_sub] at hdet
      rw [← hdet]
      congr 1
      rw [Matrix.scalar_apply, Matrix.scalar_apply, ← Matrix.diagonal_smul]
      congr 1
      apply congrArg Matrix.diagonal
      funext i
      change x = (z : F) * ((z : F)⁻¹ * x)
      rw [← mul_assoc, mul_inv_cancel₀ z.ne_zero, one_mul]
    simpa only [he, Set.ofPred_true] using (Set.infinite_univ : (Set.univ : Set F).Infinite)
  refine ⟨isRegularElliptic_center_mul h.1 (GeneralLinear.scalarToCenter z), h.2.1.scalar_mul z, ?_⟩
  rw [hz]
  exact hp

end Correspondence

section Character

variable {F D : Type u} [Field F] [DivisionRing D] [Algebra F D]
  [FiniteDimensional F D] [Algebra.IsCentral F D] {n : ℕ}

local notation "E" => {g : GeneralLinear n F // IsRegularElliptic g}
local notation "R" => {g' : Dˣ // IsRegular F D g'}

private theorem exists_correspondent (hn : reducedDegree F D = n) (g' : R) :
    ∃ g : GeneralLinear n F, Corresponds F D g g'.val := by
  subst n
  exact exists_corresponds F D g' g'.property

variable (hn : reducedDegree F D = n)

/-- A function on the regular elliptic split elements read at chosen correspondents of
regular division units. Actual character values are independent of the choices. -/
def transportedEllipticCharacter (Θ : E → ℂ) (g' : R) : ℂ :=
  let h := exists_correspondent hn g'
  Θ ⟨h.choose, h.choose_spec.1⟩

variable [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

attribute [local instance] LocalFieldTopology.generalLinear_t2Space
  LocalFieldTopology.generalLinear_locallyCompactSpace
  LocalFieldTopology.generalLinear_totallyDisconnectedSpace

variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {ρ : Representation ℂ (GeneralLinear n F) V} {hρ : IsAdmissible ρ}
  {Θ : {g : GeneralLinear n F // IsRegularElliptic (F := F) (n := n) g} → ℂ}
  (hΘ : ∀ g : {g : GeneralLinear n F // IsRegularElliptic (F := F) (n := n) g},
    HasCharacterValue ρ hρ g.val (Θ g))

include hΘ

/-- The transported character has the same value at every choice of split correspondent. -/
theorem transportedEllipticCharacter_eq {g : GeneralLinear n F} {g' : Dˣ}
    (hg : Corresponds F D g g') :
    transportedEllipticCharacter (F := F) (D := D) hn Θ ⟨g', hg.2.1⟩ =
      Θ ⟨g, hg.1⟩ := by
  let h := exists_correspondent hn (⟨g', hg.2.1⟩ : R)
  have hp : h.choose.val.charpoly = g.val.charpoly := h.choose_spec.2.2.trans hg.2.2.symm
  have hc : coefficients h.choose = coefficients g :=
    funext fun i => congrArg (fun p : F[X] => p.coeff i) hp
  obtain ⟨a, ha⟩ := exists_conj_of_regular_coefficients_eq h.choose_spec.1.1 hc
  have hv := (hΘ ⟨h.choose, h.choose_spec.1⟩).conjugate a
  rw [ha] at hv
  exact hv.unique (hΘ ⟨g, hg.1⟩)

/-- The transported character is conjugation-invariant on regular division units. -/
theorem transportedEllipticCharacter_conjugate (g' : R) (a : Dˣ) :
    transportedEllipticCharacter hn Θ
      ⟨a⁻¹ * g'.val * a, g'.property.conjugate a⟩ =
      transportedEllipticCharacter hn Θ g' := by
  let h := exists_correspondent hn g'
  exact transportedEllipticCharacter_eq hn hΘ (h.choose_spec.conjugate_division a)

variable [CharZero F]

/-- The transported character transforms under the scalar action by the same character. -/
theorem transportedEllipticCharacter_scalar_mul (g' : R) (z : Fˣ) (c : ℂ)
    (hz : ∀ v, ρ (GeneralLinear.scalar z) v = c • v) :
    transportedEllipticCharacter hn Θ
      ⟨Units.map (algebraMap F D : F →* D) z * g'.val, g'.property.scalar_mul z⟩ =
      c * transportedEllipticCharacter hn Θ g' := by
  let h := exists_correspondent hn g'
  have hzg := h.choose_spec.scalar_mul z
  refine (transportedEllipticCharacter_eq hn hΘ hzg).trans ?_
  exact (hΘ ⟨_, hzg.1⟩).unique
    (hasCharacterValue_mul_left_of_scalar (hΘ ⟨h.choose, h.choose_spec.1⟩) hz)

variable [TopologicalSpace D] [IsModuleTopology F D]

/-- Local constancy of regular split character values persists under transport to the
regular division units. -/
theorem isLocallyConstant_transportedEllipticCharacter :
    IsLocallyConstant (transportedEllipticCharacter hn Θ) := by
  apply (IsLocallyConstant.iff_exists_open _).2
  intro g'
  obtain ⟨g, hg⟩ := exists_correspondent hn g'
  obtain ⟨U, hgU, s, hU, hs, hsg, hcorr⟩ :=
    exists_local_regularCorrespondent F D hg
  let t : U → E := fun a => ⟨s a, (hcorr a).1⟩
  have ht : Continuous t := hs.subtype_mk _
  obtain ⟨W, hW, hgW, hconst⟩ := (isLocallyConstant_of_hasCharacterValue hΘ).exists_open
    (t ⟨g'.val, hgU⟩)
  let V : Set R := Subtype.val ⁻¹' (Subtype.val '' (t ⁻¹' W))
  refine ⟨V, (hU.isOpenMap_subtype_val _ (hW.preimage ht)).preimage continuous_subtype_val,
    ⟨⟨g'.val, hgU⟩, hgW, rfl⟩, ?_⟩
  rintro a ⟨b, hb, hba⟩
  have ha : Corresponds F D (s b) a.val := hba ▸ hcorr b
  have hbase : t ⟨g'.val, hgU⟩ = ⟨g, hg.1⟩ := Subtype.ext hsg
  rw [transportedEllipticCharacter_eq hn hΘ ha, transportedEllipticCharacter_eq hn hΘ hg]
  exact (hconst (t b) hb).trans (congrArg Θ hbase)

end Character

end Langlands.JacquetLanglands
