import Langlands.ClassFieldTheory.Local.IntermediateReciprocityTransport
import Langlands.LocalFactor.Ramification.Herbrand.KummerStepUpperSupProof
import Langlands.LocalFactor.Ramification.Herbrand.KummerTruncationProof

/-! # Upper ramification transitivity at every finite stage of a Kummer tower -/

noncomputable section

namespace Langlands.Ramification.Kummer

open LocalClassField Polynomial Weil.Local
open _root_.Langlands.Ramification.HerbrandBridge
open _root_.Langlands.Ramification.Padic

universe u

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{u} p)

private abbrev stageRoot (πs : ℕ → AlgebraicClosure F.Carrier) (n : ℕ) :
    (kummerStage F πs n).field :=
  IntermediateField.AdjoinSimple.gen F.Carrier (πs n)

private theorem stageRoot_pow {ϖ : F.Carrier} {πs : ℕ → AlgebraicClosure F.Carrier}
    (hπ : IsKummerRootSystem F ϖ πs) (n : ℕ) :
    πs n ^ (p ^ n) = algebraMap F.Carrier (AlgebraicClosure F.Carrier) ϖ := by
  induction n with
  | zero => simpa only [pow_zero, pow_one] using hπ.2.1
  | succ n ih =>
    rw [pow_succ' p n, pow_mul, hπ.2.2 n, ih]

/-- The order of the stage generator and the absolute ramification index of
the stage follow from the degree bound and restriction of normalized orders. -/
private theorem stageRoot_ord_and_ramificationIndex
    {ϖ : F.Carrier} {πs : ℕ → AlgebraicClosure F.Carrier}
    (hπ : IsKummerRootSystem F ϖ πs) (n : ℕ) :
    let K := (kummerStage F πs n).asPadicField (p := p)
    K.canonicalTopologicalData.ord (stageRoot F πs n) = 1 ∧
      K.canonicalTopologicalData.ramificationIndex =
        p ^ n * F.canonicalTopologicalData.ramificationIndex := by
  let K := (kummerStage F πs n).asPadicField (p := p)
  let := K.algebra
  let : IsScalarTower (Padic p) F.Carrier K.Carrier := IsScalarTower.of_algebraMap_eq' rfl
  let β : K.Carrier := stageRoot F πs n
  let T := F.canonicalTopologicalData
  let S := K.canonicalTopologicalData
  have hp : 0 < p ^ n := pow_pos (Fact.out : p.Prime).pos n
  have hpow := stageRoot_pow F hπ n
  have hdeg : Module.finrank F.Carrier K.Carrier ≤ p ^ n := by
    change Module.finrank F.Carrier (IntermediateField.adjoin F.Carrier {πs n}) ≤ p ^ n
    rw [IntermediateField.adjoin.finrank (Algebra.IsIntegral.isIntegral (R := F.Carrier) (πs n))]
    have hroot : aeval (πs n) (X ^ (p ^ n) - C ϖ) = 0 := by
      simpa only [map_sub, map_pow, aeval_X, aeval_C] using sub_eq_zero.mpr hpow
    calc
      _ ≤ (X ^ (p ^ n) - C ϖ).natDegree :=
        natDegree_le_of_dvd (minpoly.dvd F.Carrier (πs n) hroot)
          (monic_X_pow_sub_C ϖ hp.ne').ne_zero
      _ = _ := natDegree_X_pow_sub_C
  let f := IsScalarTower.toAlgHom (Padic p) F.Carrier K.Carrier
  have hdegreeIdentity := PadicField.ramificationIndex_mul_extensionResidueDegree F K f
  rw [extensionDegree_suppliedAlgebra] at hdegreeIdentity
  have hbound : S.ramificationIndex ≤ p ^ n * T.ramificationIndex := calc
    _ ≤ S.ramificationIndex * extensionResidueDegree F K f :=
      Nat.le_mul_of_pos_right _ (extensionResidueDegree_pos F K f)
    _ = Module.finrank F.Carrier K.Carrier * T.ramificationIndex := hdegreeIdentity
    _ ≤ _ := Nat.mul_le_mul_right _ hdeg
  have hpowK : β ^ (p ^ n) = algebraMap F.Carrier K.Carrier ϖ := Subtype.ext hpow
  have hord := ramificationIndex_mul_ord_relative_algebraMap F K T S ϖ
  rw [← hpowK, ord_pow, hπ.1, mul_one, ← mul_assoc] at hord
  have hfactor : 0 < (T.ramificationIndex : ℤ) * ((p ^ n : ℕ) : ℤ) :=
    mul_pos (by exact_mod_cast T.ramificationIndex_pos) (by exact_mod_cast hp)
  have hpos : 0 < S.ord β := by
    apply (mul_pos_iff_of_pos_left hfactor).mp
    rw [hord]
    exact_mod_cast S.ramificationIndex_pos
  have hle : S.ord β ≤ 1 := by
    apply (mul_le_mul_iff_right₀ hfactor).mp
    rw [hord, mul_one, mul_comm]
    exact_mod_cast hbound
  have hβ : S.ord β = 1 := by omega
  refine ⟨hβ, ?_⟩
  rw [hβ, mul_one, mul_comm] at hord
  exact_mod_cast hord.symm

/-- Each finite stage of a compatible system of uniformizer roots is
transitive under the absolute upper groups up to the first Kummer break. -/
theorem kummerTowerUpperSup : KummerTowerUpperSupStatement.{u} := by
  intro p hp F ϖ πs hπ n v hv hmax
  induction n with
  | zero =>
    have hfix : (kummerStage F πs 0).field.fixingSubgroup = ⊤ := by
      apply top_unique
      intro σ _
      apply (mem_adjoin_fixingSubgroup_iff F (πs 0) σ).mpr
      rw [hπ.2.1]
      exact σ.commutes ϖ
    rw [hfix]
    exact top_sup_eq (absoluteUpperRamificationGroup F v)
  | succ n ih =>
    let E := kummerStage F πs n
    let K := E.asPadicField (p := p)
    let β : K.Carrier := stageRoot F πs n
    let e := intermediateClosureEquiv F E
    let α := e.symm (πs (n + 1))
    obtain ⟨hβ, hindex⟩ := stageRoot_ord_and_ramificationIndex F hπ n
    change K.canonicalTopologicalData.ramificationIndex = _ at hindex
    have hα : α ^ p = algebraMap K.Carrier (AlgebraicClosure K.Carrier) β := by
      apply e.injective
      rw [map_pow, AlgEquiv.apply_symm_apply, hπ.2.2 n, e.commutes]
      rfl
    have hindex_le : F.canonicalTopologicalData.ramificationIndex ≤
        K.canonicalTopologicalData.ramificationIndex := by
      rw [hindex]
      exact Nat.le_mul_of_pos_left _ (pow_pos (Fact.out : p.Prime).pos _)
    have hbreak : kummerBreak F ≤ kummerBreak K := by
      unfold kummerBreak
      have hp₁ : (1 : ℝ) ≤ p := by exact_mod_cast (Fact.out : p.Prime).one_lt.le
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left (by exact_mod_cast hindex_le) (Nat.cast_nonneg p))
        (sub_nonneg.mpr hp₁)
    have hpsi := herbrandPsiTruncation p F E v ih v hv le_rfl
    let stepFixing : Subgroup (Field.absoluteGaloisGroup E.field) :=
      (adjoinFiniteIntermediate K α).field.fixingSubgroup
    let stepUpper : Subgroup (Field.absoluteGaloisGroup E.field) :=
      absoluteUpperRamificationGroup K v
    have hstep : stepFixing ⊔ stepUpper = ⊤ :=
      kummerStepUpperSup p K β α hβ hα v hv (hmax.trans hbreak)
    let f := (intermediateGaloisMap F E).toMonoidHom
    let fixing : Subgroup (Field.absoluteGaloisGroup F.Carrier) := E.field.fixingSubgroup
    let nextFixing : Subgroup (Field.absoluteGaloisGroup F.Carrier) :=
      (kummerStage F πs (n + 1)).field.fixingSubgroup
    let upper := absoluteUpperRamificationGroup F v
    have hfix : stepFixing.map f ≤ nextFixing := by
      rintro σ ⟨τ, hτ, rfl⟩
      apply (mem_adjoin_fixingSubgroup_iff F (πs (n + 1)) _).mpr
      have hτ' : AlgEquiv.toAlgHom τ α = α := (mem_adjoin_fixingSubgroup_iff K α τ).mp hτ
      change AlgEquiv.toAlgHom (intermediateGaloisMap F E τ) (πs (n + 1)) = _
      rw [intermediateGaloisMap_apply]
      change e (AlgEquiv.toAlgHom τ α) = πs (n + 1)
      rw [hτ', AlgEquiv.apply_symm_apply]
    have hupper : stepUpper.map f ≤ upper := by
      rintro σ ⟨τ, hτ, rfl⟩
      apply (intermediateGaloisMap_mem_absoluteUpperRamificationGroup_iff E hv τ).mpr
      rw [hpsi]
      exact hτ
    have hE : fixing ≤ nextFixing ⊔ upper := calc
      fixing = (⊤ : Subgroup (Field.absoluteGaloisGroup E.field)).map f :=
        ((Subgroup.map_top f).trans (intermediateGaloisMap_range F E)).symm
      _ = (stepFixing ⊔ stepUpper).map f := congrArg (Subgroup.map f) hstep.symm
      _ = stepFixing.map f ⊔ stepUpper.map f := Subgroup.map_sup _ _ f
      _ ≤ _ := sup_le_sup hfix hupper
    change nextFixing ⊔ upper = ⊤
    apply top_unique
    calc
      ⊤ = fixing ⊔ upper := ih.symm
      _ ≤ _ := sup_le hE le_sup_right

end Langlands.Ramification.Kummer
