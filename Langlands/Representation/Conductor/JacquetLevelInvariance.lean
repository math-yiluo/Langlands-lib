import Langlands.Representation.Conductor.MirabolicLevelGeneration
import Langlands.Representation.Conductor.NegativeLevelGeneration
import Langlands.Representation.Conductor.Definitions
import Langlands.Representation.Whittaker.Iwasawa

/-! # Jacquet group invariance in the actual field representation -/

noncomputable section

namespace Langlands.Conductor

open Matrix Langlands.GeneralLinear

universe uK uF uV

variable {F : Type uF} [Field F] {n : ℕ}

/-- The field image of the integral Jacquet group at an integral ideal level. -/
def fieldJacquetLevelMirabolic (O : Subring F) (n : ℕ) (I : Ideal O) :
    Subgroup (Langlands.GeneralLinear (n + 1) F) :=
  (integralJacquetMirabolic n I).map (GeneralLinearGroup.map O.subtype)

private theorem integral_map_mem_mirabolic_iff (O : Subring F)
    (g : Langlands.GeneralLinear (n + 1) O) :
    GeneralLinearGroup.map O.subtype g ∈ mirabolic n F ↔ g ∈ mirabolic n O := by
  change (∀ j, (g.val (Fin.last n) j : F) = if j = Fin.last n then 1 else 0) ↔
    (∀ j, g.val (Fin.last n) j = if j = Fin.last n then 1 else 0)
  constructor
  · intro hg j
    apply Subtype.val_injective
    simpa only [apply_ite, Subring.coe_one, Subring.coe_zero] using hg j
  · intro hg j
    simpa only [apply_ite, Subring.coe_one, Subring.coe_zero] using
      congrArg (fun a : O => (a : F)) (hg j)

private theorem integral_map_mem_oppositeMirabolic_iff (O : Subring F)
    (g : Langlands.GeneralLinear (n + 1) O) :
    GeneralLinearGroup.map O.subtype g ∈ oppositeMirabolic n F ↔
      g ∈ oppositeMirabolic n O := by
  change (∀ i, (g.val i (Fin.last n) : F) = if i = Fin.last n then 1 else 0) ↔
    (∀ i, g.val i (Fin.last n) = if i = Fin.last n then 1 else 0)
  constructor
  · intro hg i
    apply Subtype.val_injective
    simpa only [apply_ite, Subring.coe_one, Subring.coe_zero] using hg i
  · intro hg i
    simpa only [apply_ite, Subring.coe_one, Subring.coe_zero] using
      congrArg (fun a : O => (a : F)) (hg i)

/-- The level with unit ideal is the concrete field group `H(0)`. -/
@[simp] theorem fieldJacquetLevelMirabolic_top (O : Subring F) :
    fieldJacquetLevelMirabolic O n ⊤ = fieldJacquetMirabolic O n := by
  rw [fieldJacquetLevelMirabolic, integralJacquetMirabolic_top]
  ext g
  constructor
  · rintro ⟨gO, hgO, rfl⟩
    exact ⟨⟨gO, rfl⟩, (integral_map_mem_mirabolic_iff O gO).2 hgO⟩
  · rintro ⟨⟨gO, rfl⟩, hg⟩
    exact ⟨gO, (integral_map_mem_mirabolic_iff O gO).1 hg, rfl⟩

private theorem map_congruent_opposite (O : Subring F) (I : Ideal O) :
    (integralCongruence n I ⊓ oppositeMirabolic n O).map
        (GeneralLinearGroup.map O.subtype) =
      congruenceSubgroup O n I ⊓ oppositeMirabolic n F := by
  ext g
  constructor
  · rintro ⟨gO, ⟨hc, hp⟩, rfl⟩
    exact ⟨⟨gO, hc, rfl⟩, (integral_map_mem_oppositeMirabolic_iff O gO).2 hp⟩
  · rintro ⟨⟨gO, hc, rfl⟩, hp⟩
    exact ⟨gO, ⟨hc, (integral_map_mem_oppositeMirabolic_iff O gO).1 hp⟩, rfl⟩

private theorem integral_map_inverseTranspose (O : Subring F)
    (g : Langlands.GeneralLinear (n + 1) O) :
    GeneralLinearGroup.map O.subtype (inverseTranspose (n + 1) O g) =
      inverseTranspose (n + 1) F (GeneralLinearGroup.map O.subtype g) := by
  apply GeneralLinearGroup.ext
  intro i j
  simp only [GeneralLinearGroup.map_apply, inverseTranspose_entry, ← map_inv]

/-- In the field group the transpose Jacquet group is exactly the congruent
last-column mirabolic. Inverse transpose has the same subgroup image as transpose. -/
theorem fieldJacquetLevelMirabolic_map_inverseTranspose (O : Subring F) (I : Ideal O) :
    (fieldJacquetLevelMirabolic O n I).map
        (inverseTranspose (n + 1) F).toMonoidHom =
      congruenceSubgroup O n I ⊓ oppositeMirabolic n F := by
  rw [← map_congruent_opposite O I,
    ← integralJacquetMirabolic_map_inverseTranspose]
  ext g
  constructor
  · rintro ⟨_, ⟨gO, hgO, rfl⟩, rfl⟩
    exact ⟨_, ⟨gO, hgO, rfl⟩, integral_map_inverseTranspose O gO⟩
  · rintro ⟨_, ⟨gO, hgO, rfl⟩, rfl⟩
    exact ⟨_, ⟨gO, hgO, rfl⟩, (integral_map_inverseTranspose O gO).symm⟩

/-- The actual field Jacquet groups generate the actual field congruence subgroup. -/
theorem fieldJacquetMirabolic_sup_congruent_opposite (O : Subring F) [IsLocalRing O]
    (hn : 0 < n) (I : Ideal O) :
    fieldJacquetMirabolic O n ⊔ (congruenceSubgroup O n I ⊓ oppositeMirabolic n F) =
      congruenceSubgroup O n I := by
  rw [← fieldJacquetLevelMirabolic_top, fieldJacquetLevelMirabolic,
    integralJacquetMirabolic_top, ← map_congruent_opposite, ← Subgroup.map_sup,
    mirabolic_sup_congruent_opposite hn I]
  rfl

/-- Field form of the nonnegative Jacquet generation identity. -/
theorem fieldJacquetLevelMirabolic_sup_inverseTranspose (O : Subring F) [IsLocalRing O]
    (hn : 0 < n) (I : Ideal O) :
    fieldJacquetLevelMirabolic O n ⊤ ⊔
      (fieldJacquetLevelMirabolic O n I).map
        (inverseTranspose (n + 1) F).toMonoidHom =
      congruenceSubgroup O n I := by
  rw [fieldJacquetLevelMirabolic_top, fieldJacquetLevelMirabolic_map_inverseTranspose]
  exact fieldJacquetMirabolic_sup_congruent_opposite O hn I

section Representation

variable {K : Type uK} [CommRing K] {V : Type uV} [AddCommGroup V] [Module K V]
  (π : Representation K (Langlands.GeneralLinear (n + 1) F) V)

/-- The common fixed subspace of the two concrete field Jacquet groups. -/
def jacquetInvariantSpace (O : Subring F) (I : Ideal O) : Submodule K V :=
  fixedVectors π (fieldJacquetMirabolic O n) ⊓
    fixedVectors π (congruenceSubgroup O n I ⊓ oppositeMirabolic n F)

private theorem fixedVectors_sup (P Q : Subgroup (Langlands.GeneralLinear (n + 1) F)) :
    fixedVectors π (P ⊔ Q) = fixedVectors π P ⊓ fixedVectors π Q := by
  ext v
  constructor
  · intro hv
    exact ⟨fun g => hv ⟨g.val, (show P ≤ P ⊔ Q from le_sup_left) g.property⟩,
      fun g => hv ⟨g.val, (show Q ≤ P ⊔ Q from le_sup_right) g.property⟩⟩
  · rintro ⟨hP, hQ⟩
    let S : Subgroup (Langlands.GeneralLinear (n + 1) F) :=
      { carrier := {g | π g v = v}
        one_mem' := by simp
        mul_mem' := by
          intro g h hg hh
          change π g v = v at hg
          change π h v = v at hh
          change π (g * h) v = v
          simp only [map_mul, Module.End.mul_apply, hh, hg]
        inv_mem' := by
          intro g hg
          change π g⁻¹ v = v
          have he := congrArg (π g⁻¹) hg
          simpa only [← Module.End.mul_apply, ← map_mul, inv_mul_cancel,
            map_one, Module.End.one_apply] using he.symm }
    have hle : P ⊔ Q ≤ S :=
      sup_le (fun g hg => hP ⟨g, hg⟩) (fun g hg => hQ ⟨g, hg⟩)
    exact fun g => hle g.property

/-- Two Jacquet invariances are precisely congruence invariance, on the original
representation carrier and for every ideal, including level zero. -/
theorem jacquetInvariantSpace_eq_fixedVectors (O : Subring F) [IsLocalRing O]
    (hn : 0 < n) (I : Ideal O) :
    jacquetInvariantSpace π O I = fixedVectors π (congruenceSubgroup O n I) := by
  rw [jacquetInvariantSpace, ← fixedVectors_sup,
    fieldJacquetMirabolic_sup_congruent_opposite O hn I]

/-- Specialization to the published natural-number newvector level. -/
theorem jacquetInvariantSpace_eq_levelFixedVectors [ValuativeRel F]
    (hn : 0 < n) (a : ℕ) :
    jacquetInvariantSpace π (ValuativeRel.valuation F).integer
        (IsLocalRing.maximalIdeal (ValuativeRel.valuation F).integer ^ a) =
      levelFixedVectors π a :=
  jacquetInvariantSpace_eq_fixedVectors π _ hn _

end Representation

section Whittaker

variable [ValuativeRel F] [ValuativeRel.IsRankLeOne F] [TopologicalSpace F]
  (ψ : Langlands.HarmonicAnalysis.UnitaryAdditiveCharacter F)

/-- Nonzero Whittaker functions with the two scaled Jacquet invariances cannot
have a scale of valuation below one. -/
theorem one_le_valuation_of_jacquet_invariant (hn : 0 < n) (q : Fˣ)
    (W : (Langlands.Whittaker.equivariantFunctions (upperUnipotent (n + 1) F)
      (Langlands.Whittaker.standardCharacter ψ n)).toSubmodule) (hW : W ≠ 0)
    (hP : ∀ h ∈ fieldJacquetMirabolic (ValuativeRel.valuation F).integer n,
      ∀ g, W.val (g * h) = W.val g)
    (hQ : ∀ h ∈ scaledOppositeJacquetMirabolic (ValuativeRel.valuation F).integer n q,
      ∀ g, W.val (g * h) = W.val g) :
    1 ≤ ValuativeRel.valuation F (q : F) := by
  by_contra hq
  exact hW (whittaker_eq_zero_of_negativeLevel_invariant hn q (lt_of_not_ge hq) ψ W hP hQ)

/-- With the source scale `q = ϖ^(-m)`, the two Jacquet invariances of a nonzero
Whittaker function force the integer `m` to be nonnegative. -/
theorem nonneg_of_uniformizer_jacquet_invariant (hn : 0 < n) (ϖ : Fˣ)
    (hϖ : Iwasawa.IsUniformizingElement (ValuativeRel.valuation F) ϖ) (m : ℤ)
    (W : (Langlands.Whittaker.equivariantFunctions (upperUnipotent (n + 1) F)
      (Langlands.Whittaker.standardCharacter ψ n)).toSubmodule) (hW : W ≠ 0)
    (hP : ∀ h ∈ fieldJacquetMirabolic (ValuativeRel.valuation F).integer n,
      ∀ g, W.val (g * h) = W.val g)
    (hQ : ∀ h ∈ scaledOppositeJacquetMirabolic (ValuativeRel.valuation F).integer n
      (ϖ ^ (-m)), ∀ g, W.val (g * h) = W.val g) :
    0 ≤ m := by
  by_contra hm
  have hm : 0 < -m := neg_pos.mpr (lt_of_not_ge hm)
  have hpos : 0 < ValuativeRel.valuation F (ϖ : F) :=
    lt_of_le_of_ne zero_le (Ne.symm (by simp))
  have hsmall : ValuativeRel.valuation F ((ϖ ^ (-m) : Fˣ) : F) < 1 := by
    rw [Units.val_zpow_eq_zpow_val, map_zpow₀]
    exact zpow_lt_one₀ hpos hϖ.1 hm
  exact (not_lt_of_ge (one_le_valuation_of_jacquet_invariant ψ hn _ W hW hP hQ)) hsmall

end Whittaker

end Langlands.Conductor
