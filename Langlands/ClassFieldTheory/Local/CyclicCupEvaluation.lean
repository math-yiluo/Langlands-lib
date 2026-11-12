import Langlands.GroupTheory.CocycleSplittingCup
import Langlands.ClassFieldTheory.Local.CyclicClass
import Langlands.ClassFieldTheory.Local.TateAbelianization

noncomputable section

universe u v

open CategoryTheory

namespace Langlands.ClassFieldTheory.Local

set_option backward.isDefEq.respectTransparency false

lemma sum_cyclicCarry {n : ℕ} [NeZero n] (b : ZMod n) :
    ∑ a : ZMod n, cyclicCarry a b = b.val := by
  classical
  have hs : n * (∑ a : ZMod n, cyclicCarry a b) +
      (∑ a : ZMod n, (a + b).val) =
      (∑ a : ZMod n, a.val) + n * b.val := by
    calc
      _ = ∑ a : ZMod n, (n * cyclicCarry a b + (a + b).val) := by
        rw [Finset.mul_sum, Finset.sum_add_distrib]
      _ = ∑ a : ZMod n, (a.val + b.val) :=
        Finset.sum_congr rfl (fun a _ => cyclicCarry_spec a b)
      _ = _ := by simp [Finset.sum_add_distrib, ZMod.card]
  have hsum : (∑ a : ZMod n, (a + b).val) = ∑ a : ZMod n, a.val := by
    simpa only [Equiv.coe_addRight] using
      Equiv.sum_comp (Equiv.addRight b) (fun a : ZMod n => a.val)
  rw [hsum] at hs
  apply Nat.eq_of_mul_eq_mul_left (NeZero.pos n)
  omega

variable (K : Type v) (L : Type u) [Field K] [Field L] [Algebra K L]
  {n : ℕ} [NeZero n]

/-- The published additive carry cocycle as a normalized multiplicative cocycle. -/
def normalizedCyclicCocycle
    (χ : Gal(L/K) →* Multiplicative (ZMod n)) (a : Kˣ) :
    NormalizedTwoCocycle Gal(L/K) Lˣ :=
  NormalizedTwoCocycle.normalizedRepresentative (cyclicUnitCocycle K L χ a)

lemma normalizedCyclicCocycle_apply
    (χ : Gal(L/K) →* Multiplicative (ZMod n)) (a : Kˣ) (g h : Gal(L/K)) :
    Additive.ofMul (normalizedCyclicCocycle K L χ a (g, h)) =
      cyclicCarry (χ g).toAdd (χ h).toAdd • baseUnit K L a := by
  rw [normalizedCyclicCocycle, NormalizedTwoCocycle.normalizedRepresentative_apply]
  have hf : cyclicUnitCocycle K L χ a (1, 1) = 0 := by
    simp [cyclicUnitCocycle, cyclicCarry]
  erw [hf]
  change @Additive.ofMul Lˣ
    (@Additive.toMul Lˣ (cyclicCarry (χ g).toAdd (χ h).toAdd • baseUnit K L a) /
      g • (1 : Lˣ)) = _
  simp only [smul_one, div_one]
  rfl

lemma normalizedCyclicCocycle_class
    (χ : Gal(L/K) →* Multiplicative (ZMod n)) (a : Kˣ) :
    NormalizedTwoCocycle.cohomologyClass (normalizedCyclicCocycle K L χ a) =
      cyclicClass K L χ a :=
  NormalizedTwoCocycle.cohomologyClass_normalizedRepresentative _

lemma normalizedCyclicCocycle_inverseRowSum [Fintype Gal(L/K)]
    (χ : Gal(L/K) ≃* Multiplicative (ZMod n)) (a : Kˣ) (g : Gal(L/K)) :
    NormalizedTwoCocycle.SplittingModule.inverseRowSum
        (normalizedCyclicCocycle K L χ.toMonoidHom a) g =
      (χ g⁻¹).toAdd.val • baseUnit K L a := by
  classical
  simp only [NormalizedTwoCocycle.SplittingModule.inverseRowSum,
    normalizedCyclicCocycle_apply, ← Finset.sum_smul]
  congr 1
  rw [← sum_cyclicCarry (χ g⁻¹).toAdd]
  exact (χ.toEquiv.trans Multiplicative.toAdd).sum_comp
    (fun z : ZMod n => cyclicCarry z (χ g⁻¹).toAdd)

variable [FiniteDimensional K L] [IsGalois K L]

omit [IsGalois K L] in
lemma normQuotientProjection_degree_nsmul (a : Kˣ) :
    Module.finrank K L •
      Additive.ofMul (Langlands.LocalClassField.normQuotientProjection K L a) = 0 := by
  change Additive.ofMul
    ((Langlands.LocalClassField.normQuotientProjection K L a) ^ Module.finrank K L) =
      Additive.ofMul 1
  apply congrArg Additive.ofMul
  rw [← map_pow]
  apply (QuotientGroup.eq_one_iff _).mpr
  refine ⟨Units.map (algebraMap K L).toMonoidHom a, ?_⟩
  apply Units.ext
  exact Algebra.norm_algebraMap (a : K)

lemma inverse_val_nsmul_eq_neg {B : Type*} [AddCommGroup B]
    (b : B) (hb : n • b = 0) (z : ZMod n) :
    (-z).val • b = -(z.val • b) := by
  apply eq_neg_of_add_eq_zero_left
  rw [← add_nsmul]
  by_cases hz : z = 0
  · simp [hz]
  · rw [ZMod.neg_val, ite_eq_right (by exact hz), Nat.sub_add_cancel (Nat.le_of_lt (ZMod.val_lt z)), hb]

/-- Cup of a positive carry class on a single Galois generator. -/
lemma abelianizationCupToNormQuotient_cyclicClass
    (χ : Gal(L/K) ≃* Multiplicative (ZMod n)) (a : Kˣ) (g : Gal(L/K)) :
    abelianizationCupToNormQuotient K L (cyclicClass K L χ.toMonoidHom a)
        (Additive.ofMul (Abelianization.of g)) =
      (χ g⁻¹).toAdd.val •
        Additive.ofMul (Langlands.LocalClassField.normQuotientProjection K L a) := by
  let := Fintype.ofFinite Gal(L/K)
  rw [← integralTateMinusTwoEquiv_class K L g,
    abelianizationCupToNormQuotient_comparison]
  change tateZeroEquivNormQuotient K L
    (Tate.scalarH2Cup (unitsRepresentation K L) (-2)
      (cyclicClass K L χ.toMonoidHom a)
      (Tate.minusTwoClass (Tate.integralTrivial Gal(L/K)) g 1)) = _
  erw [← normalizedCyclicCocycle_class,
    NormalizedTwoCocycle.SplittingModule.scalarH2Cup_minusTwoClass]
  have hv : NormalizedTwoCocycle.SplittingModule.inverseRowInvariant
      (normalizedCyclicCocycle K L χ.toMonoidHom a) g =
      baseUnitsToInvariants K L (Additive.ofMul (a ^ (χ g⁻¹).toAdd.val)) := by
    apply Subtype.ext
    change NormalizedTwoCocycle.SplittingModule.inverseRowSum
      (normalizedCyclicCocycle K L χ.toMonoidHom a) g = _
    rw [normalizedCyclicCocycle_inverseRowSum]
    change (χ g⁻¹).toAdd.val •
      Additive.ofMul (Units.map (algebraMap K L).toMonoidHom a) =
      Additive.ofMul (Units.map (algebraMap K L).toMonoidHom (a ^ (χ g⁻¹).toAdd.val))
    rw [map_pow, ofMul_pow]
  erw [hv, tateZeroEquivNormQuotient_zeroClass, map_pow, ofMul_pow]

/-- Under the published inverse-action homology convention, a positive carry
class has the negative cyclic evaluation in the field norm quotient. -/
lemma abelianizationCupToNormQuotient_cyclicClass_signed
    (χ : Gal(L/K) ≃* Multiplicative (ZMod n)) (a : Kˣ) (g : Gal(L/K)) :
    abelianizationCupToNormQuotient K L (cyclicClass K L χ.toMonoidHom a)
        (Additive.ofMul (Abelianization.of g)) =
      -((χ g).toAdd.val •
        Additive.ofMul (Langlands.LocalClassField.normQuotientProjection K L a)) := by
  have hcard : Module.finrank K L = n := by
    rw [← IsGalois.card_aut_eq_finrank K L, Nat.card_congr χ.toEquiv]
    simp
  rw [abelianizationCupToNormQuotient_cyclicClass, map_inv, toAdd_inv]
  exact inverse_val_nsmul_eq_neg
    (Additive.ofMul (Langlands.LocalClassField.normQuotientProjection K L a))
    (by rw [← hcard]; exact normQuotientProjection_degree_nsmul K L a) (χ g).toAdd

end Langlands.ClassFieldTheory.Local
