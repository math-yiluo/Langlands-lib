import Langlands.ClassFieldTheory.Local.CyclicNorm
import Langlands.ClassFieldTheory.Local.UnramifiedCyclicNormQuotientProof

/-! # Finite unramified H2 invariants from explicit cyclic coordinates -/

noncomputable section

namespace Langlands.ClassFieldTheory.Local

universe u v

private theorem rationalClass_eq_zero (q : ℚ) :
    rationalClass q = 0 ↔ ∃ k : ℤ, (k : ℚ) = q := by
  change (QuotientAddGroup.mk' (AddSubgroup.zmultiples (1 : ℚ))) q = 0 ↔ _
  rw [QuotientAddGroup.mk'_apply, QuotientAddGroup.eq_zero_iff,
    AddSubgroup.mem_zmultiples_iff]
  simp only [zsmul_eq_mul, mul_one]

private def integerFraction (d : ℕ) : ℤ →+ RationalModIntegers where
  toFun z := rationalClass ((z : ℚ) / d)
  map_zero' := by simp
  map_add' a b := by simp [Int.cast_add, add_div, map_add]

private theorem integerFraction_degree (d : ℕ) (hd : 0 < d) :
    integerFraction d d = 0 := by
  apply (rationalClass_eq_zero _).mpr
  refine ⟨1, ?_⟩
  simp [ne_of_gt hd]

/-- The homomorphism taking an integer modulo d to its fraction modulo integers. -/
def denominatorMap (d : ℕ) (hd : 0 < d) : ZMod d →+ RationalModIntegers :=
  ZMod.lift d ⟨integerFraction d, integerFraction_degree d hd⟩

/-- The formula holds for every integer representative, including negative ones. -/
theorem denominatorMap_intCast (d : ℕ) (hd : 0 < d) (z : ℤ) :
    denominatorMap d hd (z : ZMod d) = rationalClass ((z : ℚ) / d) := by
  exact ZMod.lift_coe _ _ _

private theorem denominatorMap_injective (d : ℕ) (hd : 0 < d) :
    Function.Injective (denominatorMap d hd) := by
  apply (ZMod.lift_injective d).mpr
  intro z hz
  obtain ⟨k, hk⟩ := (rationalClass_eq_zero _).mp hz
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd z d).mpr
  refine ⟨k, ?_⟩
  have hdq : (d : ℚ) ≠ 0 := by exact_mod_cast (ne_of_gt hd)
  have hq : (z : ℚ) = (d : ℚ) * k := by
    rw [eq_div_iff hdq] at hk
    linarith
  exact_mod_cast hq

private theorem denominatorMap_mem (d : ℕ) (hd : 0 < d) (x : ZMod d) :
    denominatorMap d hd x ∈ denominatorSubgroup d := by
  change d • denominatorMap d hd x = 0
  rw [← map_nsmul]
  simp [nsmul_eq_mul]

private theorem denominatorMap_surjective (d : ℕ) (hd : 0 < d) :
    ∀ x : denominatorSubgroup d, ∃ z : ZMod d, denominatorMap d hd z = x := by
  intro x
  obtain ⟨q, hq⟩ := QuotientAddGroup.mk'_surjective (AddSubgroup.zmultiples (1 : ℚ)) x.val
  change rationalClass q = x.val at hq
  have hx : rationalClass ((d : ℚ) * q) = 0 := by
    rw [← nsmul_eq_mul, map_nsmul, hq]
    exact x.property
  obtain ⟨k, hk⟩ := (rationalClass_eq_zero _).mp hx
  refine ⟨(k : ZMod d), ?_⟩
  rw [denominatorMap_intCast, hk]
  have hdq : (d : ℚ) ≠ 0 := by exact_mod_cast (ne_of_gt hd)
  simpa [mul_div_cancel_left₀ q hdq] using hq

/-- The d-torsion in Q/Z is exactly ZMod d, with positive fraction convention. -/
def denominatorEquiv (d : ℕ) (hd : 0 < d) : ZMod d ≃+ denominatorSubgroup d :=
  AddEquiv.ofBijective
    ((denominatorMap d hd).codRestrict (denominatorSubgroup d) (denominatorMap_mem d hd))
    ⟨fun _ _ h => denominatorMap_injective d hd (congrArg Subtype.val h),
      fun x => by
        obtain ⟨z, hz⟩ := denominatorMap_surjective d hd x
        exact ⟨z, Subtype.ext hz⟩⟩

/-- Integer representatives have the required rational fraction after inclusion. -/
theorem denominatorEquiv_intCast (d : ℕ) (hd : 0 < d) (z : ℤ) :
    (denominatorEquiv d hd (z : ZMod d) : RationalModIntegers) =
      rationalClass ((z : ℚ) / d) :=
  denominatorMap_intCast d hd z

/-- Equivalently, one may use the canonical ZMod representative in Q. -/
theorem denominatorEquiv_apply (d : ℕ) (hd : 0 < d) (x : ZMod d) :
    (denominatorEquiv d hd x : RationalModIntegers) = rationalClass ((ZMod.cast x : ℚ) / d) := by
  have h := denominatorEquiv_intCast d hd (ZMod.cast x : ℤ)
  rw [ZMod.intCast_zmod_cast] at h
  simpa only [ZMod.intCast_cast] using h

/-- The positive generator maps to 1/d, also when d = 1. -/
theorem denominatorEquiv_one (d : ℕ) (hd : 0 < d) :
    (denominatorEquiv d hd 1 : RationalModIntegers) = reciprocalClass d := by
  simpa [reciprocalClass, one_div] using denominatorEquiv_intCast d hd 1


/-- The inverse image of the positive cyclic coordinate. -/
def cyclicCoordinateGenerator {G : Type*} [Group G] {d : ℕ}
    (χ : G ≃* Multiplicative (ZMod d)) : G :=
  χ.symm (Multiplicative.ofAdd 1)

/-- This element generates the group, without any assumption that d exceeds one. -/
theorem cyclicCoordinateGenerator_generates {G : Type*} [Group G] {d : ℕ}
    (χ : G ≃* Multiplicative (ZMod d)) (g : G) :
    g ∈ Subgroup.zpowers (cyclicCoordinateGenerator χ) := by
  obtain ⟨k, hk⟩ := ZMod.intCast_surjective (χ g).toAdd
  apply Subgroup.mem_zpowers_iff.mpr
  refine ⟨k, χ.injective ?_⟩
  rw [map_zpow]
  change (χ (χ.symm (Multiplicative.ofAdd 1))) ^ k = χ g
  rw [χ.apply_symm_apply, ← ofAdd_zsmul]
  apply Multiplicative.toAdd.injective
  change k • (1 : ZMod d) = (χ g).toAdd
  simpa only [zsmul_eq_mul, mul_one] using hk

open Langlands.LocalClassField

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{u} p) (E : PadicField.{v} p)
  [Algebra F.Carrier E.Carrier] [IsScalarTower (Padic p) F.Carrier E.Carrier]
  [FiniteDimensional F.Carrier E.Carrier]

private theorem exists_unramifiedNormOrderEquiv
    (hram : F.canonicalTopologicalData.ramificationIndex =
      E.canonicalTopologicalData.ramificationIndex) :
    ∃ e : Additive (NormQuotient F.Carrier E.Carrier) ≃+
        ZMod (Module.finrank F.Carrier E.Carrier),
      ∀ a : F.Carrierˣ,
        e (Additive.ofMul (normQuotientProjection F.Carrier E.Carrier a)) =
          (F.canonicalTopologicalData.ord (a : F.Carrier) :
            ZMod (Module.finrank F.Carrier E.Carrier)) := by
  let := F.canonicalTopologicalData.topology
  let : TopologicalSpace (Multiplicative
    (ZMod (Module.finrank F.Carrier E.Carrier))) := ⊥
  obtain ⟨e, he⟩ := unramifiedCyclicNormQuotient p F E
    F.canonicalTopologicalData E.canonicalTopologicalData hram
  exact ⟨e.toMulEquiv.toAdditiveLeft,
    fun a => congrArg Multiplicative.toAdd (he a)⟩

/-- The published unramified norm quotient, in additive notation with canonical order. -/
def unramifiedNormOrderEquiv
    (hram : F.canonicalTopologicalData.ramificationIndex =
      E.canonicalTopologicalData.ramificationIndex) :
    Additive (NormQuotient F.Carrier E.Carrier) ≃+
      ZMod (Module.finrank F.Carrier E.Carrier) :=
  Classical.choose (exists_unramifiedNormOrderEquiv F E hram)

/-- The chosen norm-quotient equivalence has the published representative formula. -/
theorem unramifiedNormOrderEquiv_projection
    (hram : F.canonicalTopologicalData.ramificationIndex =
      E.canonicalTopologicalData.ramificationIndex) (a : F.Carrierˣ) :
    unramifiedNormOrderEquiv F E hram
      (Additive.ofMul (normQuotientProjection F.Carrier E.Carrier a)) =
        (F.canonicalTopologicalData.ord (a : F.Carrier) :
          ZMod (Module.finrank F.Carrier E.Carrier)) :=
  Classical.choose_spec (exists_unramifiedNormOrderEquiv F E hram) a

variable [IsGalois F.Carrier E.Carrier]

/-- The finite unramified invariant equivalence for the explicitly supplied cyclic coordinate. -/
def unramifiedH2InvariantEquiv
    (hram : F.canonicalTopologicalData.ramificationIndex =
      E.canonicalTopologicalData.ramificationIndex)
    (χ : Gal(E.Carrier/F.Carrier) ≃*
      Multiplicative (ZMod (Module.finrank F.Carrier E.Carrier))) :
    relativeCohomology F.Carrier E.Carrier 2 ≃+
      denominatorSubgroup (Module.finrank F.Carrier E.Carrier) :=
  (cyclicH2NormEquiv F.Carrier E.Carrier (cyclicCoordinateGenerator χ)
    (cyclicCoordinateGenerator_generates χ)).trans
    ((unramifiedNormOrderEquiv F E hram).trans
      (denominatorEquiv _ (Module.finrank_pos)))

/-- The finite invariant as an additive homomorphism into the actual quotient Q/Z. -/
def unramifiedH2Invariant
    (hram : F.canonicalTopologicalData.ramificationIndex =
      E.canonicalTopologicalData.ramificationIndex)
    (χ : Gal(E.Carrier/F.Carrier) ≃*
      Multiplicative (ZMod (Module.finrank F.Carrier E.Carrier))) :
    relativeCohomology F.Carrier E.Carrier 2 →+ RationalModIntegers :=
  (denominatorSubgroup (Module.finrank F.Carrier E.Carrier)).subtype.comp
    (unramifiedH2InvariantEquiv F E hram χ).toAddMonoidHom

/-- Value on a norm representative transported backwards through the cyclic H2 comparison. -/
theorem unramifiedH2Invariant_normRepresentative
    (hram : F.canonicalTopologicalData.ramificationIndex =
      E.canonicalTopologicalData.ramificationIndex)
    (χ : Gal(E.Carrier/F.Carrier) ≃*
      Multiplicative (ZMod (Module.finrank F.Carrier E.Carrier))) (a : F.Carrierˣ) :
    unramifiedH2Invariant F E hram χ
      ((cyclicH2NormEquiv F.Carrier E.Carrier (cyclicCoordinateGenerator χ)
        (cyclicCoordinateGenerator_generates χ)).symm
          (Additive.ofMul (normQuotientProjection F.Carrier E.Carrier a))) =
      rationalClass ((F.canonicalTopologicalData.ord (a : F.Carrier) : ℚ) /
        Module.finrank F.Carrier E.Carrier) := by
  change (denominatorEquiv _ (Module.finrank_pos)
    (unramifiedNormOrderEquiv F E hram
      ((cyclicH2NormEquiv F.Carrier E.Carrier (cyclicCoordinateGenerator χ)
        (cyclicCoordinateGenerator_generates χ))
          ((cyclicH2NormEquiv F.Carrier E.Carrier (cyclicCoordinateGenerator χ)
            (cyclicCoordinateGenerator_generates χ)).symm _))) : RationalModIntegers) = _
  rw [AddEquiv.apply_symm_apply, unramifiedNormOrderEquiv_projection,
    denominatorEquiv_intCast]

/-- The finite invariant embeds relative H2 into Q/Z. -/
theorem unramifiedH2Invariant_injective
    (hram : F.canonicalTopologicalData.ramificationIndex =
      E.canonicalTopologicalData.ramificationIndex)
    (χ : Gal(E.Carrier/F.Carrier) ≃*
      Multiplicative (ZMod (Module.finrank F.Carrier E.Carrier))) :
    Function.Injective (unramifiedH2Invariant F E hram χ) :=
  Subtype.val_injective.comp (unramifiedH2InvariantEquiv F E hram χ).injective

/-- Its image is exactly the subgroup annihilated by the extension degree. -/
theorem unramifiedH2Invariant_range
    (hram : F.canonicalTopologicalData.ramificationIndex =
      E.canonicalTopologicalData.ramificationIndex)
    (χ : Gal(E.Carrier/F.Carrier) ≃*
      Multiplicative (ZMod (Module.finrank F.Carrier E.Carrier))) :
    (unramifiedH2Invariant F E hram χ).range =
      denominatorSubgroup (Module.finrank F.Carrier E.Carrier) := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    exact (unramifiedH2InvariantEquiv F E hram χ x).property
  · intro hy
    refine ⟨(unramifiedH2InvariantEquiv F E hram χ).symm ⟨y, hy⟩, ?_⟩
    exact congrArg Subtype.val
      ((unramifiedH2InvariantEquiv F E hram χ).apply_symm_apply ⟨y, hy⟩)

/-- In degree one the construction gives the zero invariant. -/
theorem unramifiedH2Invariant_degree_one
    (hram : F.canonicalTopologicalData.ramificationIndex =
      E.canonicalTopologicalData.ramificationIndex)
    (χ : Gal(E.Carrier/F.Carrier) ≃*
      Multiplicative (ZMod (Module.finrank F.Carrier E.Carrier)))
    (hd : Module.finrank F.Carrier E.Carrier = 1)
    (x : relativeCohomology F.Carrier E.Carrier 2) :
    unramifiedH2Invariant F E hram χ x = 0 := by
  have h := (unramifiedH2InvariantEquiv F E hram χ x).property
  change Module.finrank F.Carrier E.Carrier • unramifiedH2Invariant F E hram χ x = 0 at h
  simpa [hd] using h

end Langlands.ClassFieldTheory.Local
