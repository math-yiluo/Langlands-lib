import Langlands.Correspondence.Laumon.Completion
import Langlands.Galois.Local.SeparableUnramifiedArithmeticProof

/-!
# Constants of the henselian end field and the residue field of `k((t))`

For a finite field `k`, the constants `endConstants k` (the algebraic closure of `k` in the
separable generic closure `endGenericClosure k`) reduce isomorphically onto the residue field of
the integers of `SeparableClosure (LaurentSeries k)` for the Library's `closureValuation`, and
restriction of automorphisms matches the Library's residue action.
-/

noncomputable section

universe u

namespace Langlands.Henniart.Laumon

attribute [local instance] Langlands.LocalField.Laurent.valuativeRel

open IsLocalRing Polynomial ValuativeRel
open Langlands.LocalGalois Langlands.LocalGalois.SepClosed

section Restriction

variable (k : Type u) [Field k]

/-- On the separable generic closure, the restriction of `σ` agrees with the original action
of `σ`. -/
theorem completionRestriction_apply
    (σ : Gal(SeparableClosure (LaurentSeries k)/LaurentSeries k)) (x : endGenericClosure k) :
    ((completionRestriction k σ x : endGenericClosure k) : SeparableClosure (LaurentSeries k)) =
      σ (x : SeparableClosure (LaurentSeries k)) :=
  AlgEquiv.restrictNormalHom_apply (endGenericClosure k) _ x

end Restriction

section Constants

variable (k : Type u) [Field k] [Finite k]

local instance : NontriviallyNormedField (LaurentSeries k) := localNormedField (LaurentSeries k)
local instance : IsUltrametricDist (LaurentSeries k) := localNormedField_ultrametric _
local instance : CompleteSpace (LaurentSeries k) := localNormedField_complete _
local instance : Finite (ResidueField (baseIntegers (LaurentSeries k))) := localResidue_finite _

local notation "X" => LaurentSeries k
local notation "Ωx" => SeparableClosure (LaurentSeries k)
local notation "𝔸" => closureIntegers (LaurentSeries k) (SeparableClosure (LaurentSeries k))

/-- The cardinality of `k` vanishes in the separable closure of `k((t))`. -/
theorem card_cast_eq_zero : (Nat.card k : Ωx) = 0 := by
  let := Fintype.ofFinite k
  have h : (Nat.card k : k) = 0 := by
    rw [Nat.card_eq_fintype_card]
    exact FiniteField.cast_card_eq_zero k
  have := congrArg (fun c : k => ((algebraMap (endGenericClosure k) Ωx).comp
    ((algebraMap (endField k) (endGenericClosure k)).comp
      ((endRing k).subtype.comp (endConstantHom k)))) c) h
  simpa only [map_natCast, map_zero] using this

/-- For `d > 0`, the integer `q ^ d - 1` is `-1` in the separable closure, `q = #k`. -/
theorem card_pow_sub_one_cast {d : ℕ} (hd : 0 < d) :
    ((Nat.card k ^ d - 1 : ℕ) : Ωx) = -1 := by
  have hpos : 1 ≤ Nat.card k ^ d := Nat.one_le_pow _ _ Nat.card_pos
  rw [Nat.cast_sub hpos, Nat.cast_pow, card_cast_eq_zero, zero_pow hd.ne', Nat.cast_one,
    zero_sub]

/-- The order of every nonzero constant divides `q ^ d - 1` for some `d > 0`, where `q` is the
cardinality of `k`. -/
theorem endConstants_pow_eq_one (a : endConstants k) (ha : a ≠ 0) :
    ∃ d : ℕ, 0 < d ∧ (a : endGenericClosure k) ^ (Nat.card k ^ d - 1) = 1 := by
  let := endClosureConstantAlgebra k
  have hint : IsIntegral k (a : endGenericClosure k) := a.property
  exact Separable.exists_pow_card_pow_sub_one_eq_one hint (fun h => ha (Subtype.ext h))

omit [Finite k] in
/-- A root of unity of order invertible in `k((t))` lies in the separable generic closure. -/
theorem mem_endGenericClosure_of_pow_eq_one {y : Ωx} {N : ℕ} (hN : (N : Ωx) ≠ 0)
    (hy : y ^ N = 1) : y ∈ endGenericClosure k := by
  rw [mem_separableClosure_iff]
  have hNK : (N : endField k) ≠ 0 := fun h =>
    hN (by simpa only [map_natCast, map_zero] using congrArg (algebraMap (endField k) Ωx) h)
  have hsep : (Polynomial.X ^ N - C (1 : endField k)).Separable :=
    separable_X_pow_sub_C 1 hNK one_ne_zero
  refine hsep.of_dvd (minpoly.dvd _ _ ?_)
  simp [hy]

/-- The constant given by a root of unity of order invertible in `k((t))`. -/
def constantOfPowEqOne {y : Ωx} {N : ℕ} (hN : (N : Ωx) ≠ 0) (hy : y ^ N = 1) :
    endConstants k :=
  ⟨⟨y, mem_endGenericClosure_of_pow_eq_one k hN hy⟩, by
    let := endClosureConstantAlgebra k
    have hN0 : N ≠ 0 := by
      rintro rfl
      exact hN Nat.cast_zero
    change IsIntegral k _
    refine ⟨Polynomial.X ^ N - C 1, monic_X_pow_sub_C 1 hN0, ?_⟩
    have : (⟨y, mem_endGenericClosure_of_pow_eq_one k hN hy⟩ : endGenericClosure k) ^ N = 1 :=
      Subtype.ext (by simpa using hy)
    simp [this]⟩

omit [Finite k] in
@[simp] theorem coe_constantOfPowEqOne {y : Ωx} {N : ℕ} (hN : (N : Ωx) ≠ 0) (hy : y ^ N = 1) :
    (((constantOfPowEqOne k hN hy : endConstants k) : endGenericClosure k) : Ωx) = y := rfl

/-- Restriction of automorphisms preserves the constants. -/
theorem completionRestriction_mem_endConstants
    (σ : Gal(Ωx/X)) (a : endConstants k) :
    completionRestriction k σ (a : endGenericClosure k) ∈ endConstants k := by
  by_cases ha : a = 0
  · rw [ha, ZeroMemClass.coe_zero, map_zero]
    exact zero_mem _
  obtain ⟨d, hd, h⟩ := endConstants_pow_eq_one k a ha
  have hN : ((Nat.card k ^ d - 1 : ℕ) : Ωx) ≠ 0 := by
    rw [card_pow_sub_one_cast k hd]
    exact neg_ne_zero.mpr one_ne_zero
  have hy : ((completionRestriction k σ (a : endGenericClosure k) : endGenericClosure k) :
      Ωx) ^ (Nat.card k ^ d - 1) = 1 := by
    rw [← IntermediateField.coe_pow, ← map_pow, h, map_one, IntermediateField.coe_one]
  have := (constantOfPowEqOne k hN hy).property
  exact this

/-- The constant `σ(a)`. -/
def restrictedConstant (σ : Gal(Ωx/X)) (a : endConstants k) : endConstants k :=
  ⟨completionRestriction k σ (a : endGenericClosure k),
    completionRestriction_mem_endConstants k σ a⟩

/-- Constants are integral for the Library's `closureValuation`. -/
theorem constant_mem_closureIntegers (a : endConstants k) :
    ((a : endGenericClosure k) : Ωx) ∈ 𝔸 := by
  by_cases ha : a = 0
  · rw [ha]
    exact zero_mem _
  obtain ⟨d, hd, h⟩ := endConstants_pow_eq_one k a ha
  have hN : Nat.card k ^ d - 1 ≠ 0 := by
    intro h0
    have := card_pow_sub_one_cast k hd
    rw [h0, Nat.cast_zero] at this
    exact one_ne_zero (neg_eq_zero.mp this.symm)
  exact Separable.mem_integers_of_pow_eq_one (LaurentSeries k) hN
    (by rw [← IntermediateField.coe_pow, h, IntermediateField.coe_one])

/-- Reduction of the constants modulo the maximal ideal of the integers of the separable
closure. -/
def constantsResidue : endConstants k →+* ResidueField 𝔸 :=
  (residue 𝔸).comp
    ((((endGenericClosure k).val.toRingHom).comp (endConstants k).subtype).codRestrict 𝔸
      (constant_mem_closureIntegers k))

theorem constantsResidue_apply (a : endConstants k) :
    constantsResidue k a =
      residue 𝔸 ⟨((a : endGenericClosure k) : Ωx), constant_mem_closureIntegers k a⟩ := rfl

theorem constantsResidue_injective : Function.Injective (constantsResidue k) :=
  (constantsResidue k).injective

/-- Every residue class contains a constant: a Teichmüller root of unity. -/
theorem constantsResidue_surjective : Function.Surjective (constantsResidue k) := by
  intro r
  by_cases hr : r = 0
  · exact ⟨0, by rw [hr, map_zero]⟩
  obtain ⟨d, hd, hrd⟩ := Separable.exists_pow_card_pow_sub_one_eq_one
    (Algebra.IsIntegral.isIntegral (R := ResidueField (baseIntegers X)) r) hr
  obtain ⟨ζ, hζ⟩ := Separable.exists_teich X hd
  have : NeZero (Nat.card (ResidueField (baseIntegers X)) ^ d - 1) :=
    ⟨Separable.teichOrder_ne_zero X hd⟩
  obtain ⟨i, -, hi⟩ := (Separable.isPrimitiveRoot_residue X hd hζ).eq_pow_of_pow_eq_one hrd
  have hN : ((Nat.card (ResidueField (baseIntegers X)) ^ d - 1 : ℕ) : Ωx) ≠ 0 := by
    intro h
    apply (Separable.teichOrder_isUnit X hd).ne_zero
    apply Subtype.ext
    simpa using h
  have hy : ((ζ ^ i : 𝔸) : Ωx) ^ (Nat.card (ResidueField (baseIntegers X)) ^ d - 1) = 1 := by
    refine Separable.coe_pow_eq_one X ?_
    rw [← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow]
  refine ⟨constantOfPowEqOne k hN hy, ?_⟩
  rw [constantsResidue_apply, ← hi, ← map_pow]
  rfl

/-- Reduction intertwines restriction with the Library's residue action. -/
theorem constantsResidue_map (σ : Gal(Ωx/X)) (a b : endConstants k)
    (hab : (b : endGenericClosure k) = completionRestriction k σ a) :
    constantsResidue k b = residueHom X Ωx σ (constantsResidue k a) := by
  rw [constantsResidue_apply, constantsResidue_apply, residueHom_apply]
  congr 1
  apply Subtype.ext
  change ((b : endGenericClosure k) : Ωx) = σ _
  rw [hab, completionRestriction_apply]

/-- The constants are the residue field of the separable closure of `k((t))`. -/
def constantsResidueEquiv : endConstants k ≃+* ResidueField 𝔸 :=
  RingEquiv.ofBijective (constantsResidue k)
    ⟨constantsResidue_injective k, constantsResidue_surjective k⟩

/-- The constants identified with the algebraic closure of the residue field of `k((t))`,
through the Library's `residueClosureEquiv`. -/
def constantsClosureEquiv :
    endConstants k ≃+* AlgebraicClosure (Weil.Local.SepClosed.localResidueField X) :=
  (constantsResidueEquiv k).trans (residueClosureEquiv X Ωx)

/-- The identification intertwines restriction with `absoluteResidueHom`. -/
theorem constantsClosureEquiv_map (σ : Gal(Ωx/X)) (a b : endConstants k)
    (hab : (b : endGenericClosure k) = completionRestriction k σ a) :
    AlgEquiv.toAlgHom (absoluteResidueHom X Ωx σ) (constantsClosureEquiv k a) =
      constantsClosureEquiv k b := by
  change residueClosureEquiv X Ωx (residueHom X Ωx σ ((residueClosureEquiv X Ωx).symm
      (residueClosureEquiv X Ωx (constantsResidue k a)))) =
    residueClosureEquiv X Ωx (constantsResidue k b)
  rw [RingEquiv.symm_apply_apply, constantsResidue_map k σ a b hab]

/-- An automorphism lies in the Library's absolute inertia exactly when its restriction fixes
every constant. -/
theorem mem_absoluteInertia_iff (σ : Gal(Ωx/X)) :
    σ ∈ absoluteInertia X Ωx ↔
      ∀ a : endConstants k, completionRestriction k σ (a : endGenericClosure k) = a := by
  constructor
  · intro hσ a
    have h1 : residueHom X Ωx σ = 1 := MonoidHom.mem_ker.mp hσ
    have := constantsResidue_map k σ a (restrictedConstant k σ a) rfl
    rw [h1, AlgEquiv.one_apply] at this
    exact congrArg Subtype.val (constantsResidue_injective k this)
  · intro h
    change σ ∈ inertia X Ωx
    rw [mem_inertia_iff]
    intro x
    obtain ⟨a, ha⟩ := constantsResidue_surjective k (residue 𝔸 x)
    rw [← residueHom_apply, ← ha, ← constantsResidue_map k σ a a (h a).symm]

omit [Finite k] in
/-- An automorphism fixes the maximal unramified subextension exactly when it fixes every
constant. -/
theorem mem_fixingSubgroup_endUnramifiedField_iff (τ : Gal(endGenericClosure k/endField k)) :
    τ ∈ (endUnramifiedField k).fixingSubgroup ↔
      ∀ a : endConstants k, τ (a : endGenericClosure k) = a := by
  rw [IntermediateField.mem_fixingSubgroup_iff]
  constructor
  · intro h a
    exact h _ (IntermediateField.subset_adjoin _ _ a.property)
  · intro h x hx
    have hle : endUnramifiedField k ≤ IntermediateField.fixedField (Subgroup.zpowers τ) := by
      refine IntermediateField.adjoin_le_iff.mpr ?_
      intro y hy
      rw [SetLike.mem_coe, IntermediateField.mem_fixedField_iff]
      intro f hf
      have hst : τ ∈ MulAction.stabilizer (Gal(endGenericClosure k/endField k)) y := by
        rw [MulAction.mem_stabilizer_iff, AlgEquiv.smul_def]
        exact h ⟨y, hy⟩
      have := (Subgroup.zpowers_le.mpr hst) hf
      rwa [MulAction.mem_stabilizer_iff, AlgEquiv.smul_def] at this
    exact (IntermediateField.mem_fixedField_iff _ _).mp (hle hx) τ (Subgroup.mem_zpowers τ)

/-- **Clause 1.** If restriction is surjective, it maps the Library's absolute inertia onto the
automorphisms fixing the maximal unramified subextension. -/
theorem absoluteInertia_map_completionRestriction
    (hsurj : Function.Surjective (completionRestriction k)) :
    (absoluteInertia X Ωx).map (completionRestriction k) =
      (endUnramifiedField k).fixingSubgroup := by
  ext τ
  rw [Subgroup.mem_map, mem_fixingSubgroup_endUnramifiedField_iff]
  constructor
  · rintro ⟨σ, hσ, rfl⟩
    exact (mem_absoluteInertia_iff k σ).mp hσ
  · intro h
    obtain ⟨σ, rfl⟩ := hsurj τ
    exact ⟨σ, (mem_absoluteInertia_iff k σ).mpr h, rfl⟩

/-- **Clause 2.** The constants are identified with the algebraic closure of the residue field
compatibly with the Library's residue map. -/
theorem exists_constants_residue_equiv :
    ∃ φ : endConstants k ≃+* AlgebraicClosure (Weil.Local.SepClosed.localResidueField X),
      ∀ (σ : Gal(Ωx/X)) (a b : endConstants k),
        (b : endGenericClosure k) = completionRestriction k σ a →
          AlgEquiv.toAlgHom (absoluteResidueHom X Ωx σ) (φ a) = φ b :=
  ⟨constantsClosureEquiv k, constantsClosureEquiv_map k⟩

end Constants

section Frobenius

open Langlands.Galois.FiniteField

/-- On the algebraic closure of a finite field `F` with `q` elements, the `n`-th power of
geometric Frobenius `g` satisfies `g(y) ^ (q ^ n) = y` for `n ≥ 0` and `g(y) = y ^ (q ^ (-n))`
for `n < 0`. -/
theorem geometricFrobenius_zpow_apply_pow (F : Type*) [Field F] [Finite F] (n : ℤ)
    (y : AlgebraicClosure F) :
    (AlgEquiv.toAlgHom (geometricFrobenius F ^ n) y) ^ (Nat.card F ^ n.toNat) =
      y ^ (Nat.card F ^ (-n).toNat) := by
  have harith : ∀ (m : ℕ) (z : AlgebraicClosure F),
      AlgEquiv.toAlgHom (arithmeticFrobenius F ^ m) z = z ^ (Nat.card F ^ m) := by
    intro m
    induction m with
    | zero => intro z; rw [pow_zero, pow_zero, pow_one]; rfl
    | succ m ih =>
      intro z
      have h1 : AlgEquiv.toAlgHom (arithmeticFrobenius F ^ (m + 1)) z =
          AlgEquiv.toAlgHom (arithmeticFrobenius F)
            (AlgEquiv.toAlgHom (arithmeticFrobenius F ^ m) z) := by
        rw [pow_succ']
        rfl
      rw [h1, ih]
      change arithmetic F (AlgebraicClosure F) _ = _
      rw [arithmetic_apply, ← pow_mul, ← pow_succ]
  rcases n with m | m
  · have hg : geometricFrobenius F ^ (Int.ofNat m) = (arithmeticFrobenius F ^ m)⁻¹ := by
      rw [geometricFrobenius, Int.ofNat_eq_natCast, zpow_natCast, inv_pow]
    have hn : (-(Int.ofNat m)).toNat = 0 := by simp
    have hn' : (Int.ofNat m).toNat = m := rfl
    rw [hn, pow_zero, pow_one, hn', hg, ← harith]
    have key : ∀ e : AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F,
        AlgEquiv.toAlgHom e (AlgEquiv.toAlgHom e⁻¹ y) = y := fun e => e.apply_symm_apply y
    exact key _
  · have hg : geometricFrobenius F ^ (Int.negSucc m) = arithmeticFrobenius F ^ (m + 1) := by
      rw [geometricFrobenius, zpow_negSucc, inv_pow, inv_inv]
    have hn : (Int.negSucc m).toNat = 0 := rfl
    have hm : (-(Int.negSucc m)).toNat = m + 1 := rfl
    rw [hn, hm, pow_zero, pow_one, hg, harith]

end Frobenius

section Degree

variable (k : Type u) [Field k] [Finite k]

local instance : NontriviallyNormedField (LaurentSeries k) := localNormedField (LaurentSeries k)
local instance : IsUltrametricDist (LaurentSeries k) := localNormedField_ultrametric _
local instance : CompleteSpace (LaurentSeries k) := localNormedField_complete _
local instance : Finite (ResidueField (baseIntegers (LaurentSeries k))) := localResidue_finite _

local notation "X" => LaurentSeries k
local notation "Ωx" => SeparableClosure (LaurentSeries k)

open Langlands.Weil Langlands.Weil.Local.SepClosed

/-- A Weil element of degree `n` acts on the residue field as the `n`-th power of geometric
Frobenius. -/
theorem absoluteResidueHom_localProjection (w : localWeilGroup X Ωx) :
    absoluteResidueHom X Ωx (localProjection X Ωx w) =
      Galois.FiniteField.geometricFrobenius (localResidueField X) ^ localDegreeInt X Ωx w := by
  have hw : localResidueDegree X Ωx (localProjection X Ωx w) =
      frobenius (localDegree X Ωx w) := w.property
  rw [localDegreeInt, ← Galois.FiniteField.profiniteEquivalence_symm_frobenius, ← hw]
  exact ((Galois.FiniteField.profiniteEquivalence _).symm_apply_apply _).symm

/-- **Clause 3.** A Weil element of degree `n` acts on the constants as the `n`-th power of
geometric Frobenius. -/
theorem completionRestriction_localProjection_pow (w : localWeilGroup X Ωx)
    (a : endConstants k) :
    (completionRestriction k (localProjection X Ωx w) a) ^
        (Nat.card k ^ (localDegreeInt X Ωx w).toNat) =
      (a : endGenericClosure k) ^ (Nat.card k ^ (-localDegreeInt X Ωx w).toNat) := by
  have hq : Nat.card (localResidueField X) = Nat.card k :=
    LocalField.Laurent.residueCardinality_eq k
  have h := constantsClosureEquiv_map k (localProjection X Ωx w) a
    (restrictedConstant k (localProjection X Ωx w) a) rfl
  rw [absoluteResidueHom_localProjection] at h
  have key : constantsClosureEquiv k
        (restrictedConstant k (localProjection X Ωx w) a ^
          (Nat.card k ^ (localDegreeInt X Ωx w).toNat)) =
      constantsClosureEquiv k (a ^ (Nat.card k ^ (-localDegreeInt X Ωx w).toNat)) := by
    rw [map_pow, map_pow, ← h, ← hq]
    exact geometricFrobenius_zpow_apply_pow _ _ _
  have := congrArg (fun c : endConstants k => (c : endGenericClosure k))
    ((constantsClosureEquiv k).injective key)
  simp only [SubmonoidClass.coe_pow] at this
  exact this

end Degree

end Langlands.Henniart.Laumon
