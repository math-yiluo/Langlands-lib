import Langlands.ClassField.Global.UnramifiedCyclotomicStatement
import Langlands.ClassFieldTheory.Local.UnramifiedArithmeticProof
import Langlands.ClassFieldTheory.Local.NormOrderProof
import Langlands.Global.CompletionResidueAdic

/-! # Unramified cyclotomic completions and the Frobenius of the Artin symbol (proof) -/

noncomputable section

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum IsLocalRing
open scoped NumberField Langlands.Global.AdelicFunctoriality.FiniteExtension
open Langlands.Global.AdelicFunctoriality Langlands.Global.CompletionPadic
open Langlands.ClassFieldTheory.Local

namespace Langlands.ClassField.Global

universe u v

namespace UnramifiedCyclotomic

section RootsOfUnity

/-- In a local domain in which `N` is invertible, two `N`-th roots of unity with the same
residue are equal. -/
theorem eq_of_pow_eq_one_of_residue_eq {A : Type*} [CommRing A] [IsDomain A] [IsLocalRing A]
    {N : ℕ} (hN : IsUnit (N : A)) {α β : A} (hα : α ^ N = 1) (hβ : β ^ N = 1)
    (h : residue A α = residue A β) : α = β := by
  by_contra hne
  have hS : (∑ i ∈ Finset.range N, α ^ i * β ^ (N - 1 - i)) = 0 := by
    have key := (Commute.all α β).geom_sum₂_mul N
    rw [hα, hβ, sub_self] at key
    exact (mul_eq_zero.1 key).resolve_right (sub_ne_zero.2 hne)
  have hN0 : N ≠ 0 := by
    rintro rfl
    simp at hN
  have hαu : IsUnit α := IsUnit.of_pow_eq_one hα hN0
  have h1 := congrArg (residue A) hS
  rw [map_sum, map_zero] at h1
  simp only [map_mul, map_pow, ← h] at h1
  have h2 : ∀ i ∈ Finset.range N,
      residue A α ^ i * residue A α ^ (N - 1 - i) = residue A α ^ (N - 1) := by
    intro i hi
    rw [← pow_add]
    congr 1
    have := Finset.mem_range.1 hi
    omega
  rw [Finset.sum_congr rfl h2, Finset.sum_const, Finset.card_range, nsmul_eq_mul] at h1
  have hNr : (N : ResidueField A) ≠ 0 := by
    rw [← map_natCast (residue A)]
    exact (residue_ne_zero_iff_isUnit _).2 hN
  exact mul_ne_zero hNr (pow_ne_zero _ (hαu.map (residue A)).ne_zero) h1

end RootsOfUnity

section LocalCoordinate

open LocalGalois

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{u} p)

local instance : NontriviallyNormedField F.Carrier := F.canonicalNormedField
local instance : NormedAlgebra (Padic p) F.Carrier := F.canonicalNormedAlgebra
local instance : IsUltrametricDist F.Carrier :=
  IsUltrametricDist.isUltrametricDist_of_isNonarchimedean_norm
    (isNonarchimedean_spectralNorm (K := Padic p) (L := F.Carrier))
local instance : ProperSpace F.Carrier := FiniteDimensional.proper (Padic p) F.Carrier

variable (L : Type v) [Field L] [Algebra F.Carrier L] [FiniteDimensional F.Carrier L]

/-- A root of unity of order `N` as an element of the spectral integers. -/
theorem mem_extensionIntegers_of_pow_eq_one {N : ℕ} (hN : N ≠ 0) {α : L} (hα : α ^ N = 1) :
    α ∈ extensionIntegers F.Carrier L := by
  rw [← integral_iff_mem_spectralIntegers]
  refine IsIntegral.of_pow (Nat.pos_of_ne_zero hN) ?_
  rw [hα]
  exact isIntegral_one

/-- If `N` is nonzero in the base residue field, it is a unit in the spectral integers of `L`. -/
theorem isUnit_natCast_extensionIntegers {N : ℕ}
    (hN : (N : ResidueField (baseIntegers F.Carrier)) ≠ 0) :
    IsUnit (N : extensionIntegers F.Carrier L) := by
  rw [← residue_ne_zero_iff_isUnit, map_natCast]
  intro h
  apply hN
  apply (algebraMap (ResidueField (baseIntegers F.Carrier))
    (ResidueField (extensionIntegers F.Carrier L))).injective
  rw [map_natCast, map_zero]
  exact h

/-- An automorphism acting trivially on the residue field fixes every root of unity of order
prime to the residue characteristic. -/
theorem apply_eq_of_residueHom_eq_one {N : ℕ}
    (hN : (N : ResidueField (baseIntegers F.Carrier)) ≠ 0) {α : L} (hα : α ^ N = 1)
    (σ : Gal(L/F.Carrier)) (n : ℕ) (hσ : ∀ x, residueHom F.Carrier L σ x = x ^ n) :
    σ α = α ^ n := by
  have hN0 : N ≠ 0 := by
    rintro rfl
    exact hN Nat.cast_zero
  set a : extensionIntegers F.Carrier L := ⟨α, mem_extensionIntegers_of_pow_eq_one F L hN0 hα⟩
  have ha : a ^ N = 1 := Subtype.ext (by simpa using hα)
  have hb : (integerAut F.Carrier L σ a) ^ N = 1 := by
    rw [← map_pow, ha, map_one]
  have hc : (a ^ n) ^ N = 1 := by
    rw [← pow_mul, mul_comm, pow_mul, ha, one_pow]
  have key := eq_of_pow_eq_one_of_residue_eq (isUnit_natCast_extensionIntegers F L hN) hb hc
    (by rw [map_pow]; exact hσ (residue _ a))
  exact congrArg Subtype.val key

variable [IsGalois F.Carrier L]

/-- Faithful action on a root of unity of order prime to `p` makes the residue action
injective. -/
theorem residueHom_injective_of_root {N : ℕ}
    (hN : (N : ResidueField (baseIntegers F.Carrier)) ≠ 0) {α : L} (hα : α ^ N = 1)
    (hfaith : ∀ σ : Gal(L/F.Carrier), σ α = α → σ = 1) :
    Function.Injective (residueHom F.Carrier L) := by
  rw [injective_iff_map_eq_one]
  intro σ hσ
  apply hfaith
  have h := apply_eq_of_residueHom_eq_one F L hN hα σ 1 (fun x => by simp [hσ])
  rwa [pow_one] at h

/-- `L` as a finite extension of `ℚ_p` through `F`. -/
def towerField : PadicField.{v} p where
  Carrier := L
  algebra := ((algebraMap F.Carrier L).comp (algebraMap (Padic p) F.Carrier)).toAlgebra
  finiteDimensional := by
    let : Algebra (Padic p) L :=
      ((algebraMap F.Carrier L).comp (algebraMap (Padic p) F.Carrier)).toAlgebra
    have : IsScalarTower (Padic p) F.Carrier L := IsScalarTower.of_algebraMap_eq fun _ => rfl
    exact Module.Finite.trans F.Carrier L

instance towerField.instAlgebra : Algebra F.Carrier (towerField F L).Carrier :=
  inferInstanceAs (Algebra F.Carrier L)

instance towerField.instFiniteDimensional :
    FiniteDimensional F.Carrier (towerField F L).Carrier :=
  inferInstanceAs (FiniteDimensional F.Carrier L)

instance towerField.instIsScalarTower :
    IsScalarTower (Padic p) F.Carrier (towerField F L).Carrier :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

theorem extensionResidue_finite :
    Finite (ResidueField (extensionIntegers F.Carrier L)) :=
  ArithmeticCoordinate.extensionResidueFinite F (towerField F L)

/-- With an injective residue action, a lift of the residue Frobenius generates the Galois
group. -/
theorem exists_frobenius_generator (hinj : Function.Injective (residueHom F.Carrier L)) :
    ∃ φ : Gal(L/F.Carrier), (∀ σ, σ ∈ Subgroup.zpowers φ) ∧
      ∀ x, residueHom F.Carrier L φ x = x ^ Nat.card (ResidueField (baseIntegers F.Carrier)) := by
  have := ArithmeticCoordinate.baseResidueFinite F
  have := extensionResidue_finite F L
  let := Fintype.ofFinite (ResidueField (baseIntegers F.Carrier))
  let r := MulEquiv.ofBijective (residueHom F.Carrier L)
    ⟨hinj, residueHom_surjective F.Carrier L⟩
  let ψ := FiniteField.frobeniusAlgEquivOfAlgebraic
    (ResidueField (baseIntegers F.Carrier)) (ResidueField (extensionIntegers F.Carrier L))
  refine ⟨r.symm ψ, fun σ => ?_, fun x => ?_⟩
  · obtain ⟨i, hi⟩ := (FiniteField.bijective_frobeniusAlgEquivOfAlgebraic_pow
      (ResidueField (baseIntegers F.Carrier))
      (ResidueField (extensionIntegers F.Carrier L))).surjective (r σ)
    apply Subgroup.mem_zpowers_iff.mpr
    refine ⟨(i.val : ℤ), ?_⟩
    apply r.injective
    simpa only [map_zpow, map_pow, MulEquiv.apply_symm_apply, zpow_natCast] using hi
  · change r (r.symm ψ) x = _
    rw [MulEquiv.apply_symm_apply]
    change x ^ Fintype.card (ResidueField (baseIntegers F.Carrier)) = _
    rw [Fintype.card_eq_nat_card]

/-- A Frobenius generator gives an arithmetic coordinate onto `ℤ / e` for `e` the order of the
Galois group. -/
theorem exists_coordinate_of_generator {φ : Gal(L/F.Carrier)}
    (hg : ∀ σ, σ ∈ Subgroup.zpowers φ) (hinj : Function.Injective (residueHom F.Carrier L))
    (hφ : ∀ x, residueHom F.Carrier L φ x =
      x ^ Nat.card (ResidueField (baseIntegers F.Carrier)))
    {e : ℕ} [NeZero e] (he : Nat.card Gal(L/F.Carrier) = e) :
    ∃ χ : Gal(L/F.Carrier) ≃* Multiplicative (ZMod e),
      IsArithmeticUnramifiedCoordinate F L χ ∧ χ.symm (Multiplicative.ofAdd 1) = φ := by
  let χ := (zmodMulEquivOfGenerator hg he).symm
  have h1 : χ.symm (Multiplicative.ofAdd 1) = φ := by
    dsimp only [χ, MulEquiv.symm_symm]
    exact zmodMulEquivOfGenerator_apply_ofAdd_one hg he
  refine ⟨χ, ⟨hinj, fun x => ?_⟩, h1⟩
  rw [h1]
  exact hφ x

variable {F} in
/-- A valuation subring with the spectral unit ball as carrier is the spectral integer ring. -/
def integersEquiv (O : ValuationSubring F.Carrier)
    (hO : ∀ x, x ∈ O ↔ F.canonicalNorm x ≤ 1) : O ≃+* baseIntegers F.Carrier :=
  RingEquiv.subringCongr (R := F.Carrier) (s := O.toSubring)
    (t := (baseIntegers F.Carrier).toSubring) (by
      ext x
      exact hO x)

/-- **Local Frobenius coordinate.** Let `L / F` be finite Galois, `O` the integers of `F`, and
`α ∈ L` an `N`-th root of unity with `N` invertible in the residue field of `O`, on which
`Gal(L/F)` acts faithfully. Then a Frobenius `φ` generates `Gal(L/F)`, acts on `α` by the
residue cardinality, and gives an arithmetic coordinate onto `ℤ / |Gal(L/F)|`. -/
theorem exists_frobenius_coordinate (O : ValuationSubring F.Carrier)
    (hO : ∀ x, x ∈ O ↔ F.canonicalNorm x ≤ 1) {N : ℕ} (hN : (N : ResidueField O) ≠ 0)
    {α : L} (hα : α ^ N = 1) (hfaith : ∀ σ : Gal(L/F.Carrier), σ α = α → σ = 1) :
    ∃ φ : Gal(L/F.Carrier), (∀ σ, σ ∈ Subgroup.zpowers φ) ∧
      φ α = α ^ Nat.card (ResidueField O) ∧
      ∀ (e : ℕ) [NeZero e], Nat.card Gal(L/F.Carrier) = e →
        ∃ χ : Gal(L/F.Carrier) ≃* Multiplicative (ZMod e),
          IsArithmeticUnramifiedCoordinate F L χ ∧ χ.symm (Multiplicative.ofAdd 1) = φ := by
  let eO := ResidueField.mapEquiv (integersEquiv O hO)
  have hN' : (N : ResidueField (baseIntegers F.Carrier)) ≠ 0 := by
    rw [← map_natCast eO]
    exact (map_ne_zero eO).2 hN
  have hcard : Nat.card (ResidueField (baseIntegers F.Carrier)) =
      Nat.card (ResidueField O) := Nat.card_congr eO.symm.toEquiv
  have hinj := residueHom_injective_of_root F L hN' hα hfaith
  obtain ⟨φ, hg, hφ⟩ := exists_frobenius_generator F L hinj
  refine ⟨φ, hg, ?_, fun e _ he => exists_coordinate_of_generator F L hg hinj hφ he⟩
  rw [← hcard]
  exact apply_eq_of_residueHom_eq_one F L hN' hα φ _ hφ

omit [FiniteDimensional F.Carrier L] [IsGalois F.Carrier L] in
/-- The residue field of `O` has cardinality `p ^ f`, `f` the residue degree. -/
theorem card_residueField_eq_pow (O : ValuationSubring F.Carrier)
    (hO : ∀ x, x ∈ O ↔ F.canonicalNorm x ≤ 1) :
    Nat.card (ResidueField O) = p ^ F.canonicalTopologicalData.residueDegree := by
  rw [← F.canonicalTopologicalData.residueCardinality_eq_pow]
  exact (Nat.card_congr (ResidueField.mapEquiv (integersEquiv O hO)).toEquiv).trans
    (Nat.card_congr (ArithmeticCoordinate.baseResidueEquiv F).toEquiv)

omit [FiniteDimensional F.Carrier L] [IsGalois F.Carrier L] in
/-- The residue field of `O` has characteristic `p`. -/
theorem natCast_residueField_eq_zero (O : ValuationSubring F.Carrier)
    (hO : ∀ x, x ∈ O ↔ F.canonicalNorm x ≤ 1) : (p : ResidueField O) = 0 := by
  have := F.canonicalTopologicalData.residueCharP
  apply ((ResidueField.mapEquiv (integersEquiv O hO)).trans
    (ArithmeticCoordinate.baseResidueEquiv F)).injective
  rw [map_natCast, map_zero, CharP.cast_eq_zero]

omit [FiniteDimensional F.Carrier L] [IsGalois F.Carrier L] in
/-- An integer which is nonzero in the residue field of `O` is prime to `p`. -/
theorem coprime_of_natCast_ne_zero (O : ValuationSubring F.Carrier)
    (hO : ∀ x, x ∈ O ↔ F.canonicalNorm x ≤ 1) {N : ℕ} (hN : (N : ResidueField O) ≠ 0) :
    Nat.Coprime p N := by
  rw [Nat.Prime.coprime_iff_not_dvd Fact.out]
  rintro ⟨c, rfl⟩
  apply hN
  rw [Nat.cast_mul, natCast_residueField_eq_zero F O hO, zero_mul]

end LocalCoordinate

section Stabilizer

variable {F L : Type*} [Field F] [Field L] [Algebra F L]

/-- A power `ζ ^ a` of a primitive `N`-th root of unity depends only on `a` modulo `N`. -/
theorem pow_eq_pow_iff_natCast_eq {K : Type*} [CommMonoid K] {ξ : K} {N : ℕ} [NeZero N]
    (hξ : IsPrimitiveRoot ξ N) (a b : ℕ) : ξ ^ a = ξ ^ b ↔ (a : ZMod N) = (b : ZMod N) := by
  rw [(hξ.isOfFinOrder (NeZero.ne N)).pow_eq_pow_iff_modEq, ← hξ.eq_orderOf,
    ZMod.natCast_eq_natCast_iff]

/-- The element `ζ ^ k` of `F(ζ ^ k) = stabilizerField ζ k`. -/
def stabilizerRoot (ζ : L) (k : ℕ) : stabilizerField (F := F) ζ k :=
  ⟨ζ ^ k, (IntermediateField.mem_fixedField_iff _ _).2 fun _ h => h⟩

theorem algebraMap_stabilizerRoot (ζ : L) (k : ℕ) :
    algebraMap (stabilizerField (F := F) ζ k) L (stabilizerRoot ζ k) = ζ ^ k :=
  rfl

/-- If `ζ` is a primitive `M`-th root of unity and `N ∣ M`, then `ζ ^ (M / N)` is a primitive
`N`-th root of unity. -/
theorem isPrimitiveRoot_stabilizerRoot {M N : ℕ} [NeZero M] {ζ : L} (hζ : IsPrimitiveRoot ζ M)
    (hNM : N ∣ M) : IsPrimitiveRoot (stabilizerRoot (F := F) ζ (M / N)) N :=
  IsPrimitiveRoot.of_map_of_injective (f := algebraMap (stabilizerField (F := F) ζ (M / N)) L)
    (IsPrimitiveRoot.pow (Nat.pos_of_ne_zero (NeZero.ne M)) hζ (Nat.div_mul_cancel hNM).symm)
    (algebraMap (stabilizerField (F := F) ζ (M / N)) L).injective

/-- Restriction of `σ` to `F(ζ ^ k)` acts on `ζ ^ k` through the cyclotomic character of `σ`. -/
theorem restrictNormal_stabilizerRoot {M : ℕ} [NeZero M] {ζ : L} (hζ : IsPrimitiveRoot ζ M)
    (k : ℕ) [Normal F (stabilizerField (F := F) ζ k)] (σ : L ≃ₐ[F] L) :
    σ.restrictNormal (stabilizerField (F := F) ζ k) (stabilizerRoot ζ k) =
      stabilizerRoot ζ k ^ (hζ.autToPow F σ : ZMod M).val := by
  apply (algebraMap (stabilizerField (F := F) ζ k) L).injective
  rw [AlgEquiv.restrictNormal_commutes, map_pow, algebraMap_stabilizerRoot, map_pow,
    ← hζ.autToPow_spec F σ, ← pow_mul, ← pow_mul, mul_comm]

variable [FiniteDimensional F L] [IsGalois F L] {ζ : L} {k : ℕ}
  [(rootStabilizer (F := F) (ζ := ζ) k).Normal]

/-- `Gal(F(ζ ^ k)/F)` acts faithfully on `ζ ^ k`. -/
theorem eq_one_of_apply_stabilizerRoot
    (τ : stabilizerField (F := F) ζ k ≃ₐ[F] stabilizerField (F := F) ζ k)
    (h : τ (stabilizerRoot ζ k) = stabilizerRoot ζ k) : τ = 1 := by
  obtain ⟨σ, rfl⟩ := AlgEquiv.restrictNormalHom_surjective (F := F)
    (K₁ := stabilizerField (F := F) ζ k) L τ
  have hσ : σ ∈ rootStabilizer (F := F) (ζ := ζ) k := by
    change σ (ζ ^ k) = ζ ^ k
    have h1 := AlgEquiv.restrictNormal_commutes σ (stabilizerField (F := F) ζ k)
      (stabilizerRoot ζ k)
    rw [algebraMap_stabilizerRoot] at h1
    rw [← h1]
    exact congrArg (algebraMap (stabilizerField (F := F) ζ k) L) h
  rw [← MonoidHom.mem_ker, IntermediateField.restrictNormalHom_ker,
    IntermediateField.fixingSubgroup_fixedField]
  exact hσ

/-- Elements of `Gal(F(ζ ^ k)/F)` are determined by their value on `ζ ^ k`. -/
theorem eq_of_apply_stabilizerRoot_eq
    {τ₁ τ₂ : stabilizerField (F := F) ζ k ≃ₐ[F] stabilizerField (F := F) ζ k}
    (h : τ₁ (stabilizerRoot ζ k) = τ₂ (stabilizerRoot ζ k)) : τ₁ = τ₂ := by
  have h1 : (τ₂⁻¹ * τ₁) (stabilizerRoot ζ k) = stabilizerRoot ζ k := by
    rw [AlgEquiv.mul_apply, h, ← AlgEquiv.mul_apply, inv_mul_cancel, AlgEquiv.one_apply]
  exact (inv_mul_eq_one.1 (eq_one_of_apply_stabilizerRoot _ h1)).symm

/-- The cyclotomic character of `F(ζ ^ k)` is injective. -/
theorem autToPow_stabilizerRoot_injective {N : ℕ} [NeZero N]
    (hN : IsPrimitiveRoot (stabilizerRoot (F := F) ζ k) N) :
    Function.Injective (hN.autToPow F) := by
  intro τ₁ τ₂ h
  apply eq_of_apply_stabilizerRoot_eq
  rw [← hN.autToPow_spec F τ₁, ← hN.autToPow_spec F τ₂, h]

end Stabilizer

section NormValuation

variable {F : Type u} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))

/-- The local norm to `ℚ_p` of an element of `F_v` of order `1` has `p`-adic valuation the
residue degree `f` of `F_v`. -/
theorem valuation_localNorm (π : (v.adicCompletion F)ˣ)
    (hπ : (padicField v).canonicalTopologicalData.ord (π : v.adicCompletion F) = 1) :
    ((Units.map ((Rat.HeightOneSpectrum.adicCompletion.padicEquiv
        (rationalPlace v)).toRingEquiv.toMonoidHom.comp
        (FiniteExtension.localNorm (rationalPlace v) v)) π : ℚ_[residuePrime v]ˣ) :
        ℚ_[residuePrime v]).valuation =
      ((padicField v).canonicalTopologicalData.residueDegree : ℤ) := by
  let Q := PadicField.rational (residuePrime v)
  let TQ := PadicField.rationalTopologicalData (residuePrime v)
  let : Algebra (Padic (residuePrime v)) (padicField v).Carrier := padicAlgebra v
  let : Algebra Q.Carrier (padicField v).Carrier := padicAlgebra v
  have : IsScalarTower (Padic (residuePrime v)) Q.Carrier (padicField v).Carrier :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : FiniteDimensional Q.Carrier (padicField v).Carrier := padicFinite v
  have h := Langlands.LocalClassField.residueDegree_mul_ord_relative_norm Q (padicField v) TQ
    (padicField v).canonicalTopologicalData (π : v.adicCompletion F)
  obtain ⟨he1, hf1⟩ := TQ.indices_eq_one_of_degree_one
    (Module.finrank_self (Padic (residuePrime v)))
  rw [hf1, hπ, Nat.cast_one, one_mul, mul_one] at h
  have hnorm : Rat.HeightOneSpectrum.adicCompletion.padicEquiv (rationalPlace v)
      (FiniteExtension.localNorm (rationalPlace v) v (π : v.adicCompletion F)) =
      Algebra.norm Q.Carrier (π : v.adicCompletion F) := by
    refine Algebra.norm_eq_of_ringEquiv (B := Q.Carrier)
      (Rat.HeightOneSpectrum.adicCompletion.padicEquiv (rationalPlace v)).toRingEquiv ?_ _
    refine RingHom.ext fun x => ?_
    change FiniteExtension.completionMap (rationalPlace v) v
        ((Rat.HeightOneSpectrum.adicCompletion.padicEquiv (rationalPlace v)).symm
          (Rat.HeightOneSpectrum.adicCompletion.padicEquiv (rationalPlace v) x)) =
      FiniteExtension.completionMap (rationalPlace v) v x
    rw [ContinuousAlgEquiv.symm_apply_apply]
  have hord := TQ.ord_algebraMap
    (Algebra.norm Q.Carrier (π : v.adicCompletion F) : Padic (residuePrime v))
  rw [he1, Nat.cast_one, one_mul] at hord
  change (Rat.HeightOneSpectrum.adicCompletion.padicEquiv (rationalPlace v)
      (FiniteExtension.localNorm (rationalPlace v) v (π : v.adicCompletion F))).valuation = _
  rw [hnorm, ← h]
  exact hord.symm

end NormValuation

section Artin

open LocalSymbolIdentity Langlands.Global.CyclotomicSymbol

variable {F L : Type u} [Field F] [Field L] [NumberField F] [NumberField L] [Algebra F L]
  [IsGalois F L] {M : ℕ} [NeZero M] {ζ : L} (hζ : IsPrimitiveRoot ζ M)
  (hinj : Function.Injective (hζ.autToPow F)) (v : HeightOneSpectrum (𝓞 F))

/-- Modulo a divisor `N` of the prime-to-`p` part of `M`, the cyclotomic character of the Artin
symbol of an element of order `1` is `p ^ f`. -/
theorem castHom_autToPow_artinSymbol {N : ℕ} (hNM : N ∣ M)
    (hd : N ∣ M / residuePrime v ^ M.factorization (residuePrime v))
    (π : (v.adicCompletion F)ˣ)
    (hπ : (padicField v).canonicalTopologicalData.ord (π : v.adicCompletion F) = 1) :
    ZMod.castHom hNM (ZMod N) (hζ.autToPow F (artinSymbol hζ hinj v π) : ZMod M) =
      ((residuePrime v ^ (padicField v).canonicalTopologicalData.residueDegree : ℕ) :
        ZMod N) := by
  rw [autToPow_artinSymbol, normSymbolAt_apply, localSymbol_apply,
    castHom_crtUnits_snd M (residuePrime v) hd hNM, valuation_localNorm v π hπ, zpow_natCast,
    Units.val_pow_eq_pow_val, map_pow, primeUnit, ZMod.coe_unitOfCoprime, map_natCast,
    Nat.cast_pow]

end Artin

section Main

open FundamentalClass CompletionTower LocalSymbolIdentity

/-- **Unramified cyclotomic completions and the Frobenius of the Artin symbol.** -/
theorem unramifiedCyclotomicFrobenius : UnramifiedCyclotomicFrobenius.{u} := by
  intro F L _ _ _ _ _ _ M _ ζ hζ hinj v u _ N _ hNM hNv hH
  have hζU := isPrimitiveRoot_stabilizerRoot (F := F) hζ hNM
  have := isGalois_adicCompletion v (stabilizerPlace (F := F) ζ (M / N) u)
  -- the root of unity `ζ ^ (M / N)` in the completion of `U = F(ζ ^ (M / N))`
  have hα : (algebraMap (stabilizerField (F := F) ζ (M / N))
      ((stabilizerPlace (F := F) ζ (M / N) u).adicCompletion
        (stabilizerField (F := F) ζ (M / N))) (stabilizerRoot (F := F) ζ (M / N))) ^ N = 1 := by
    rw [← map_pow, hζU.pow_eq_one, map_one]
  have hfaith : ∀ σ : (stabilizerPlace (F := F) ζ (M / N) u).adicCompletion
      (stabilizerField (F := F) ζ (M / N)) ≃ₐ[v.adicCompletion F]
      (stabilizerPlace (F := F) ζ (M / N) u).adicCompletion (stabilizerField (F := F) ζ (M / N)),
      σ (algebraMap _ _ (stabilizerRoot (F := F) ζ (M / N))) = algebraMap _ _ (stabilizerRoot (F := F) ζ (M / N)) →
        σ = 1 := by
    intro σ hσ
    apply decompositionHom_injective v (stabilizerPlace (F := F) ζ (M / N) u)
    rw [map_one]
    apply eq_one_of_apply_stabilizerRoot
    apply (algebraMap (stabilizerField (F := F) ζ (M / N))
      ((stabilizerPlace (F := F) ζ (M / N) u).adicCompletion
        (stabilizerField (F := F) ζ (M / N)))).injective
    rw [algebraMap_decompositionHom]
    exact hσ
  -- `N` is invertible in the residue field of `F_v`
  have hN : ((N : ℕ) : ResidueField (v.adicCompletionIntegers F)) ≠ 0 := by
    intro h
    apply hNv
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]
    apply (Langlands.Global.CompletionResidue.adicResidueEquiv F v).injective
    rw [map_natCast, map_zero]
    exact h
  have hcard : Nat.card (𝓞 F ⧸ v.asIdeal) =
      Nat.card (ResidueField (v.adicCompletionIntegers F)) :=
    Nat.card_congr (Langlands.Global.CompletionResidue.adicResidueEquiv F v).toEquiv
  obtain ⟨φ, hg, hφα, hχ⟩ := exists_frobenius_coordinate (padicField v)
    ((stabilizerPlace (F := F) ζ (M / N) u).adicCompletion (stabilizerField (F := F) ζ (M / N)))
    (v.adicCompletionIntegers F) (mem_adicCompletionIntegers_iff v) hN hα hfaith
  rw [← hcard] at hφα
  -- the Frobenius acts on `ζ ^ (M / N)` by `q = |𝓞 F / v|`
  have hφU : decompositionHom v (stabilizerPlace (F := F) ζ (M / N) u) φ
      (stabilizerRoot (F := F) ζ (M / N)) = stabilizerRoot (F := F) ζ (M / N) ^ Nat.card (𝓞 F ⧸ v.asIdeal) := by
    apply (algebraMap (stabilizerField (F := F) ζ (M / N))
      ((stabilizerPlace (F := F) ζ (M / N) u).adicCompletion
        (stabilizerField (F := F) ζ (M / N)))).injective
    rw [algebraMap_decompositionHom, hφα, map_pow]
  -- the cyclotomic character of the local Galois group is injective and sends `φ` to `q`
  let ψ := (hζU.autToPow F).comp (decompositionHom v (stabilizerPlace (F := F) ζ (M / N) u))
  have hψ : Function.Injective ψ :=
    (autToPow_stabilizerRoot_injective hζU).comp (decompositionHom_injective v _)
  have hζφ : stabilizerRoot (F := F) ζ (M / N) ^ ((ψ φ : (ZMod N)ˣ) : ZMod N).val =
      stabilizerRoot (F := F) ζ (M / N) ^ Nat.card (𝓞 F ⧸ v.asIdeal) := by
    rw [← hφU]
    exact hζU.autToPow_spec F _
  have hψφ := (pow_eq_pow_iff_natCast_eq hζU _ _).1 hζφ
  rw [ZMod.natCast_zmod_val] at hψφ
  have horder : orderOf ((Nat.card (𝓞 F ⧸ v.asIdeal) : ℕ) : ZMod N) =
      Nat.card ((stabilizerPlace (F := F) ζ (M / N) u).adicCompletion
        (stabilizerField (F := F) ζ (M / N)) ≃ₐ[v.adicCompletion F]
        (stabilizerPlace (F := F) ζ (M / N) u).adicCompletion
          (stabilizerField (F := F) ζ (M / N))) := by
    rw [← hψφ, orderOf_units, orderOf_injective ψ hψ, orderOf_eq_card_of_forall_mem_zpowers hg]
  have he : NeZero (Nat.card ((stabilizerPlace (F := F) ζ (M / N) u).adicCompletion
      (stabilizerField (F := F) ζ (M / N)) ≃ₐ[v.adicCompletion F]
      (stabilizerPlace (F := F) ζ (M / N) u).adicCompletion
        (stabilizerField (F := F) ζ (M / N)))) := ⟨Nat.card_pos.ne'⟩
  obtain ⟨χ, hχar, hχ1⟩ := @hχ _ he rfl
  refine ⟨_, he, horder.symm, χ, hχar, fun π hπ => ?_⟩
  rw [hχ1]
  apply eq_of_apply_stabilizerRoot_eq
  rw [hφU, restrictNormal_stabilizerRoot hζ, pow_eq_pow_iff_natCast_eq hζU]
  -- the Artin symbol of an element of order `1` acts on `ζ ^ (M / N)` by `p ^ f = q`
  have hcop := coprime_of_natCast_ne_zero (padicField v) (v.adicCompletionIntegers F)
    (mem_adicCompletionIntegers_iff v) hN
  have hd : N ∣ M / residuePrime v ^ M.factorization (residuePrime v) := by
    apply (hcop.pow_left (M.factorization (residuePrime v))).symm.dvd_of_dvd_mul_left
    rw [Nat.ordProj_mul_ordCompl_eq_self]
    exact hNM
  have h := castHom_autToPow_artinSymbol hζ hinj v hNM hd π hπ
  rw [ZMod.castHom_apply, ZMod.cast_eq_val] at h
  rw [h, hcard, card_residueField_eq_pow (padicField v) (v.adicCompletionIntegers F)
    (mem_adicCompletionIntegers_iff v)]

end Main

end UnramifiedCyclotomic

end Langlands.ClassField.Global
