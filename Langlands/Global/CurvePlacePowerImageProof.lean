import Langlands.Global.CurvePlacePowerImageStatement
import Langlands.Global.NumberFieldPowerImageProof
import Langlands.Global.CurvePlaceExtension
import Langlands.Global.FunctionFieldPlaceResidueProof

/-! # Proof that power maps have non-open image on function-field adelic units -/

noncomputable section

universe u

open Filter Topology IsDedekindDomain Polynomial AlgebraicCurve
open scoped RestrictedProduct

namespace Langlands.Global

section FiniteField

variable (k : Type u) [Field k] [Finite k]

/-- Over a finite field there is an irreducible polynomial of every positive degree. -/
theorem finiteField_exists_irreducible_natDegree {d : ℕ} (hd : d ≠ 0) :
    ∃ f : k[X], Irreducible f ∧ f.natDegree = d := by
  obtain ⟨p, hp⟩ := CharP.exists k
  have : Fact p.Prime := ⟨CharP.char_is_prime k p⟩
  have : NeZero d := ⟨hd⟩
  let pb := Field.powerBasisOfFiniteOfSeparable k (FiniteField.Extension k p d)
  refine ⟨minpoly k pb.gen, minpoly.irreducible pb.isIntegral_gen, ?_⟩
  rw [pb.natDegree_minpoly, ← pb.finrank, FiniteField.finrank_extension]

/-- A prime different from the characteristic divides `|k| ^ ((ℓ - 1) * j) - 1`. -/
theorem prime_dvd_card_pow_mul_sub_one {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓk : ℓ ≠ ringChar k)
    (j : ℕ) : ℓ ∣ Nat.card k ^ ((ℓ - 1) * j) - 1 := by
  have : Fintype k := Fintype.ofFinite k
  obtain ⟨r, hp, hq⟩ := FiniteField.card k (ringChar k)
  have hcop : (Nat.card k).Coprime ℓ := by
    rw [Nat.card_eq_fintype_card, hq]
    exact Nat.Coprime.pow_left _ ((Nat.coprime_primes hp hℓ).mpr (Ne.symm hℓk))
  have h := (Nat.ModEq.pow_totient hcop).pow j
  rw [Nat.totient_prime hℓ, one_pow, ← pow_mul] at h
  exact (Nat.modEq_iff_dvd' (Nat.one_le_pow _ _ Nat.card_pos)).mp h.symm

omit [Finite k] in
/-- The residue field at the place of an irreducible polynomial has `|k| ^ deg` elements. -/
theorem ratFuncPlace_natCard_residueField {f : k[X]} (hf : Irreducible f) :
    Nat.card (RationalFunctionField.finitePlace k hf).ResidueField =
      Nat.card k ^ f.natDegree := by
  have hdeg : Module.finrank k (RationalFunctionField.finitePlace k hf).ResidueField =
      f.natDegree :=
    RationalFunctionField.deg_finitePlace k hf
  have : Module.Finite k (RationalFunctionField.finitePlace k hf).ResidueField :=
    Module.finite_of_finrank_pos (by rw [hdeg]; exact hf.natDegree_pos)
  rw [Module.natCard_eq_pow_finrank (K := k), hdeg]

end FiniteField

section Extension

variable {k F : Type u} [Field k] [Field F] [Algebra k F] [Algebra (RatFunc k) F]
  [IsScalarTower k (RatFunc k) F] [FunctionField k F]

/-- The inclusion of the valuation ring of a rational place into that of its chosen
extension. -/
def curvePlaceExtensionIntegersMap (p : Place k (RatFunc k)) :
    p.toValuationSubring →+* (curvePlaceExtension (F := F) p).toValuationSubring where
  toFun x := ⟨algebraMap (RatFunc k) F x, curvePlaceExtension_mem p x.2⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' x y := Subtype.ext (map_mul _ (x : RatFunc k) y)
  map_zero' := Subtype.ext (map_zero _)
  map_add' x y := Subtype.ext (map_add _ (x : RatFunc k) y)

/-- The residue map from a rational place to the residue ring of its chosen extension. -/
def curvePlaceExtensionResidueMap (p : Place k (RatFunc k)) :
    p.ResidueField →+* (curvePlaceExtension (F := F) p).toValuationSubring ⧸
      (curvePlaceExtension (F := F) p).heightOneSpectrum.asIdeal :=
  Ideal.quotientMap _ (curvePlaceExtensionIntegersMap p) (fun x hx =>
    ValuationSubring.coe_mem_nonunits_iff.mp (curvePlaceExtension_dominates p x hx))

end Extension

section Places

variable (k F : Type u) [Field k] [Finite k] [Field F] [Algebra k F] [Algebra (RatFunc k) F]
  [IsScalarTower k (RatFunc k) F] [FunctionField k F]

/-- The residue rings of actual curve places are finite. -/
theorem curvePlace_finite_residue (v : Place k F) :
    Finite (v.toValuationSubring ⧸ v.heightOneSpectrum.asIdeal) := by
  have : Module.Finite k v.ResidueField := functionFieldPlaceResidue k F v
  exact Module.finite_of_finite k (M := v.ResidueField)

/-- For a prime `ℓ` different from the characteristic, there are infinitely many actual
curve places whose residue fields have cardinality `≡ 1 [MOD ℓ]`. -/
theorem exists_curvePlace_embedding_card_modEq_one {ℓ : ℕ} (hℓ : ℓ.Prime)
    (hℓk : ℓ ≠ ringChar k) :
    ∃ e : ℕ ↪ Place k F, ∀ m,
      ℓ ∣ Nat.card ((e m).toValuationSubring ⧸ (e m).heightOneSpectrum.asIdeal) - 1 := by
  have hℓ1 : ℓ - 1 ≠ 0 := by have := hℓ.two_le; omega
  have hdeg : ∀ j : ℕ, ∃ f : k[X], Irreducible f ∧ f.natDegree = (ℓ - 1) * (j + 1) :=
    fun j => finiteField_exists_irreducible_natDegree k (Nat.mul_ne_zero hℓ1 j.succ_ne_zero)
  choose f hf hfd using hdeg
  let p : ℕ → Place k (RatFunc k) := fun j => RationalFunctionField.finitePlace k (hf j)
  let e : ℕ → Place k F := fun j => curvePlaceExtension (F := F) (p j)
  have hpdeg : ∀ j, (p j).deg = (ℓ - 1) * (j + 1) := fun j =>
    (RationalFunctionField.deg_finitePlace k (hf j)).trans (hfd j)
  have he : Function.Injective e := by
    intro i j hij
    have hp : (p i).toValuationSubring = (p j).toValuationSubring :=
      calc (p i).toValuationSubring
          = (e i).toValuationSubring.comap (algebraMap (RatFunc k) F) :=
            (curvePlaceExtension_comap (p i)).symm
        _ = (e j).toValuationSubring.comap (algebraMap (RatFunc k) F) := by rw [hij]
        _ = (p j).toValuationSubring := curvePlaceExtension_comap (p j)
    have hd := congrArg Place.deg (Place.ext hp)
    rw [hpdeg, hpdeg] at hd
    have := Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hℓ1) hd
    omega
  refine ⟨⟨e, he⟩, fun j => ?_⟩
  have hlow : ℓ ∣ Nat.card (p j).ResidueField - 1 := by
    rw [ratFuncPlace_natCard_residueField k (hf j), hfd]
    exact prime_dvd_card_pow_mul_sub_one k hℓ hℓk (j + 1)
  have : Finite ((e j).toValuationSubring ⧸ (e j).heightOneSpectrum.asIdeal) :=
    curvePlace_finite_residue k F (e j)
  let : Field ((e j).toValuationSubring ⧸ (e j).heightOneSpectrum.asIdeal) :=
    Ideal.Quotient.field _
  let ψ := curvePlaceExtensionResidueMap (F := F) (p j)
  have hdvd := Subgroup.card_dvd_of_injective (Units.map ψ.toMonoidHom)
    (Units.map_injective (f := ψ.toMonoidHom) ψ.injective)
  rw [Nat.card_units, Nat.card_units] at hdvd
  exact hlow.trans hdvd

end Places

section Assembly

variable (k F : Type u) [Field k] [Finite k] [Field F] [Algebra k F] [Algebra (RatFunc k) F]
  [IsScalarTower k (RatFunc k) F] [FunctionField k F]

/-- Power maps of exponent at least `2` and prime to the characteristic have non-open image
on function-field adelic units. -/
theorem curvePlace_units_powerImage_not_open {n : ℕ} (hn : 2 ≤ n) (hnk : ¬ ringChar k ∣ n) :
    ¬ IsOpen (Set.range (fun x : (CurvePlaceAdeleRing k F)ˣ => x ^ n)) := by
  classical
  obtain ⟨ℓ, hℓ, hℓn⟩ := Nat.exists_prime_and_dvd (show n ≠ 1 by omega)
  have hn0 : n ≠ 0 := by omega
  have hℓk : ℓ ≠ ringChar k := fun h => hnk (h ▸ hℓn)
  obtain ⟨e, he⟩ := exists_curvePlace_embedding_card_modEq_one k F hℓ hℓk
  have hres : ∀ v : Place k F, ∃ c : v.toValuationSubring,
      c ∉ v.heightOneSpectrum.asIdeal ∧
        (v ∈ Set.range e → ∀ a : v.toValuationSubring,
          a ^ n - c ∉ v.heightOneSpectrum.asIdeal) := by
    intro v
    by_cases hv : v ∈ Set.range e
    · obtain ⟨m, rfl⟩ := hv
      have : Finite ((e m).toValuationSubring ⧸ (e m).heightOneSpectrum.asIdeal) :=
        curvePlace_finite_residue k F (e m)
      obtain ⟨c, hc⟩ := exists_not_pow_mod (e m).heightOneSpectrum.asIdeal hℓ hn0 hℓn (he m)
      refine ⟨c, ?_, fun _ => hc⟩
      have := hc 0
      rwa [zero_pow hn0, zero_sub, Ideal.neg_mem_iff] at this
    · exact ⟨1, (Ideal.ne_top_iff_one _).mp v.heightOneSpectrum.isPrime.ne_top,
        fun h => absurd h hv⟩
  choose c hc0 hc using hres
  let ι := fun v : Place k F => algebraMap F (curvePlaceCompletion v)
  let cv : ∀ v : Place k F, curvePlaceCompletion v :=
    fun v => ι v (algebraMap v.toValuationSubring F (c v))
  have hcvv : ∀ v, Valued.v (cv v) = 1 := by
    intro v
    have h := HeightOneSpectrum.valuedAdicCompletion_eq_valuation' (v := v.heightOneSpectrum)
      (K := F) (algebraMap v.toValuationSubring F (c v))
    rw [HeightOneSpectrum.valuation_of_algebraMap] at h
    exact h.trans ((v.heightOneSpectrum.intValuation_eq_one_iff_mem_primeCompl (c v)).mpr (hc0 v))
  have hcv0 : ∀ v, cv v ≠ 0 := by
    intro v h
    have := hcvv v
    rw [h, map_zero] at this
    exact zero_ne_one this
  let A : ∀ v : Place k F, Subring (curvePlaceCompletion v) :=
    fun v => (curvePlaceCompletionIntegers v).toSubring
  let a : ∀ v, A v := fun v => ⟨cv v, (hcvv v).le⟩
  let b : ∀ v, A v := fun v =>
    ⟨(cv v)⁻¹, show Valued.v (cv v)⁻¹ ≤ 1 by rw [map_inv₀, hcvv v, inv_one]⟩
  have ha : ∀ v, (a v : curvePlaceCompletion v) ≠ 0 := hcv0
  have hb : ∀ v, (b v : curvePlaceCompletion v) ≠ 0 := fun v => inv_ne_zero (hcv0 v)
  have hab : ∀ v, (b v : curvePlaceCompletion v) = (a v : curvePlaceCompletion v)⁻¹ :=
    fun _ => rfl
  let u : ℕ → (CurvePlaceAdeleRing k F)ˣ := fun m => restrictedUnitAtPlace A a ha (e m)
  apply not_isOpen_range_pow_of_tendsto n u
  · apply units_tendsto_one
    · exact tendsto_restrictedUnitAtPlace_val A a ha e
    · exact (tendsto_restrictedUnitAtPlace_val A b hb e).congr
        (fun m => (restrictedUnitAtPlace_inv_val A a ha b hb hab (e m)).symm)
  · rintro m ⟨y, hy⟩
    have h1 : (u m : CurvePlaceAdeleRing k F) (e m) = cv (e m) := by
      change ((restrictedUnitAtPlace A a ha (e m)).val) (e m) = _
      rw [restrictedUnitAtPlace_val_apply]
      exact ite_eq_left_of_eq_true _ _ (eq_self _)
    have h2 : (u m : CurvePlaceAdeleRing k F) (e m) =
        ((y : CurvePlaceAdeleRing k F) (e m)) ^ n := by
      rw [← hy, Units.val_pow_eq_pow_val]
      exact RestrictedProduct.pow_apply _ (y : CurvePlaceAdeleRing k F) n (e m)
    exact not_pow_in_adicCompletion (K := F) (e m).heightOneSpectrum hn0
      (hc (e m) ⟨m, rfl⟩) _ (h2.symm.trans h1)

end Assembly

open Langlands.AlgebraicGeometry.PointTopology in
/-- Proof of `CurvePlacePowerImageStatement`. -/
theorem curvePlacePowerImage : CurvePlacePowerImageStatement.{u} := by
  intro k F _ _ _ _ _ _ _ n hn hnk
  exact ⟨curvePlace_units_powerImage_not_open k F hn hnk, fun R _ _ =>
    schemePoints_powerImage_not_open (CurvePlaceAdeleRing k F) n
      (curvePlace_units_powerImage_not_open k F hn hnk) R⟩

end Langlands.Global
