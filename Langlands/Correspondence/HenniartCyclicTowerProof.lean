import Langlands.Correspondence.HenniartCyclicTower
import Langlands.LocalFactor.Ramification.Herbrand.KummerStepUpperSupProof
import Mathlib.GroupTheory.QuotientGroup.Simple
import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
# Cyclic prime-degree towers reaching the close range

Use the actual Kummer break at natural inputs and first adjoin a primitive
root of unity by prime-degree steps in a finite abelian cyclotomic extension.
-/

noncomputable section

namespace Langlands.Henniart

open Numerical Polynomial
open Ramification.Kummer

universe uK

variable {p : ℕ} [Fact p.Prime]

private abbrev absRamIndex (F : PadicField.{uK} p) : ℕ :=
  F.canonicalTopologicalData.ramificationIndex

private def cyclicStepOfAlgebra (F L : PadicField.{uK} p)
    [Algebra F.Carrier L.Carrier] [IsScalarTower (Padic p) F.Carrier L.Carrier]
    [IsGalois F.Carrier L.Carrier] (hprime : (Module.finrank F.Carrier L.Carrier).Prime) :
    CyclicPrimeStep.{uK} p where
  base := F
  top := L
  embedding := IsScalarTower.toAlgHom (Padic p) F.Carrier L.Carrier
  isGalois := by
    change @IsGalois F.Carrier _ L.Carrier _ (algebraMap F.Carrier L.Carrier).toAlgebra
    rw [toAlgebra_algebraMap]
    infer_instance
  card_prime := by
    have : FiniteDimensional F.Carrier L.Carrier :=
      Module.Finite.right (Padic p) F.Carrier L.Carrier
    change (Nat.card (@AlgEquiv F.Carrier L.Carrier L.Carrier _ _ _
      (algebraMap F.Carrier L.Carrier).toAlgebra
      (algebraMap F.Carrier L.Carrier).toAlgebra)).Prime
    rw [toAlgebra_algebraMap, IsGalois.card_aut_eq_finrank]
    exact hprime

private theorem herbrandPsi_congr_algebra (F L : PadicField.{uK} p)
    {A B : Algebra F.Carrier L.Carrier} (h : A = B)
    (hA : @IsScalarTower (Padic p) F.Carrier L.Carrier _ A.toSMul _)
    (hB : @IsScalarTower (Padic p) F.Carrier L.Carrier _ B.toSMul _) :
    @Ramification.Padic.herbrandPsi p _ L L.canonicalTopologicalData F.Carrier _ _ A hA =
      @Ramification.Padic.herbrandPsi p _ L L.canonicalTopologicalData F.Carrier _ _ B hB := by
  subst B
  rfl

private theorem cyclicStepOfAlgebra_herbrandPsi (F L : PadicField.{uK} p)
    [Algebra F.Carrier L.Carrier] [IsScalarTower (Padic p) F.Carrier L.Carrier]
    [IsGalois F.Carrier L.Carrier] (hprime : (Module.finrank F.Carrier L.Carrier).Prime) :
    (cyclicStepOfAlgebra F L hprime).herbrandPsi =
      Ramification.Padic.herbrandPsi L.canonicalTopologicalData F.Carrier :=
  herbrandPsi_congr_algebra F L toAlgebra_algebraMap _ _

private theorem step_herbrandPsi_strictMono (S : CyclicPrimeStep.{uK} p) :
    StrictMono S.herbrandPsi := by
  let := S.algebra
  have := Weil.Local.extensionAlgebra_isScalarTower S.base S.top S.embedding
  exact Ramification.Padic.herbrandPsi_strictMono S.top.canonicalTopologicalData S.base.Carrier

/-- A Kummer step with the bound on the inverse function needed at natural inputs. -/
private theorem exists_kummerStep (F : PadicField.{uK} p) {ζ : F.Carrier}
    (hζ : IsPrimitiveRoot ζ p) :
    ∃ S : CyclicPrimeStep.{uK} p, S.base = F ∧
      (∃ z : S.top.Carrier, IsPrimitiveRoot z p) ∧
      absRamIndex S.top = p * absRamIndex F ∧
      ∀ n : ℕ, S.herbrandPsi n ≤
        max (n : ℝ) ((p : ℝ) * n - (p : ℝ) * absRamIndex F) := by
  have : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  let ϖ := F.canonicalTopologicalData.uniformizer
  have hϖ : F.canonicalTopologicalData.ord ϖ = 1 := F.canonicalTopologicalData.ord_uniformizer
  have hirr := kummerStep_polynomial_irreducible F hϖ
  let E := ClassFieldTheory.Local.KummerNorm.radicalField F.Carrier p ϖ
  have : FiniteDimensional (Padic p) E := FiniteDimensional.trans (Padic p) F.Carrier E
  let L : PadicField.{uK} p := PadicField.ofField E
  let : Algebra F.Carrier L.Carrier := (inferInstance : Algebra F.Carrier E)
  have : IsScalarTower (Padic p) F.Carrier L.Carrier :=
    (inferInstance : IsScalarTower (Padic p) F.Carrier E)
  have : FiniteDimensional F.Carrier L.Carrier :=
    (inferInstance : FiniteDimensional F.Carrier E)
  have : IsGalois F.Carrier L.Carrier :=
    (ClassFieldTheory.Local.KummerNorm.radicalField_isAbelianGalois hirr hζ).toIsGalois
  have hd : Module.finrank F.Carrier L.Carrier = p :=
    ClassFieldTheory.Local.KummerNorm.radicalField_finrank hirr hζ
  have hprime : (Module.finrank F.Carrier L.Carrier).Prime := hd.symm ▸ Fact.out
  let S := cyclicStepOfAlgebra F L hprime
  let β : L.Carrier := rootOfSplitsXPowSubC (NeZero.pos p) ϖ E
  have hβ : β ^ p = algebraMap F.Carrier L.Carrier ϖ := rootOfSplitsXPowSubC_pow ϖ E
  have he := (uniformizer_radical_arithmetic F L hϖ hβ hd).2.1
  have hgen := adjoin_radical_eq_top F L hϖ hβ hd
  obtain ⟨t, ht, hpattern⟩ := galois_radical_lower_break F L hϖ hβ hd hgen
  have hp : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have hbreak : (t : ℝ) * ((p : ℝ) - 1) = (p : ℝ) * absRamIndex F :=
    (eq_div_iff (sub_ne_zero.mpr hp.ne')).mp ht
  refine ⟨S, rfl, ⟨algebraMap F.Carrier L.Carrier ζ,
    hζ.map_of_injective (algebraMap F.Carrier L.Carrier).injective⟩, he, ?_⟩
  intro n
  change (cyclicStepOfAlgebra F L hprime).herbrandPsi n ≤ _
  rw [cyclicStepOfAlgebra_herbrandPsi,
    LocalClassField.herbrandPsi_nat_of_prime_pattern F L L.canonicalTopologicalData
      hprime t hpattern, hd]
  split_ifs with hn
  · exact le_max_left _ _
  · push_cast [Nat.cast_sub (Nat.le_of_not_ge hn)]
    have hlin : (t : ℝ) + (p : ℝ) * ((n : ℝ) - t) =
        (p : ℝ) * n - (p : ℝ) * absRamIndex F := by
      linear_combination -hbreak
    rw [hlin]
    exact le_max_right _ _

/-- A strict slope bound by `(n + 1)e` gives a nonempty Kummer tower. -/
private theorem reaches_of_primitiveRoot_aux (n : ℕ) (F : PadicField.{uK} p)
    (hζ : ∃ ζ : F.Carrier, IsPrimitiveRoot ζ p) (x : ℝ)
    (hx : x < ((n + 1) * absRamIndex F : ℕ)) : ReachesCloseRange F x := by
  induction n generalizing F x with
  | zero =>
    obtain ⟨ζ, hz⟩ := hζ
    obtain ⟨S, hS, _, he, hψ⟩ := exists_kummerStep F hz
    subst F
    have hlt : x < (absRamIndex S.base : ℝ) := by simpa only [zero_add, one_mul] using hx
    have hp : (1 : ℝ) ≤ p := by exact_mod_cast (Fact.out : p.Prime).one_le
    have hlarge : (absRamIndex S.base : ℝ) ≤ (absRamIndex S.top : ℝ) := by
      rw [he, Nat.cast_mul]
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hp (Nat.cast_nonneg (absRamIndex S.base))
    apply ReachesCloseRange.last S x
    refine ((step_herbrandPsi_strictMono S) hlt).trans_le ((hψ _).trans ?_)
    rw [sub_self]
    exact max_le hlarge (Nat.cast_nonneg _)
  | succ n ih =>
    obtain ⟨ζ, hz⟩ := hζ
    obtain ⟨S, hS, hroot, he, hψ⟩ := exists_kummerStep F hz
    subst F
    apply ReachesCloseRange.step S x
    apply ih S.top hroot (S.herbrandPsi x)
    refine ((step_herbrandPsi_strictMono S) hx).trans_le ((hψ _).trans ?_)
    rw [he]
    push_cast
    have hp : (2 : ℝ) ≤ p := by exact_mod_cast (Fact.out : p.Prime).two_le
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg _
    have hcoef : (n : ℝ) + 1 + 1 ≤ ((n : ℝ) + 1) * p := calc
      _ ≤ ((n : ℝ) + 1) * 2 := by linarith
      _ ≤ ((n : ℝ) + 1) * p := mul_le_mul_of_nonneg_left hp (by positivity)
    refine max_le ?_ ?_
    · rw [← mul_assoc]
      exact mul_le_mul_of_nonneg_right hcoef (Nat.cast_nonneg _)
    · apply le_of_eq
      ring

private theorem reaches_of_primitiveRoot (F : PadicField.{uK} p)
    (hζ : ∃ ζ : F.Carrier, IsPrimitiveRoot ζ p) (x : ℝ) : ReachesCloseRange F x := by
  have he : (0 : ℝ) < absRamIndex F := by
    exact_mod_cast F.canonicalTopologicalData.ramificationIndex_pos
  obtain ⟨n, hn⟩ := exists_nat_gt (x / (absRamIndex F : ℝ))
  apply reaches_of_primitiveRoot_aux n F hζ x
  rw [Nat.cast_mul, ← div_lt_iff₀ he]
  exact hn.trans_le (by exact_mod_cast Nat.le_succ n)

open scoped IsMulCommutative in
/-- Pull back through a finite abelian Galois extension containing a primitive
root. Each induction step first passes to the fixed field of a maximal subgroup. -/
private theorem reaches_of_abelian (L : PadicField.{uK} p) (ζ : L.Carrier)
    (hζ : IsPrimitiveRoot ζ p) (d : ℕ) :
    ∀ (F : PadicField.{uK} p) [Algebra F.Carrier L.Carrier]
      [IsScalarTower (Padic p) F.Carrier L.Carrier] [IsAbelianGalois F.Carrier L.Carrier],
      Module.finrank F.Carrier L.Carrier = d → ∀ x, ReachesCloseRange F x := by
  induction d using Nat.strong_induction_on with
  | h d ih =>
    intro F _ _ _ hd x
    have : FiniteDimensional F.Carrier L.Carrier :=
      Module.Finite.right (Padic p) F.Carrier L.Carrier
    by_cases h1 : d = 1
    · obtain ⟨z, hz⟩ := (finrank_eq_one_iff_of_nonzero' (1 : L.Carrier) one_ne_zero).mp
        (hd.trans h1) ζ
      rw [Algebra.smul_def, mul_one] at hz
      have hmap : IsPrimitiveRoot (algebraMap F.Carrier L.Carrier z) p := by rwa [hz]
      exact reaches_of_primitiveRoot F ⟨z, hmap.of_map_of_injective
        (f := algebraMap F.Carrier L.Carrier) (algebraMap F.Carrier L.Carrier).injective⟩ x
    · let G := L.Carrier ≃ₐ[F.Carrier] L.Carrier
      have hc : Nat.card G = d := (IsGalois.card_aut_eq_finrank F.Carrier L.Carrier).trans hd
      have : Nontrivial G := Finite.one_lt_card_iff_nontrivial.mp (by
        rw [hc]
        have hdpos : 0 < d := hd ▸ (Module.finrank_pos : 0 < Module.finrank F.Carrier L.Carrier)
        omega)
      have : Finite (Subgroup G) :=
        Finite.of_injective (fun H : Subgroup G => (H : Set G)) SetLike.coe_injective
      obtain ⟨H, hH, _⟩ := (eq_top_or_exists_le_coatom (⊥ : Subgroup G)).resolve_left bot_ne_top
      let M₀ := IntermediateField.fixedField H
      have : FiniteDimensional (Padic p) M₀ := FiniteDimensional.trans (Padic p) F.Carrier M₀
      let M : PadicField.{uK} p := PadicField.ofField M₀
      let : Algebra F.Carrier M.Carrier := (inferInstance : Algebra F.Carrier M₀)
      let : Algebra M.Carrier L.Carrier := (inferInstance : Algebra M₀ L.Carrier)
      have : IsScalarTower (Padic p) F.Carrier M.Carrier :=
        (inferInstance : IsScalarTower (Padic p) F.Carrier M₀)
      have : IsScalarTower (Padic p) M.Carrier L.Carrier :=
        (inferInstance : IsScalarTower (Padic p) M₀ L.Carrier)
      have : IsScalarTower F.Carrier M.Carrier L.Carrier :=
        (inferInstance : IsScalarTower F.Carrier M₀ L.Carrier)
      have : FiniteDimensional M.Carrier L.Carrier :=
        Module.Finite.right (Padic p) M.Carrier L.Carrier
      have : IsAbelianGalois F.Carrier M.Carrier :=
        inferInstanceAs (IsAbelianGalois F.Carrier ↥M₀)
      have : IsAbelianGalois M.Carrier L.Carrier :=
        inferInstanceAs (IsAbelianGalois ↥M₀ L.Carrier)
      have hprime : (Module.finrank F.Carrier M.Carrier).Prime := by
        change (Module.finrank F.Carrier ↥M₀).Prime
        rw [IntermediateField.finrank_eq_fixingSubgroup_index,
          IntermediateField.fixingSubgroup_fixedField]
        exact CommGroup.is_simple_iff_prime_card.mp (CommGroup.isSimpleGroup_iff_isCoatom.mpr hH)
      have hdeg : Module.finrank F.Carrier M.Carrier * Module.finrank M.Carrier L.Carrier = d :=
        (Module.finrank_mul_finrank F.Carrier M.Carrier L.Carrier).trans hd
      have hlt : Module.finrank M.Carrier L.Carrier < d := by
        rw [← hdeg]
        exact lt_mul_of_one_lt_left Module.finrank_pos hprime.one_lt
      let S := cyclicStepOfAlgebra F M hprime
      exact ReachesCloseRange.step S x (ih _ hlt M rfl (S.herbrandPsi x))

/-- Every nonnegative slope enters the close range after finitely many cyclic
prime-degree steps. -/
theorem cyclicTower : CyclicTowerStatement.{uK} := by
  intro p _ F x _
  have : CharZero F.Carrier := Algebra.charZero_of_charZero (Padic p) F.Carrier
  have : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (AlgebraicClosure F.Carrier) p
  let E₀ := IntermediateField.adjoin F.Carrier {ζ}
  have : FiniteDimensional F.Carrier E₀ :=
    IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral ζ)
  have : FiniteDimensional (Padic p) E₀ := FiniteDimensional.trans (Padic p) F.Carrier E₀
  let E : PadicField.{uK} p := PadicField.ofField E₀
  let : Algebra F.Carrier E.Carrier := (inferInstance : Algebra F.Carrier E₀)
  have : IsScalarTower (Padic p) F.Carrier E.Carrier :=
    (inferInstance : IsScalarTower (Padic p) F.Carrier E₀)
  have : IsCyclotomicExtension {p} F.Carrier E₀ :=
    (IntermediateField.isCyclotomicExtension_singleton_iff_eq_adjoin
      p F.Carrier (AlgebraicClosure F.Carrier) E₀ hζ).mpr rfl
  have : IsAbelianGalois F.Carrier E.Carrier := IsCyclotomicExtension.isAbelianGalois {p} F.Carrier E₀
  let z : E₀ := ⟨ζ, IntermediateField.subset_adjoin F.Carrier {ζ} (Set.mem_singleton ζ)⟩
  have hz : IsPrimitiveRoot z p := hζ.of_map_of_injective (f := E₀.val) E₀.val.injective
  exact reaches_of_abelian E z hz _ F rfl x

end Langlands.Henniart
