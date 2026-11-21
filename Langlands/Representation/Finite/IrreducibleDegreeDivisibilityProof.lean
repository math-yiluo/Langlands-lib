import Langlands.Representation.Finite.IrreducibleDegreeDivisibility
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.RepresentationTheory.Character
import Mathlib.Algebra.GCDMonoid.IntegrallyClosed
import Mathlib.GroupTheory.PGroup
import Mathlib.RingTheory.Finiteness.Finsupp

/-!
# The character-integrality proof of degree divisibility
-/

noncomputable section

open scoped MonoidAlgebra

namespace Langlands

private def conjFiber {G : Type*} [Group G] [Fintype G] (c : ConjClasses G) : Finset G := by
  classical
  exact Finset.univ.filter (fun g => ConjClasses.mk g = c)

private theorem mk_conj_eq {G : Type*} [Group G] (g h : G) :
    ConjClasses.mk (h * g * h⁻¹) = ConjClasses.mk g :=
  (ConjClasses.mk_eq_mk_iff_isConj.mpr (isConj_iff.mpr ⟨h, rfl⟩)).symm

section ClassSum

variable {G V : Type*} [Group G] [Fintype G] [AddCommGroup V] [Module ℂ V]
  [FiniteDimensional ℂ V] [Nontrivial V] (ρ : Representation ℂ G V) [ρ.IsIrreducible]

/-- The trace of the conjugacy-class sum divided by the degree is integral:
this number is the scalar by which the integral class sum acts. -/
private theorem isIntegral_classTraceDiv (c : ConjClasses G) :
    IsIntegral ℤ ((∑ g ∈ conjFiber c, ρ.character g) / (Module.finrank ℂ V : ℂ)) := by
  classical
  let B : Module.End ℂ V := ∑ g ∈ conjFiber c, ρ g
  have hcomm (h : G) : ρ h * B = B * ρ h := by
    have hinv : (∑ g ∈ conjFiber c, ρ (h * g * h⁻¹)) = B := by
      refine Finset.sum_equiv (MulAut.conj h).toEquiv ?_ (fun _ _ => rfl)
      intro g
      change g ∈ conjFiber c ↔ h * g * h⁻¹ ∈ conjFiber c
      simp only [conjFiber, Finset.mem_filter, Finset.mem_univ, true_and, mk_conj_eq]
    calc
      ρ h * B = ∑ g ∈ conjFiber c, ρ (h * g * h⁻¹) * ρ h := by
        dsimp only [B]
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun g _ => ?_
        rw [← map_mul, ← map_mul]
        simp [mul_assoc]
      _ = B * ρ h := by rw [← Finset.sum_mul, hinv]
  let U : ρ.IntertwiningMap ρ := ⟨B, fun h => (hcomm h).symm⟩
  obtain ⟨a, ha⟩ := (Representation.IsIrreducible.algebraMap_intertwiningMap_bijective_of_isAlgClosed
    (ρ := ρ)).2 U
  have ha' : a • (1 : Module.End ℂ V) = B :=
    congrArg Representation.IntertwiningMap.toLinearMap ha
  have hB : IsIntegral ℤ B := by
    let φ : ℤ[G] →ₐ[ℤ] Module.End ℂ V := MonoidAlgebra.lift ℤ (Module.End ℂ V) G ρ
    have h := (IsIntegral.of_finite ℤ (∑ g ∈ conjFiber c, MonoidAlgebra.single g (1 : ℤ))).map φ
    simpa only [φ, B, map_sum, MonoidAlgebra.lift_single, one_smul] using h
  have hI : IsIntegral ℤ a :=
    (isIntegral_algebraMap_iff (R := ℤ) (B := Module.End ℂ V)).mp (by
      change IsIntegral ℤ (a • (1 : Module.End ℂ V))
      rw [ha']
      exact hB)
  have htrace := congrArg (LinearMap.trace ℂ V) ha'
  change (LinearMap.trace ℂ V) (a • (1 : Module.End ℂ V)) =
    (LinearMap.trace ℂ V) (∑ g ∈ conjFiber c, ρ g) at htrace
  simp only [map_smul, LinearMap.trace_one, map_sum, smul_eq_mul] at htrace
  change a * (Module.finrank ℂ V : ℂ) = ∑ g ∈ conjFiber c, ρ.character g at htrace
  have hn : (Module.finrank ℂ V : ℂ) ≠ 0 := by exact_mod_cast Module.finrank_pos.ne'
  rwa [← htrace, mul_div_cancel_right₀ _ hn]

end ClassSum

/-- Serre's degree divisibility: the sum of the algebraic integers attached
 to the conjugacy classes is the rational number `|G| / dim V`. -/
theorem irreducibleDegreeDivisibility.{uG, uV} : IrreducibleDegreeDivisibilityStatement.{uG, uV} := by
  intro G _ _ V _ _ _ ρ hρ
  classical
  let := Fintype.ofFinite G
  let : Finite (ConjClasses G) := Finite.of_surjective _ ConjClasses.mk_surjective
  let := Fintype.ofFinite (ConjClasses G)
  let : Nontrivial V := by
    by_contra h
    let : Subsingleton V := not_nontrivial_iff_subsingleton.mp h
    exact (bot_ne_top : (⊥ : Subrepresentation ρ) ≠ ⊤)
      (Subrepresentation.ext (Subsingleton.elim _ _))
  let n := Module.finrank ℂ V
  have hn : 0 < n := Module.finrank_pos
  have hG : (Nat.card G : ℂ) ≠ 0 := by exact_mod_cast (Nat.card_pos (α := G)).ne'
  let := invertibleOfNonzero hG
  have horth : (∑ g : G, ρ.character g * ρ.character g⁻¹) = (Nat.card G : ℂ) := by
    have h := ρ.char_orthonormal ρ
    have he : Nonempty (ρ.Equiv ρ) := ⟨Representation.Equiv.refl ρ⟩
    simp only [ite_eq_left he] at h
    apply mul_left_cancel₀ (inv_ne_zero hG)
    rw [h, inv_mul_cancel₀ hG]
  have hchoose (c : ConjClasses G) : ∃ g : G, ConjClasses.mk g = c :=
    ConjClasses.mk_surjective c
  let rep (c : ConjClasses G) := (hchoose c).choose
  have htr (c : ConjClasses G) (g : G) (hg : g ∈ conjFiber c) :
      ρ.character g⁻¹ = ρ.character (rep c)⁻¹ := by
    have hgc : ConjClasses.mk g = c := (Finset.mem_filter.mp hg).2
    obtain ⟨t, ht⟩ := isConj_iff.mp (ConjClasses.mk_eq_mk_iff_isConj.mp
      ((hchoose c).choose_spec.trans hgc.symm))
    rw [← ht]
    simp only [mul_inv_rev, inv_inv, ← mul_assoc, Representation.char_conj, rep]
  have hsplit :
      (∑ g : G, ρ.character g * ρ.character g⁻¹) / (n : ℂ) =
      ∑ c : ConjClasses G,
        ((∑ g ∈ conjFiber c, ρ.character g) / (n : ℂ)) * ρ.character (rep c)⁻¹ := by
    rw [← Finset.sum_fiberwise Finset.univ ConjClasses.mk, Finset.sum_div]
    refine Finset.sum_congr rfl fun c _ => ?_
    change (∑ g ∈ conjFiber c, ρ.character g * ρ.character g⁻¹) / (n : ℂ) = _
    rw [div_mul_eq_mul_div, Finset.sum_mul]
    congr 1
    exact Finset.sum_congr rfl fun g hg => by rw [htr c g hg]
  have hquot : IsIntegral ℤ ((Nat.card G : ℂ) / (n : ℂ)) := by
    rw [← horth, hsplit]
    exact IsIntegral.sum _ fun c _ =>
      (isIntegral_classTraceDiv ρ c).mul (ρ.isIntegral_character (rep c)⁻¹)
  have hrat : IsIntegral ℤ ((Nat.card G : ℚ) / (n : ℚ)) :=
    (isIntegral_algebraMap_iff (R := ℤ) (B := ℂ)).mp (by simpa only [map_div₀, map_natCast] using hquot)
  obtain ⟨z, hz⟩ := IsIntegrallyClosed.isIntegral_iff.mp hrat
  have hnQ : (n : ℚ) ≠ 0 := by exact_mod_cast hn.ne'
  have hmul : (z : ℚ) * (n : ℚ) = (Nat.card G : ℚ) :=
    (eq_div_iff hnQ).mp hz
  have hmulZ : (z : ℤ) * (n : ℤ) = (Nat.card G : ℤ) := by exact_mod_cast hmul
  have hdvd : (n : ℤ) ∣ (Nat.card G : ℤ) := ⟨z, by simpa only [mul_comm] using hmulZ.symm⟩
  exact_mod_cast hdvd

/-- Irreducible complex representations of a finite `p`-group have
`p`-power degree. -/
theorem irreducibleDegree_primePow_of_isPGroup {p : ℕ} [Fact p.Prime] {G V : Type*}
    [Group G] [Finite G] [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (hG : IsPGroup p G) (ρ : Representation ℂ G V) (hρ : ρ.IsIrreducible) :
    ∃ a : ℕ, Module.finrank ℂ V = p ^ a := by
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hG
  have hd := irreducibleDegreeDivisibility G V ρ hρ
  rw [hk] at hd
  obtain ⟨a, _, ha⟩ := (Nat.dvd_prime_pow (Fact.out : p.Prime)).mp hd
  exact ⟨a, ha⟩

end Langlands
