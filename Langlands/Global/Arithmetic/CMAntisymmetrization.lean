import Langlands.Global.Arithmetic.CMCharacterStatement
import Langlands.Global.HeckeCharacterTransport
import Langlands.ClassField.Global.IntegralIdeleCoefficients

/-!
# Antisymmetrization of Hecke characters on CM fields

For a Hecke character `ψ` of a CM field, `ψ * (ψ ∘ c)⁻¹` is conjugate self-dual. If `ψ` has
the infinity component of an anticyclotomic infinity type `b`, the quotient has the infinity
component of `2 * b`; if `ψ` is unramified everywhere, so is the quotient. These are the
final steps of `CMUnramifiedInfinityRealizationStatement`. See the paired Markdown.
-/

noncomputable section

universe u

namespace Langlands.Global

namespace CMUnramifiedInfinity

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open Langlands.ClassField.Global Langlands.Global.AdelicFunctoriality

variable {K : Type u} [Field K] [NumberField K]

section Unramified

/-- A Hecke character trivial on the integral ideles with trivial archimedean part is
unramified at every finite place. -/
theorem isUnramifiedAt_of_integral {ψ : HeckeCharacter K}
    (hψ : ∀ x : Ideles K, x ∈ integralIdeles K → (x : Adeles K).1 = 1 →
      ψ (ideleClassMap K x) = 1) (w : FinitePlace K) : ψ.IsUnramifiedAt w := by
  intro a ha
  have hv : Valued.v (a : FiniteCompletion K w) = 1 :=
    adicCompletionIntegers.mem_units_iff_valued_eq_one.mp ha
  apply hψ
  · intro w'
    by_cases h : w' = w
    · subst h
      change Valued.v (ideleCoordinate w' (IdeleGroup.ofAdicCompletion (𝓞 K) K w' a) :
        w'.adicCompletion K) = 1
      rw [ideleCoordinate_ofAdicCompletion_self]
      exact hv
    · change Valued.v (ideleCoordinate w' (IdeleGroup.ofAdicCompletion (𝓞 K) K w a) :
        w'.adicCompletion K) = 1
      rw [ideleCoordinate_ofAdicCompletion_of_ne h, Units.val_one, map_one]
  · rfl

end Unramified

variable [IsCMField K]

/-- The antisymmetrization `ψ * (ψ ∘ c)⁻¹` of a Hecke character of a CM field. -/
def antisymmetrize (ψ : HeckeCharacter K) : HeckeCharacter K :=
  ψ * ψ.complexConj⁻¹

theorem antisymmetrize_apply (ψ : HeckeCharacter K) (x : IdeleClasses K) :
    antisymmetrize ψ x = ψ x * (ψ (ideleClassComplexConj x))⁻¹ := rfl

/-- The antisymmetrization is conjugate self-dual. -/
theorem antisymmetrize_complexConj (ψ : HeckeCharacter K) (x : IdeleClasses K) :
    antisymmetrize ψ (ideleClassComplexConj x) = (antisymmetrize ψ x)⁻¹ := by
  rw [antisymmetrize_apply, antisymmetrize_apply, ideleClassComplexConj_involutive x,
    mul_inv, inv_inv, mul_comm]

/-- Conjugating the archimedean inclusion: the transported idele has trivial finite part. -/
theorem ideleEquiv_complexConj_infiniteIdelesInclusion (y : (InfiniteAdeles K)ˣ) :
    ideleEquiv (IsCMField.complexConj K).toRingEquiv (infiniteIdelesInclusion K y) =
      infiniteIdelesInclusion K
        (ideleProductEquiv K
          (ideleEquiv (IsCMField.complexConj K).toRingEquiv (infiniteIdelesInclusion K y))).1 := by
  apply (ideleProductEquiv K).injective
  refine Prod.ext ?_ ?_
  · change _ = (ideleProductEquiv K ((ideleProductEquiv K).symm (_, 1))).1
    rw [ContinuousMulEquiv.apply_symm_apply]
  · change _ = (ideleProductEquiv K ((ideleProductEquiv K).symm (_, 1))).2
    rw [ContinuousMulEquiv.apply_symm_apply]
    apply Units.ext
    exact map_one (finiteAdeleEquiv (IsCMField.complexConj K).toRingEquiv)

/-- Complex conjugation inverts an anticyclotomic infinity character. -/
theorem toCharacter_complexConj {b : InfinityType K} (hb : b.IsAnticyclotomic)
    (y : (InfiniteAdeles K)ˣ) :
    InfinityType.toCharacter b (ideleProductEquiv K
        (ideleEquiv (IsCMField.complexConj K).toRingEquiv (infiniteIdelesInclusion K y))).1 =
      (InfinityType.toCharacter b y)⁻¹ := by
  rw [InfinityType.toCharacter_anticyclotomic _ hb, InfinityType.toCharacter_anticyclotomic _ hb,
    ← Finset.prod_inv_distrib]
  refine Finset.prod_congr rfl fun v _ ↦ ?_
  have h : InfinityType.coordinate v (ideleProductEquiv K
      (ideleEquiv (IsCMField.complexConj K).toRingEquiv (infiniteIdelesInclusion K y))).1 =
      star (InfinityType.coordinate v y) := by
    apply Units.ext
    rw [Units.coe_star]
    exact ideleComplexConj_infinite_coordinate (infiniteIdelesInclusion K y) v
  rw [h, star_star, ← inv_zpow, inv_div]

/-- Doubling all weights squares the infinity character. -/
theorem toCharacter_two_mul (b : InfinityType K) (y : (InfiniteAdeles K)ˣ) :
    InfinityType.toCharacter (fun σ ↦ 2 * b σ) y = InfinityType.toCharacter b y ^ 2 := by
  rw [InfinityType.toCharacter_apply, InfinityType.toCharacter_apply, ← Finset.prod_pow]
  refine Finset.prod_congr rfl fun v _ ↦ ?_
  rw [mul_pow, ← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, Nat.cast_ofNat,
    mul_comm (b _) 2, mul_comm (b _) 2]

/-- Antisymmetrizing a character of anticyclotomic infinity type `b` gives infinity type
`2 * b`. -/
theorem antisymmetrize_hasPrescribedInfinityComponent {ψ : HeckeCharacter K}
    {b : InfinityType K} (hb : b.IsAnticyclotomic)
    (hψ : ψ.HasPrescribedInfinityComponent (InfinityType.toCharacter b)) :
    (antisymmetrize ψ).HasPrescribedInfinityComponent
      (InfinityType.toCharacter (fun σ ↦ 2 * b σ)) := by
  have hψy : ∀ y, ψ (ideleClassMap K (infiniteIdelesInclusion K y)) =
      InfinityType.toCharacter b y := fun y ↦ DFunLike.congr_fun hψ y
  ext y
  change (antisymmetrize ψ (ideleClassMap K (infiniteIdelesInclusion K y)) : ℂ) = _
  rw [antisymmetrize_apply, hψy, toCharacter_two_mul]
  change ((InfinityType.toCharacter b y *
    (ψ (ideleClassMap K (ideleEquiv (IsCMField.complexConj K).toRingEquiv
      (infiniteIdelesInclusion K y))))⁻¹ : ℂˣ) : ℂ) = _
  rw [ideleEquiv_complexConj_infiniteIdelesInclusion, hψy, toCharacter_complexConj hb, inv_inv,
    sq]

theorem isUnramifiedAt_complexConj {ψ : HeckeCharacter K} (hψ : ∀ w, ψ.IsUnramifiedAt w)
    (w : FinitePlace K) : ψ.complexConj.IsUnramifiedAt w := by
  have h := (HeckeCharacter.isUnramifiedAt_comap_iff (IsCMField.complexConj K).toRingEquiv ψ
    ((finitePlaceEquiv (IsCMField.complexConj K).toRingEquiv).symm w)).mpr (hψ _)
  rwa [Equiv.apply_symm_apply] at h

/-- The antisymmetrization of an everywhere unramified character is everywhere unramified. -/
theorem antisymmetrize_isUnramifiedAt {ψ : HeckeCharacter K} (hψ : ∀ w, ψ.IsUnramifiedAt w)
    (w : FinitePlace K) : (antisymmetrize ψ).IsUnramifiedAt w := by
  intro a ha
  change ψ.finiteComponent w a * (ψ.complexConj.finiteComponent w a)⁻¹ = 1
  rw [hψ w a ha, isUnramifiedAt_complexConj hψ w a ha, inv_one, mul_one]

/-- The conclusion of `CMUnramifiedInfinityRealizationStatement` from a character of infinity
type `n * a` that is trivial on the integral ideles with trivial archimedean part. -/
theorem realization_of_base {a : InfinityType K} (ha : a.IsAnticyclotomic) {n : ℕ} (hn : 0 < n)
    {ψ : HeckeCharacter K}
    (hψinf : ψ.HasPrescribedInfinityComponent
      (InfinityType.toCharacter (fun σ ↦ (n : ℤ) * a σ)))
    (hψ : ∀ x : Ideles K, x ∈ integralIdeles K → (x : Adeles K).1 = 1 →
      ψ (ideleClassMap K x) = 1) :
    ∃ (m : ℕ) (χ : HeckeCharacter K), 0 < m ∧
      (∀ x, χ (AdelicFunctoriality.ideleClassComplexConj x) = (χ x)⁻¹) ∧
      χ.HasPrescribedInfinityComponent
        (InfinityType.toCharacter (fun σ ↦ (m : ℤ) * a σ)) ∧
      ∀ w : FinitePlace K, χ.IsUnramifiedAt w := by
  have hb : InfinityType.IsAnticyclotomic (fun σ ↦ (n : ℤ) * a σ) := fun σ ↦ by
    simp only [ha σ, mul_neg]
  refine ⟨2 * n, antisymmetrize ψ, by omega, antisymmetrize_complexConj ψ, ?_,
    antisymmetrize_isUnramifiedAt (isUnramifiedAt_of_integral hψ)⟩
  have h := antisymmetrize_hasPrescribedInfinityComponent hb hψinf
  have he : (fun σ ↦ ((2 * n : ℕ) : ℤ) * a σ) = fun σ ↦ 2 * ((n : ℤ) * a σ) := by
    funext σ
    push_cast
    ring
  rwa [he]

end CMUnramifiedInfinity

end Langlands.Global
