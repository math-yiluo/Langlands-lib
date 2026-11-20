import Mathlib.RepresentationTheory.Homological.GroupCohomology.Hilbert90
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.RingTheory.RootsOfUnity.Basic

/-! # Kummer cochains on a finite Galois coefficient field -/

noncomputable section

universe u

open groupCohomology

namespace Langlands.GroupScheme.KummerCocycle

variable {F E : Type u} [Field F] [Field E] [Algebra F E]

/-- The unit-valued crossed coboundary of an actual radical. -/
def value (z : Eˣ) (σ : Gal(E/F)) : Eˣ := σ • z / z

/-- Its values satisfy the crossed cocycle law. -/
theorem value_isMulCocycle (z : Eˣ) : IsMulCocycle₁ (value (F := F) z) := by
  intro σ τ
  simp only [value, mul_smul, smul_div']
  exact (div_mul_div_cancel _ _ _).symm

/-- A radical with base-field power gives roots-of-unity values. -/
theorem value_pow (n : ℕ) (a : Fˣ) {z : Eˣ} (hz : z ^ n = Units.map (algebraMap F E) a)
    (σ : Gal(E/F)) : value z σ ^ n = 1 := by
  rw [value, div_pow, ← smul_pow', hz]
  apply div_eq_one.mpr
  apply Units.ext
  exact σ.commutes (a : F)

/-- Read the crossed coboundary of the radical in the actual roots-of-unity subgroup. -/
def rootValue (n : ℕ) (a : Fˣ) {z : Eˣ} (hz : z ^ n = Units.map (algebraMap F E) a)
    (σ : Gal(E/F)) : rootsOfUnity n E :=
  ⟨value z σ, (mem_rootsOfUnity n _).mpr (value_pow n a hz σ)⟩

/-- Every finite relative roots-of-unity cocycle is the Kummer cocycle of a base-field unit
with a radical in the coefficient field. -/
theorem exists_radical [FiniteDimensional F E] [IsGalois F E]
    (n : ℕ) (c : Gal(E/F) → Eˣ) (hc : IsMulCocycle₁ c) (hp : ∀ σ, c σ ^ n = 1) :
    ∃ (a : Fˣ) (z : Eˣ), z ^ n = Units.map (algebraMap F E) a ∧ ∀ σ, value z σ = c σ := by
  obtain ⟨z, hz⟩ := isMulCoboundary₁_of_isMulCocycle₁_of_aut_to_units c hc
  have hfix (σ : Gal(E/F)) : σ • z ^ n = z ^ n := by
    apply div_eq_one.mp
    rw [smul_pow', ← div_pow, hz, hp]
  obtain ⟨a, ha⟩ := (IsGalois.mem_range_algebraMap_iff_fixed (F := F) ((z ^ n : Eˣ) : E)).mpr
    (fun σ => congrArg Units.val (hfix σ))
  have ha₀ : a ≠ 0 := by
    intro h
    apply (z ^ n).ne_zero
    rw [← ha, h, map_zero]
  exact ⟨Units.mk0 a ha₀, z, (Units.ext ha).symm, hz⟩

/-- If the two base scalars differ by an `n`-th power, their Kummer cochains differ by the
coboundary of an actual root of unity over the common coefficient field. -/
theorem exists_root_compare (n : ℕ) (a b q : Fˣ)
    {x y : Eˣ} (hx : x ^ n = Units.map (algebraMap F E) a)
    (hy : y ^ n = Units.map (algebraMap F E) b) (h : a = b * q ^ n) :
    ∃ t : rootsOfUnity n E, ∀ σ : Gal(E/F), value x σ / value y σ = value (t : Eˣ) σ := by
  let i : Fˣ →* Eˣ := Units.map (algebraMap F E)
  have hi (σ : Gal(E/F)) : σ • i q = i q := Units.ext (σ.commutes (q : F))
  have ht : (x / (y * i q)) ^ n = 1 := by
    change x ^ n = i a at hx
    change y ^ n = i b at hy
    rw [div_pow, mul_pow, hx, hy, h, map_mul, map_pow, div_self']
  refine ⟨⟨x / (y * i q), (mem_rootsOfUnity n _).mpr ht⟩, fun σ => ?_⟩
  simp only [value, smul_div', smul_mul', hi]
  rw [div_div_div_comm (σ • x) (σ • y * i q) x (y * i q), mul_div_mul_right_eq_div]

end Langlands.GroupScheme.KummerCocycle
