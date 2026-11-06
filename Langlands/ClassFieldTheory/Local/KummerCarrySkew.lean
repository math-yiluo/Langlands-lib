import Langlands.ClassFieldTheory.Local.CyclicClassAlgebra

/-! # Explicit skew symmetry of Kummer carry classes -/

noncomputable section

namespace Langlands.ClassFieldTheory.Local

universe u v

namespace KummerCarry

/-- The explicit degree-one cochain whose coboundary is the sum of the two
positive carry cocycles under the root-action hypotheses below. -/
def skewCochain
    {K : Type v} {L : Type u} [Field K] [Field L] [Algebra K L]
    {n : ℕ} (χ ψ : Gal(L/K) →* Multiplicative (ZMod n))
    (α β ζ : unitsRepresentation K L) (g : Gal(L/K)) : unitsRepresentation K L :=
  ((χ g).toAdd.val : ℤ) • β + ((ψ g).toAdd.val : ℤ) • α +
    (((χ g).toAdd.val : ℤ) * ((ψ g).toAdd.val : ℤ)) • ζ

private theorem zsmul_eq_zero_of_cast_eq_zero {A : Type*} [AddCommGroup A]
    {n : ℕ} [NeZero n] (ζ : A) (hζ : (n : ℤ) • ζ = 0) (r : ℤ)
    (hr : (r : ZMod n) = 0) : r • ζ = 0 := by
  obtain ⟨k, rfl⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd r n).mp hr
  rw [mul_smul, smul_comm, hζ, smul_zero]

private theorem carry_int {n : ℕ} [NeZero n] (x y : ZMod n) :
    (x.val : ℤ) + (y.val : ℤ) - ((x + y).val : ℤ) =
      (n : ℤ) * (cyclicCarry x y : ℤ) := by
  have h := congrArg (fun r : ℕ => (r : ℤ)) (cyclicCarry_spec x y)
  push_cast at h
  omega

/-- Explicit coboundary proving skew symmetry when the two characters describe
Galois actions on roots of the two base units. -/
theorem cyclicClass_add_eq_zero
    {K : Type v} {L : Type u} [Field K] [Field L] [Algebra K L]
    {n : ℕ} [NeZero n]
    (χ ψ : Gal(L/K) →* Multiplicative (ZMod n))
    (a b : Kˣ) (α β ζ : unitsRepresentation K L)
    (hα : (n : ℤ) • α = baseUnit K L a)
    (hβ : (n : ℤ) • β = baseUnit K L b)
    (hζ : (n : ℤ) • ζ = 0)
    (hfix : ∀ g, (unitsRepresentation K L).ρ g ζ = ζ)
    (haction : ∀ g, (unitsRepresentation K L).ρ g α =
      ((χ g).toAdd.val : ℤ) • ζ + α)
    (hbction : ∀ g, (unitsRepresentation K L).ρ g β =
      ((ψ g).toAdd.val : ℤ) • ζ + β) :
    cyclicClass K L χ b + cyclicClass K L ψ a = 0 := by
  rw [cyclicClass, cyclicClass, ← map_add, groupCohomology.H2π_eq_zero_iff]
  refine ⟨skewCochain χ ψ α β ζ, ?_⟩
  funext gh
  obtain ⟨g, h⟩ := gh
  rw [groupCohomology.d₁₂_hom_apply]
  dsimp only [skewCochain]
  simp only [map_add, map_zsmul, hfix, haction, hbction]
  let x : ℤ := (χ g).toAdd.val
  let y : ℤ := (χ h).toAdd.val
  let z : ℤ := (χ (g * h)).toAdd.val
  let r : ℤ := (ψ g).toAdd.val
  let s : ℤ := (ψ h).toAdd.val
  let t : ℤ := (ψ (g * h)).toAdd.val
  have hx : x + y - z = (n : ℤ) * (cyclicCarry (χ g).toAdd (χ h).toAdd : ℤ) := by
    simpa only [x, y, z, map_mul, toAdd_mul] using carry_int (χ g).toAdd (χ h).toAdd
  have hr : r + s - t = (n : ℤ) * (cyclicCarry (ψ g).toAdd (ψ h).toAdd : ℤ) := by
    simpa only [r, s, t, map_mul, toAdd_mul] using carry_int (ψ g).toAdd (ψ h).toAdd
  have hxy : (x + y : ZMod n) = z := by
    simp only [x, y, z, Int.cast_natCast, ZMod.natCast_zmod_val,
      map_mul, toAdd_mul]
  have hrs : (r + s : ZMod n) = t := by
    simp only [r, s, t, Int.cast_natCast, ZMod.natCast_zmod_val,
      map_mul, toAdd_mul]
  have hz : (y * r + s * x + y * s - z * t + x * r) • ζ = 0 := by
    apply zsmul_eq_zero_of_cast_eq_zero ζ hζ
    push_cast
    rw [← hxy, ← hrs]
    ring
  change y • (r • ζ + β) + s • (x • ζ + α) + (y * s) • ζ -
      (z • β + t • α + (z * t) • ζ) +
      (x • β + r • α + (x * r) • ζ) =
    cyclicCarry (χ g).toAdd (χ h).toAdd • baseUnit K L b +
      cyclicCarry (ψ g).toAdd (ψ h).toAdd • baseUnit K L a
  calc
    _ = (x + y - z) • β + (r + s - t) • α +
        (y * r + s * x + y * s - z * t + x * r) • ζ := by module
    _ = _ := by rw [hx, hr, hz, add_zero, mul_smul, mul_smul,
      smul_comm (n : ℤ) _ β, smul_comm (n : ℤ) _ α, hβ, hα,
      natCast_zsmul, natCast_zsmul]

end KummerCarry

end Langlands.ClassFieldTheory.Local
