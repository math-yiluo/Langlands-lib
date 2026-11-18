import Langlands.Geometry.FormalGroup.PiDivisible

/-! # Uniform scalar torsion on represented kernels -/

noncomputable section
universe u v
namespace Langlands.FormalGroup.ModuleLaw
open CategoryTheory
attribute [local instance] coefficientAlgebra coefficientScalarTower

variable {O : Type u} [CommRing O]
variable {R : Type v} [CommRing R] [Algebra O R]
variable {σ τ υ : Type} [Finite σ] [Finite τ] [Finite υ]
variable {M : ModuleLaw O R σ} {N : ModuleLaw O R τ}
variable {P : ModuleLaw O R υ} {π : O}

namespace Hom

/-- Torsion of the universal represented kernel point supplies one scalar
power killing every kernel point over every test algebra. -/
theorem exists_pow_kills_kernel_of_corepresentable (hM : M.IsPiPowerTorsion π)
    (f : Hom M N) (A₀ : CommAlgCat.{v} R)
    (e : f.kernelSetFunctor.CorepresentableBy A₀) :
    ∃ n : ℕ, ∀ (A : CommAlgCat.{v} R) (x : f.kernelPoints A),
      (π ^ n) • x.val = 0 := by
  let x₀ : f.kernelPoints A₀ := e.homEquiv (𝟙 A₀)
  obtain ⟨n, hn⟩ := hM A₀ x₀.val
  refine ⟨n, ?_⟩
  intro A x
  let φ : A₀ ⟶ A := e.homEquiv.symm x
  have hx : f.kernelMap φ x₀ = x := by
    have he := e.homEquiv_eq φ
    change e.homEquiv φ = f.kernelMap φ x₀ at he
    exact he.symm.trans (e.homEquiv.apply_symm_apply x)
  have h := congrArg (M.algebraMapPoints φ.hom) hn
  rw [map_smul, map_zero] at h
  have hxval : M.algebraMapPoints φ.hom x₀.val = x.val :=
    congrArg Subtype.val hx
  rw [hxval] at h
  exact h

/-- An actual finite locally free kernel of a scalar-power torsion formal
module is killed by one common power and all larger powers. -/
theorem HasFiniteLocallyFreeKernel.exists_eventually_pow_kills
    {f : Hom M N} (hf : f.HasFiniteLocallyFreeKernel)
    (hM : M.IsPiPowerTorsion π) :
    ∃ n : ℕ, ∀ j, n ≤ j →
      ∀ (A : CommAlgCat.{v} R) (x : f.kernelPoints A), (π ^ j) • x.val = 0 := by
  obtain ⟨K⟩ := hf
  obtain ⟨n, hn⟩ := exists_pow_kills_kernel_of_corepresentable hM f
    K.coordinateAlgebra K.represents
  refine ⟨n, ?_⟩
  intro j hj A x
  rw [← Nat.sub_add_cancel hj, pow_add, mul_smul, hn A x, smul_zero]

/-- The source's scalar divisibility supplies a common annihilating
scalar-power threshold for the actual kernel of any isogeny. -/
theorem IsIsogeny.exists_eventually_pow_kills_kernel
    {f : Hom M N} (hf : f.IsIsogeny) (hM : M.IsPiDivisible π) :
    ∃ n : ℕ, ∀ j, n ≤ j →
      ∀ (A : CommAlgCat.{v} R) (x : f.kernelPoints A), (π ^ j) • x.val = 0 :=
  hf.2.exists_eventually_pow_kills hM.torsion

/-- A lift through a composite gives a lift through its left factor. -/
theorem IsFppfLocallySurjective.right_of_comp {f : Hom M N} {g : Hom N P}
    (h : (g.comp f).IsFppfLocallySurjective) : g.IsFppfLocallySurjective := by
  intro A y
  obtain ⟨B, φ, hff, hfp, x, hx⟩ := h A y
  exact ⟨B, φ, hff, hfp, f.onAlgebraPoints x,
    (onAlgebraPoints_comp g f x).symm.trans hx⟩

/-- An integral scalar-power dual has actual fppf local lifting, by
lifting target points through the source scalar endomorphism. -/
theorem isFppfLocallySurjective_of_comp_eq_scalarHom
    (hM : M.IsPiDivisible π) (f : Hom M N) (g : Hom N M) (j : ℕ)
    (h : g.comp f = M.scalarHom (π ^ j)) : g.IsFppfLocallySurjective := by
  apply IsFppfLocallySurjective.right_of_comp (f := f)
  rw [h]
  exact hM.scalarPower_locallySurjective j

end Hom
end Langlands.FormalGroup.ModuleLaw
