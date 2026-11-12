import Langlands.Galois.FrobeniusLift
import Langlands.Global.HeckeCharacter

/-!
# `λ`-adic characters realizing algebraic Hecke characters

A continuous character of the actual absolute Galois group with values in the
completion `L_λ`, and the relation saying that it realizes a complex Hecke
character through `ι : L → ℂ`: at almost all finite places `v` away from the
residue characteristic of `λ`, both are unramified and the value at a lift of
geometric Frobenius corresponds to the value at a uniformizer.
-/

noncomputable section

universe uK uL

namespace Langlands.GaloisRepresentation

open Langlands.Global
open scoped Valued

/-- A continuous `λ`-adic character of `Gal(K̄/K)`, with values in the units of
the actual completion `L_λ` of the coefficient field. -/
abbrev LambdaAdicCharacter (K : Type uK) [Field K] (L : Type uL) [Field L] [NumberField L]
    (lam : FinitePlace L) :=
  Field.absoluteGaloisGroup K →ₜ* (FiniteCompletion L lam)ˣ

namespace LambdaAdicCharacter

variable {K : Type uK} [Field K] [NumberField K]
variable {L : Type uL} [Field L] [NumberField L] {lam : FinitePlace L}

/-- Restriction to the absolute Galois group of the completion `K_v`, along the
same map of absolute Galois groups as `GaloisRepresentation.atFinitePlace`. -/
def atFinitePlace (ψ : LambdaAdicCharacter K L lam) (v : FinitePlace K) :
    LocalGroup v →ₜ* (FiniteCompletion L lam)ˣ :=
  ψ.comp (Field.absoluteGaloisGroup.map (NumberField.FinitePlace.embedding v))

/-- Unramified at `v`: trivial on the actual inertia subgroup at `v`. -/
def IsUnramifiedAt (ψ : LambdaAdicCharacter K L lam) (v : FinitePlace K) : Prop :=
  ∀ i : localInertia v, ψ.atFinitePlace v i.val = 1

/-- At an unramified place, all lifts of geometric Frobenius have the same value. -/
theorem atFinitePlace_eq_of_geometricFrobenius {ψ : LambdaAdicCharacter K L lam}
    {v : FinitePlace K} (hψ : ψ.IsUnramifiedAt v) {g h : LocalGroup v}
    (hg : IsGeometricFrobeniusLift v g) (hh : IsGeometricFrobeniusLift v h) :
    ψ.atFinitePlace v g = ψ.atFinitePlace v h := by
  have hres := residueAction_eq_of_geometricFrobenius hg hh
  have hker : g * h⁻¹ ∈ localInertia v := by
    change localResidueAction v (g * h⁻¹) = 1
    rw [map_mul, map_inv, hres, mul_inv_cancel]
  have hprod := hψ ⟨g * h⁻¹, hker⟩
  rw [map_mul, map_inv] at hprod
  exact mul_inv_eq_one.mp hprod

end LambdaAdicCharacter

variable {K : Type uK} [Field K] [NumberField K]
variable {L : Type uL} [Field L] [NumberField L]

/-- `ψ` is a `λ`-adic realization of the Hecke character `χ` through
`ι : L → ℂ`: outside a finite set `S` of finite places of `K`, at every `v`
whose residue characteristic differs from that of `λ`, both `χ` and `ψ` are
unramified at `v`, and there is `c ∈ L` with `ι(c) = χ_v(ϖ_v)` for an actual
uniformizer `ϖ_v` of `K_v` and `ψ(Frob_v) = c` in `L_λ` for an actual lift
`Frob_v` of geometric Frobenius. Geometric Frobenius corresponds to the
uniformizer. -/
def IsLambdaAdicRealization (ι : L →+* ℂ) (lam : FinitePlace L)
    (χ : HeckeCharacter K) (ψ : LambdaAdicCharacter K L lam) : Prop :=
  ∃ S : Finset (FinitePlace K), ∀ v : FinitePlace K, v ∉ S →
    residueCharacteristic v ≠ residueCharacteristic lam →
      χ.IsUnramifiedAt v ∧ ψ.IsUnramifiedAt v ∧
        ∃ c : L,
          (∃ ϖ : (FiniteCompletion K v)ˣ,
            Valued.v (ϖ : FiniteCompletion K v) = WithZero.exp (-1 : ℤ) ∧
              (χ.finiteComponent v ϖ : ℂ) = ι c) ∧
          ∃ g : LocalGroup v, IsGeometricFrobeniusLift v g ∧
            (ψ.atFinitePlace v g : FiniteCompletion L lam) =
              NumberField.FinitePlace.embedding lam c

/-- In a realization, every lift of geometric Frobenius at a good place has the
value prescribed by the Hecke character. -/
theorem IsLambdaAdicRealization.forall_lifts {ι : L →+* ℂ} {lam : FinitePlace L}
    {χ : HeckeCharacter K} {ψ : LambdaAdicCharacter K L lam}
    (h : IsLambdaAdicRealization ι lam χ ψ) :
    ∃ S : Finset (FinitePlace K), ∀ v : FinitePlace K, v ∉ S →
      residueCharacteristic v ≠ residueCharacteristic lam →
        ∃ c : L,
          (∃ ϖ : (FiniteCompletion K v)ˣ,
            Valued.v (ϖ : FiniteCompletion K v) = WithZero.exp (-1 : ℤ) ∧
              (χ.finiteComponent v ϖ : ℂ) = ι c) ∧
          ∀ g : LocalGroup v, IsGeometricFrobeniusLift v g →
            (ψ.atFinitePlace v g : FiniteCompletion L lam) =
              NumberField.FinitePlace.embedding lam c := by
  obtain ⟨S, hS⟩ := h
  refine ⟨S, fun v hv hp => ?_⟩
  obtain ⟨-, hψ, c, hχ, g₀, hg₀, hψg₀⟩ := hS v hv hp
  refine ⟨c, hχ, fun g hg => ?_⟩
  rw [LambdaAdicCharacter.atFinitePlace_eq_of_geometricFrobenius hψ hg hg₀, hψg₀]

/-- Nonvacuity: the trivial `λ`-adic character realizes the trivial Hecke
character, with the exceptional set empty. -/
theorem isLambdaAdicRealization_one (ι : L →+* ℂ) (lam : FinitePlace L) :
    IsLambdaAdicRealization ι lam (1 : HeckeCharacter K)
      (1 : LambdaAdicCharacter K L lam) := by
  refine ⟨∅, fun v _ _ => ⟨fun _ _ => rfl, fun _ => rfl, 1, ?_, ?_⟩⟩
  · obtain ⟨b, hb⟩ :=
      IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_surjective K v
        (WithZero.exp (-1 : ℤ))
    have hb0 : b ≠ 0 := by
      intro h0
      exact (WithZero.exp_ne_zero (a := (-1 : ℤ)))
        (by simpa only [h0, map_zero] using hb.symm)
    refine ⟨Units.mk0 b hb0, hb, ?_⟩
    change ((1 : ℂˣ) : ℂ) = ι 1
    simp
  · obtain ⟨g, hg⟩ := exists_geometricFrobeniusLift v
    refine ⟨g, hg, ?_⟩
    change ((1 : (FiniteCompletion L lam)ˣ) : FiniteCompletion L lam) = _
    simp

end Langlands.GaloisRepresentation
