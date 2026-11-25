/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.LinearAlgebra.Basis.TowerLift
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.LocalRing.Quotient

/-!
# Surjections of free modules over truncations of a local ring

- `Module.Basis.exists_linearEquiv_comp_eq`: two surjective `Λ`-linear maps `P → Q` between free
  modules of the same finite rank over quotients `R → S` of `Λ` (`R → S` local and surjective)
  differ by a `Λ`-linear automorphism of `P`;
- `Ideal.exists_linearEquiv_comp_eq_powQuotientReduction`: in particular every surjection
  `(Λ ⧸ Iⁿ⁺²)^r → (Λ ⧸ Iⁿ⁺¹)^r` is the reduction map `Ideal.powQuotientReduction` up to an
  automorphism, for a proper ideal `I` of a local ring `Λ` (e.g. `𝒪_E ⧸ ℓⁿ`).
-/

@[expose] public section

open Module

namespace Module.Basis

variable {ι Λ R S P Q : Type*} [Finite ι] [CommRing Λ] [CommRing R] [CommRing S]
  [Algebra Λ R] [Algebra Λ S] [AddCommGroup P] [Module R P] [Module Λ P] [IsScalarTower Λ R P]
  [AddCommGroup Q] [Module S Q] [Module Λ Q] [IsScalarTower Λ S Q]

/-- A `Λ`-linear map between modules over quotients `R`, `S` of `Λ` is semilinear over any ring
map `π : R → S` compatible with the structure maps. -/
def semilinearOfLinear (hR : Function.Surjective (algebraMap Λ R)) (π : R →+* S)
    (hπ : π.comp (algebraMap Λ R) = algebraMap Λ S) (f : P →ₗ[Λ] Q) : P →ₛₗ[π] Q where
  toFun := f
  map_add' := f.map_add
  map_smul' r x := by
    obtain ⟨c, rfl⟩ := hR r
    rw [algebraMap_smul, f.map_smul, ← RingHom.comp_apply, hπ, algebraMap_smul]

/-- **Surjections of free modules over a tower of local rings are standard up to automorphism.**
Let `R → S` be a surjective local homomorphism of quotients of `Λ`, and `P`, `Q` free modules
over `R`, `S` with bases indexed by the same finite type. Any two surjective `Λ`-linear maps
`f, std : P → Q` differ by a `Λ`-linear automorphism of `P`: `f ∘ g = std`. -/
theorem exists_linearEquiv_comp_eq (hR : Function.Surjective (algebraMap Λ R)) (π : R →+* S)
    [IsLocalHom π] (hπs : Function.Surjective π) (hπ : π.comp (algebraMap Λ R) = algebraMap Λ S)
    (b : Basis ι R P) (b' : Basis ι S Q) (std f : P →ₗ[Λ] Q) (hstd : Function.Surjective std)
    (hf : Function.Surjective f) : ∃ g : P ≃ₗ[Λ] P, f ∘ₗ g.toLinearMap = std := by
  have := Fintype.ofFinite ι
  let std' := semilinearOfLinear hR π hπ std
  let f' := semilinearOfLinear hR π hπ f
  have hspan : Submodule.span S (Set.range fun i ↦ std (b i)) = ⊤ := by
    have : RingHomSurjective π := ⟨hπs⟩
    have h := Submodule.map_span std' (Set.range b)
    rw [b.span_eq, Submodule.map_top,
      LinearMap.range_eq_top.2 (show Function.Surjective std' from hstd),
      ← Set.range_comp] at h
    exact h.symm
  let b'' := b'.ofSpanEqTop _ hspan
  obtain ⟨c, hc⟩ := Basis.exists_basis_map_eq hπs (t := f') hf b b''
  refine ⟨(b.equiv c (Equiv.refl ι)).restrictScalars Λ, ?_⟩
  have h : f' ∘ₛₗ (b.equiv c (Equiv.refl ι)).toLinearMap = std' :=
    b.ext fun i ↦ by
      have := hc i
      simp only [b'', ofSpanEqTop_apply] at this
      rw [LinearMap.comp_apply, LinearEquiv.coe_coe, Basis.equiv_apply, Equiv.refl_apply]
      exact this
  ext x
  exact congrArg (fun φ : P →ₛₗ[π] Q ↦ φ x) h

end Module.Basis

namespace Ideal

variable {Λ : Type*} [CommRing Λ] [IsLocalRing Λ] (I : Ideal Λ) (r : ℕ)

/-- The reduction map `(Λ ⧸ Iⁿ⁺²)^r → (Λ ⧸ Iⁿ⁺¹)^r`. -/
def powQuotientReduction (n : ℕ) :
    (Fin r → Λ ⧸ I ^ (n + 2)) →ₗ[Λ] (Fin r → Λ ⧸ I ^ (n + 1)) :=
  LinearMap.pi fun i ↦ (Ideal.Quotient.factorₐ Λ (Ideal.pow_le_pow_right (Nat.le_succ (n + 1)) :
    I ^ (n + 2) ≤ I ^ (n + 1))).toLinearMap ∘ₗ LinearMap.proj i

/-- **Surjections `(Λ ⧸ Iⁿ⁺²)^r → (Λ ⧸ Iⁿ⁺¹)^r` are standard up to automorphism**, for a
proper ideal `I` of a local ring `Λ` (e.g. `𝒪_E ⧸ ℓⁿ`): every surjective `Λ`-linear map is the
reduction map up to a `Λ`-linear automorphism of the source. -/
theorem exists_linearEquiv_comp_eq_powQuotientReduction (hI : I ≠ ⊤) (n : ℕ)
    (f : (Fin r → Λ ⧸ I ^ (n + 2)) →ₗ[Λ] (Fin r → Λ ⧸ I ^ (n + 1)))
    (hf : Function.Surjective f) :
    ∃ g : (Fin r → Λ ⧸ I ^ (n + 2)) ≃ₗ[Λ] (Fin r → Λ ⧸ I ^ (n + 2)),
      f ∘ₗ g.toLinearMap = powQuotientReduction I r n := by
  have hle : I ^ (n + 2) ≤ I ^ (n + 1) := Ideal.pow_le_pow_right (Nat.le_succ (n + 1))
  have hne (k : ℕ) : I ^ (k + 1) ≠ ⊤ := fun h ↦ hI (eq_top_iff.2 (h ▸ Ideal.pow_le_self
    k.succ_ne_zero))
  have : Nontrivial (Λ ⧸ I ^ (n + 1)) := Ideal.Quotient.nontrivial_iff.2 (hne n)
  have : Nontrivial (Λ ⧸ I ^ (n + 2)) := Ideal.Quotient.nontrivial_iff.2 (hne (n + 1))
  have : IsLocalRing (Λ ⧸ I ^ (n + 2)) :=
    IsLocalRing.of_surjective' _ Ideal.Quotient.mk_surjective
  have := IsLocalHom.of_surjective (Ideal.Quotient.factor hle)
    (Ideal.Quotient.factor_surjective hle)
  refine Module.Basis.exists_linearEquiv_comp_eq Ideal.Quotient.mk_surjective
    (Ideal.Quotient.factor hle) (Ideal.Quotient.factor_surjective hle)
    (Ideal.Quotient.factor_comp_mk hle) (Pi.basisFun _ _) (Pi.basisFun _ _) _ f ?_ hf
  intro y
  choose x hx using fun i ↦ Ideal.Quotient.factor_surjective hle (y i)
  exact ⟨x, funext fun i ↦ hx i⟩

end Ideal
