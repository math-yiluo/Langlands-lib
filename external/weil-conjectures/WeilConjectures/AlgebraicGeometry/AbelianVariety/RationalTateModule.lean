/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.AbelianVariety.GeometricPoints
public import WeilConjectures.NumberTheory.TateModule

/-!
# The Tate module of an abelian variety over an arbitrary field

Let `A` be an abelian variety of dimension `g` over a field `K` and `ℓ` a prime invertible in
`K`. The Tate module `T_ℓ A` of the group `A(K̄)` of geometric points is free of rank `2 g`
over `ℤ_ℓ`, so that `V_ℓ A` is a `2 g`-dimensional `ℚ_ℓ`-vector space. Over a finite field the
arithmetic Frobenius `σ` fixes no nonzero vector of `T_ℓ A`, and `σ - 1` is an automorphism of
`V_ℓ A`.

## Main statements

- `AlgebraicGeometry.IsAbelianVariety.nonempty_linearEquiv_tateModule_of_natCast_ne_zero`:
  `T_ℓ A ≅ ℤ_ℓ ^ (2 g)`.
- `AlgebraicGeometry.IsAbelianVariety.nonempty_linearEquiv_rationalTateModule_of_natCast_ne_zero`:
  `V_ℓ A ≅ ℚ_ℓ ^ (2 g)`.
- `AlgebraicGeometry.IsAbelianVariety.eq_zero_of_galoisRepresentation_frobenius_eq_self`:
  `(T_ℓ A)^{σ = 1} = 0`.
- `AlgebraicGeometry.IsAbelianVariety.bijective_rationalTateModuleGaloisMap_frobenius_sub_id`:
  `σ - 1` is bijective on `V_ℓ A`.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj

namespace AlgebraicGeometry.IsAbelianVariety

variable {K : Type u} [Field K] (ℓ : ℕ) [Fact ℓ.Prime] (A : Over (Spec (.of K))) [GrpObj A]
  [IsAbelianVariety A]

/-- For a prime `ℓ` invertible in `K`, the `ℓ`-torsion of the geometric points `A(K̄)` of an
abelian variety of dimension `g` over `K` has `ℓ ^ (2 g)` elements. -/
theorem natCard_torsionBy_geometricPoints (hℓ : (ℓ : K) ≠ 0) :
    Nat.card (AddSubgroup.torsionBy (Additive (Scheme.specAlgebraicClosure K ⟶ A)) (ℓ : ℤ)) =
      ℓ ^ (2 * IsAbelianVariety.dim A) := by
  have hp : ¬ ringChar K ∣ ℓ := fun h ↦ hℓ ((ringChar.spec K ℓ).2 h)
  obtain ⟨f⟩ := nonempty_addEquiv_torsionBy_points (K' := AlgebraicClosure K) A (ringChar K) ℓ
    (Fact.out : ℓ.Prime).pos hp
  refine (Nat.card_congr f.toEquiv).trans ?_
  rw [Nat.card_fun, Nat.card_zmod, Nat.card_eq_fintype_card, Fintype.card_fin]

/-- Blueprint `proposition-integral-tate-module--2` over an arbitrary field: for a prime `ℓ`
invertible in `K`, the Tate module of an abelian variety of dimension `g` over `K` is
`T_ℓ A ≅ ℤ_ℓ ^ (2 g)`. -/
theorem nonempty_linearEquiv_tateModule_of_natCast_ne_zero (hℓ : (ℓ : K) ≠ 0) :
    Nonempty (tateModule ℓ A ≃ₗ[ℤ_[ℓ]] (Fin (2 * IsAbelianVariety.dim A) → ℤ_[ℓ])) :=
  AddCommGroup.tateModule.nonempty_linearEquiv_of_natCard_eq ℓ _
    (exists_zsmul_eq_geometricPoints A ℓ (Fact.out : ℓ.Prime).pos) _
    (natCard_torsionBy_geometricPoints ℓ A hℓ)

/-- Blueprint `proposition-integral-tate-module--2` over an arbitrary field: for a prime `ℓ`
invertible in `K`, the rational Tate module of an abelian variety of dimension `g` over `K` is
`V_ℓ A ≅ ℚ_ℓ ^ (2 g)`. -/
theorem nonempty_linearEquiv_rationalTateModule_of_natCast_ne_zero (hℓ : (ℓ : K) ≠ 0) :
    Nonempty (rationalTateModule ℓ A ≃ₗ[ℚ_[ℓ]] (Fin (2 * IsAbelianVariety.dim A) → ℚ_[ℓ])) :=
  AddCommGroup.rationalTateModule.nonempty_linearEquiv_of_natCard_eq ℓ _
    (exists_zsmul_eq_geometricPoints A ℓ (Fact.out : ℓ.Prime).pos) _
    (natCard_torsionBy_geometricPoints ℓ A hℓ)

/-- For a prime `ℓ` invertible in `K`, the rational Tate module `V_ℓ A` of an abelian variety
over `K` is finite dimensional. -/
theorem finiteDimensional_rationalTateModule (hℓ : (ℓ : K) ≠ 0) :
    FiniteDimensional ℚ_[ℓ] (rationalTateModule ℓ A) :=
  let ⟨e⟩ := nonempty_linearEquiv_rationalTateModule_of_natCast_ne_zero ℓ A hℓ
  e.symm.finiteDimensional

/-- The action `V_ℓ A ⟶ V_ℓ A` of `σ ∈ Gal(K̄ / K)` on the rational Tate module, induced by its
action on geometric points by coordinates. -/
noncomputable def rationalTateModuleGaloisMap (σ : Gal(AlgebraicClosure K/K)) :
    rationalTateModule ℓ A →ₗ[ℚ_[ℓ]] rationalTateModule ℓ A :=
  AddCommGroup.rationalTateModule.map (geometricPointsAddEquiv (A := A) σ).toAddMonoidHom

section FiniteField

variable [Fintype K]

/-- Blueprint `proposition-no-frobenius-fixed-vector` (integral form): the arithmetic Frobenius
`σ : z ↦ z ^ q` of `Gal(K̄ / K)`, acting on `T_ℓ A` through the Galois representation, fixes no
nonzero vector: `(T_ℓ A)^{σ = 1} = 0`. -/
theorem eq_zero_of_galoisRepresentation_frobenius_eq_self {t : tateModule ℓ A}
    (ht : galoisRepresentation ℓ A
      (FiniteField.frobeniusAlgEquivOfAlgebraic K (AlgebraicClosure K)) t = t) :
    t = 0 :=
  Subtype.ext <| AddCommGroup.eq_zero_of_mem_tateModule_of_forall_fixed _
    (finite_setOf_frobenius_fixed A) t.2 fun n ↦ congrFun (congrArg Subtype.val ht) n

/-- Blueprint `proposition-no-frobenius-fixed-vector` (rational form): for a prime `ℓ` invertible in
`K`, the endomorphism `σ - 1` of `V_ℓ A` is bijective, where `σ` is the arithmetic Frobenius
acting on geometric points by coordinates. It is injective since `σ` has no nonzero fixed vector
(`AddCommGroup.rationalTateModule.eq_zero_of_map_eq_self`), hence bijective as `V_ℓ A` is finite
dimensional. -/
theorem bijective_rationalTateModuleGaloisMap_frobenius_sub_id (hℓ : (ℓ : K) ≠ 0) :
    Function.Bijective (rationalTateModuleGaloisMap ℓ A
      (FiniteField.frobeniusAlgEquivOfAlgebraic K (AlgebraicClosure K)) -
        LinearMap.id (R := ℚ_[ℓ]) (M := rationalTateModule ℓ A)) := by
  have := finiteDimensional_rationalTateModule ℓ A hℓ
  have hinj : Function.Injective (rationalTateModuleGaloisMap ℓ A
      (FiniteField.frobeniusAlgEquivOfAlgebraic K (AlgebraicClosure K)) -
        LinearMap.id (R := ℚ_[ℓ]) (M := rationalTateModule ℓ A)) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro v hv
    rw [LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero] at hv
    exact AddCommGroup.rationalTateModule.eq_zero_of_map_eq_self _
      (finite_setOf_frobenius_fixed A) hv
  exact ⟨hinj, LinearMap.injective_iff_surjective.1 hinj⟩

/-- Blueprint `proposition-no-frobenius-fixed-vector` (rational form): for a prime `ℓ` invertible in
`K`, `σ - 1` is an automorphism of the rational Tate module `V_ℓ A`, `σ` the arithmetic
Frobenius. -/
noncomputable def frobeniusSubOneLinearEquiv (hℓ : (ℓ : K) ≠ 0) :
    rationalTateModule ℓ A ≃ₗ[ℚ_[ℓ]] rationalTateModule ℓ A :=
  LinearEquiv.ofBijective _ (bijective_rationalTateModuleGaloisMap_frobenius_sub_id ℓ A hℓ)

theorem frobeniusSubOneLinearEquiv_apply (hℓ : (ℓ : K) ≠ 0) (v : rationalTateModule ℓ A) :
    frobeniusSubOneLinearEquiv ℓ A hℓ v = rationalTateModuleGaloisMap ℓ A
      (FiniteField.frobeniusAlgEquivOfAlgebraic K (AlgebraicClosure K)) v - v :=
  rfl

end FiniteField

end AlgebraicGeometry.IsAbelianVariety
