/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.CharP.Defs
public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.LocalFlatDescent
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import WeilConjectures.Mathlib.Algebra.Module.Torsion.Basic
public import WeilConjectures.AlgebraicGeometry.AbelianVariety.Basic
public import WeilConjectures.AlgebraicGeometry.AbelianVariety.Isogeny
public import WeilConjectures.AlgebraicGeometry.GroupScheme.Defs
public import WeilConjectures.AlgebraicGeometry.GroupScheme.Finite

/-!
# The `n`-torsion of an abelian variety

For `n` prime to the characteristic, the `n`-torsion subgroup scheme of an abelian variety is
étale; over an algebraically closed field its points do not change under extension of
algebraically closed fields, and for an abelian variety of dimension `g` the group of
`n`-torsion points is `(ℤ/nℤ) ^ (2 * g)`.

The group `A(K)` of `K`-points of `A` is `𝟙_ (Over (Spec (.of K))) ⟶ A` with the group structure
of `CategoryTheory.GrpObj.Hom.group`; it is written additively as
`Additive (𝟙_ (Over (Spec (.of K))) ⟶ A)`, so that `AddSubgroup.torsionBy` describes its
`n`-torsion.

"Prime to the characteristic" is spelled `¬ p ∣ n`, which for `p = 0` says exactly `n ≠ 0`.

The proofs follow the blueprint: `A[n]` is finite of order `n ^ (2 * g)`
(`AlgebraicGeometry.finrankΓ_torsionSubgroupScheme`), hence étale
(`AlgebraicGeometry.etale_of_not_dvd_finrankΓ`), so its points over an algebraically closed
field are counted by `AlgebraicGeometry.card_points_eq_finrankΓ`; together with divisibility of
`A(K)` this determines the group `A(K)[n]`
(`AddSubgroup.nonempty_addEquiv_torsionBy_of_forall_prime`).

## Main statements

- `AlgebraicGeometry.etale_torsionSubgroupScheme`: the `n`-torsion of an abelian variety is
  étale for `n` prime to the characteristic.
- `AlgebraicGeometry.etale_npow_id`: equivalently, multiplication by `n` is étale.
- `AlgebraicGeometry.bijective_toUnit_comp_torsionSubgroupScheme`: its points do not change
  under an extension of algebraically closed fields.
- `AlgebraicGeometry.nonempty_addEquiv_torsionBy`: `A(K)[n] ≃+ (ℤ/nℤ) ^ (2 * g)`.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj

namespace AlgebraicGeometry

variable {K : Type u} [Field K]

/-- Blueprint `proposition-multiplication-n--2`: The `n`-torsion of an abelian variety is étale.

Let `A` be an abelian variety over a field `K` of characteristic `p` and let `n` be prime to
`p`. Then `A[n]` is an étale group scheme over `K`. This is also the first part of blueprint
`proposition-multiplication-n--2`.

`A[n]` is a finite group scheme of order `n ^ (2 * g)`
(`AlgebraicGeometry.finrankΓ_torsionSubgroupScheme`), which is prime to `p`, so it is étale by
`AlgebraicGeometry.etale_of_not_dvd_finrankΓ`. -/
theorem etale_torsionSubgroupScheme (p : ℕ) [CharP K p] (A : Over (Spec (.of K))) [GrpObj A]
    [IsAbelianVariety A] (n : ℕ) (hn : 0 < n) (hnp : ¬ p ∣ n) :
    Etale (torsionSubgroupScheme A n).hom := by
  have := isFinite_torsionSubgroupScheme A n hn
  refine etale_of_not_dvd_finrankΓ p _ ?_
  rw [finrankΓ_torsionSubgroupScheme n hn]
  intro h
  rcases CharP.char_is_prime_or_zero K p with hp | rfl
  · exact hnp (hp.dvd_of_dvd_pow h)
  · exact pow_ne_zero _ hn.ne' (zero_dvd_iff.1 h)

/-- Blueprint `proposition-multiplication-n--2`: Multiplication by `d` prime to the characteristic
is étale.

Let `A` be an abelian variety over a field `K` of characteristic `p` and let `n` be prime to
`p`. Then `[n] : A ⟶ A` is étale; equivalently, its kernel `A[n]` is étale
(`AlgebraicGeometry.etale_torsionSubgroupScheme`).

By translation (`CategoryTheory.GrpObj.isPullback_ker_tensor`), the base change of `[n]` along
itself is the projection `A[n] ⊗ A ⟶ A`, a base change of the étale `A[n] ⟶ Spec K`. As `[n]`
is finite, flat and surjective (`AlgebraicGeometry.isIsogeny_npow_id`), étaleness descends
along it. -/
theorem etale_npow_id (p : ℕ) [CharP K p] (A : Over (Spec (.of K))) [GrpObj A]
    [IsAbelianVariety A] (n : ℕ) (hn : 0 < n) (hnp : ¬ p ∣ n) :
    Etale (𝟙 A ^ n).left := by
  have : Etale (GrpObj.ker (𝟙 A ^ n)).hom := etale_torsionSubgroupScheme p A n hn hnp
  have := isIsogeny_npow_id (A := A) n hn
  have := IsIsogeny.flat (𝟙 A ^ n)
  have := IsIsogeny.isFinite (𝟙 A ^ n)
  have := surjective_npow_id A n hn
  have sq := (Over.forget _).map_isPullback (GrpObj.isPullback_ker_tensor (𝟙 A ^ n) (𝟙 A)).flip
  have hsnd : Etale (snd (GrpObj.ker (𝟙 A ^ n)) A).left := by
    rw [Over.snd_left]
    infer_instance
  refine MorphismProperty.of_isPullback_of_descendsAlong
    (Q := (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme)) sq ?_ hsnd
  change (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme) (𝟙 A ≫ 𝟙 A ^ n).left
  rw [Category.id_comp]
  exact ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩

/-- Blueprint `proposition-multiplication-n--2`: The `n`-torsion of an abelian variety is étale.

For `n` prime to the characteristic of an algebraically closed base field `K`, the canonical
base-change map `A[n](K) ⟶ A[n](K')` is a bijection for every extension `K ⊆ K'` of
algebraically closed fields. This is also the second part of blueprint
`proposition-multiplication-n--2`.

`A[n]` is finite étale (`AlgebraicGeometry.etale_torsionSubgroupScheme`), so this is
`AlgebraicGeometry.bijective_toUnit_comp`. -/
theorem bijective_toUnit_comp_torsionSubgroupScheme [IsAlgClosed K] (p : ℕ) [CharP K p]
    (A : Over (Spec (.of K))) [GrpObj A] [IsAbelianVariety A] (n : ℕ) (hn : 0 < n)
    (hnp : ¬ p ∣ n) (K' : Type u) [Field K'] [Algebra K K'] [IsAlgClosed K'] :
    Function.Bijective
      (fun s : 𝟙_ (Over (Spec (.of K))) ⟶ torsionSubgroupScheme A n ↦
        toUnit (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K K')))) ≫ s) := by
  have := isFinite_torsionSubgroupScheme A n hn
  have := etale_torsionSubgroupScheme p A n hn hnp
  exact bijective_toUnit_comp (torsionSubgroupScheme A n)

/-- Blueprint `proposition-multiplication-n--2`: The `n`-torsion of an abelian variety is étale.

Let `A` be an abelian variety of dimension `g` over an algebraically closed field `K` of
characteristic `p` and let `n` be prime to `p`. Then `A(K)[n] ≅ (ℤ/nℤ) ^ (2 * g)`. This is also
the third part of blueprint `proposition-multiplication-n--2`.

The group `A(K)` is abelian and divisible (`AlgebraicGeometry.surjective_npow_points`). For a
prime `ℓ ∣ n` the `K`-points of the finite étale `A[ℓ]` are its `ℓ`-torsion
(`AlgebraicGeometry.torsionByEquiv`), so there are `ℓ ^ (2 * g)` of them
(`AlgebraicGeometry.card_points_eq_finrankΓ`), and
`AddSubgroup.nonempty_addEquiv_torsionBy_of_forall_prime` concludes. -/
theorem nonempty_addEquiv_torsionBy [IsAlgClosed K] (p : ℕ) [CharP K p]
    (A : Over (Spec (.of K))) [GrpObj A] [IsAbelianVariety A] (n : ℕ) (hn : 0 < n)
    (hnp : ¬ p ∣ n) :
    Nonempty (AddSubgroup.torsionBy (Additive (𝟙_ (Over (Spec (.of K))) ⟶ A)) (n : ℤ) ≃+
      (Fin (2 * IsAbelianVariety.dim A) → ZMod n)) := by
  let _ : DivisibleBy (Additive (𝟙_ (Over (Spec (.of K))) ⟶ A)) ℤ :=
    divisibleByOfSMulRightSurj _ _ fun {m} hm x ↦ by
      obtain ⟨a, ha⟩ := surjective_npow_points (A := A) m.natAbs (Int.natAbs_pos.2 hm) x.toMul
      refine ⟨m.sign • Additive.ofMul a, show m • _ = x from ?_⟩
      rw [smul_smul, Int.mul_sign_self, natCast_zsmul]
      exact congrArg Additive.ofMul ha
  refine AddSubgroup.nonempty_addEquiv_torsionBy_of_forall_prime _ _ hn.ne' fun ℓ hℓ hℓn ↦ ?_
  have hℓp : ¬ p ∣ ℓ := fun h ↦ hnp (h.trans hℓn)
  have := isFinite_torsionSubgroupScheme A ℓ hℓ.pos
  have := etale_torsionSubgroupScheme p A ℓ hℓ.pos hℓp
  rw [Nat.card_congr (torsionByEquiv A ℓ), card_points_eq_finrankΓ,
    finrankΓ_torsionSubgroupScheme ℓ hℓ.pos]

end AlgebraicGeometry
