/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.AlgClosed.Basic
public import WeilConjectures.AlgebraicGeometry.Curve.Divisor
public import WeilConjectures.AlgebraicGeometry.Curve.DivisorIdealSheaf
public import WeilConjectures.AlgebraicGeometry.Curve.RiemannRoch
public import WeilConjectures.AlgebraicGeometry.Picard.Group
public import WeilConjectures.AlgebraicGeometry.Sites.GmPicard

/-!
# The Picard group of a curve: degree, `Pic⁰` and divisor classes

Let `C` be a smooth proper curve over a field `k`. Its Picard group `Pic(C)` of invertible
`𝒪_C`-modules up to isomorphism (`AlgebraicGeometry.Scheme.Pic`, a group under `⊗`) carries a
*degree* homomorphism `deg : Pic(C) → ℤ`, and `Pic⁰(C) = ker deg`. Over an algebraically closed
field `k` we compare it with the divisor class group `Cl(C)` of
`WeilConjectures/AlgebraicGeometry/Curve/Divisor.lean`: a closed point `P` defines the class of
`𝒪_C(P) = 𝓘_Pᵛ`, the dual of its ideal sheaf, and `D ↦ [𝒪_C(D)]` identifies `Cl(C)` with
`Pic(C)`. The degree of `𝒪_C(D)` is the degree of `D`, which gives the degree map its meaning as
the degree of divisors, and shows that principal divisors have degree zero.

## Main definitions

- `AlgebraicGeometry.Scheme.picDegreeHom`: the degree `deg : Pic(C) →* ℤ`; its kernel is
  `Pic⁰(C)`, the set `AlgebraicGeometry.Scheme.Hom.picZero`
  (`AlgebraicGeometry.Scheme.coe_ker_picDegreeHom`).
- `AlgebraicGeometry.Scheme.Pic.ofClosedPoint`: the class of `𝒪_C(P)` for a closed point `P`.
- `AlgebraicGeometry.Scheme.Divisor.toPic`: the homomorphism `D ↦ [𝒪_C(D)]`, `Div(C) → Pic(C)`.

## Main statements

- `AlgebraicGeometry.Scheme.exists_divisorClassGroup_addEquiv_pic`: `Cl(C) ≅ Pic(C)` for a
  smooth integral curve (blueprint `proposition-cohomology-smooth-affine-curve`).
- `AlgebraicGeometry.Scheme.picDegreeHom_toPic`: `deg 𝒪_C(D) = deg D`.
- `AlgebraicGeometry.Scheme.surjective_picDegreeHom`: the degree is surjective.
- `AlgebraicGeometry.Scheme.exists_mulEquiv_prod_ker_picDegreeHom`:
  `Pic(C) ≅ ℤ × Pic⁰(C)` (blueprint `corollary-degree-jacobian--1`).

## Implementation notes

The degree of an invertible module is defined cohomologically, as `χ(ℒ) - χ(𝒪_C)`
(`AlgebraicGeometry.Scheme.Hom.picDegree`). The blueprint defines it instead as the degree of
divisors, transported along `Cl(C) ≅ Pic(C)`; the two agree by
`AlgebraicGeometry.Scheme.picDegreeHom_toPic`.

The module `𝒪_C(D)` of the blueprint is a subsheaf of the constant sheaf `k(C)`, which is not
available. Here `D ↦ [𝒪_C(D)]` is defined as the homomorphism sending `[P]` to the class of
`𝓘_Pᵛ`; for effective `D` the two constructions agree (blueprint
`theorem-riemann-roch-coherent-serre-duality`), so they define the same map to `Pic(C)`.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme

variable {k : Type u} [Field k] {C : Scheme.{u}} [C.Over (Spec (.of k))]

section Degree

variable [SmoothOfRelativeDimension 1 (C ↘ Spec (.of k))] [IsProper (C ↘ Spec (.of k))]

variable (k C) in
/-- Blueprint `corollary-degree-jacobian--1`: Picard group, degree, `Pic⁰`

The **degree homomorphism** `deg : Pic(C) → ℤ` of a smooth proper curve `C` over `k`, with
values in `Multiplicative ℤ` since the group law of `Pic(C)` is written multiplicatively. The
degree of the class of `ℒ` is `deg ℒ = χ(ℒ) - χ(𝒪_C)`
(`AlgebraicGeometry.Scheme.Hom.picDegree`); it is a homomorphism by
`AlgebraicGeometry.Scheme.Modules.degree_tensorObj`. Its kernel is `Pic⁰(C)`
(`AlgebraicGeometry.Scheme.coe_ker_picDegreeHom`), and it is the degree of divisors
(`AlgebraicGeometry.Scheme.picDegreeHom_toPic`).

(blueprint: `corollary-degree-jacobian--1`) -/
noncomputable def picDegreeHom : C.Pic →* Multiplicative ℤ where
  toFun L := .ofAdd ((C ↘ Spec (.of k)).picDegree L)
  map_one' := by
    rw [Hom.picDegree_eq, ofAdd_eq_one]
    exact (Modules.degree_congr k Pic.oneIso).trans (Modules.degree_unit k)
  map_mul' L L' := by
    rw [Hom.picDegree_eq, Hom.picDegree_eq, Hom.picDegree_eq, ← ofAdd_add]
    exact congrArg _ ((Modules.degree_congr k (Pic.mulIso L L')).trans
      (Modules.degree_tensorObj _ _))

lemma picDegreeHom_apply (L : C.Pic) :
    picDegreeHom k C L = .ofAdd ((C ↘ Spec (.of k)).picDegree L) :=
  rfl

/-- The degree of the class of an invertible module `ℳ` is `deg ℳ = χ(ℳ) - χ(𝒪_C)`. -/
lemma picDegreeHom_ofIsInvertible (ℳ : C.Modules) [ℳ.IsInvertible] :
    picDegreeHom k C (Pic.ofIsInvertible ℳ) = .ofAdd (ℳ.degree k) := by
  rw [picDegreeHom_apply, Hom.picDegree_eq]
  exact congrArg _ (Modules.degree_congr k (Pic.ofIsInvertibleIso ℳ))

/-- The kernel of the degree homomorphism is `Pic⁰(C)`, the set of classes of degree zero. -/
lemma coe_ker_picDegreeHom :
    ((picDegreeHom k C).ker : Set C.Pic) = (C ↘ Spec (.of k)).picZero := by
  ext L
  simp [Hom.picZero, MonoidHom.mem_ker, picDegreeHom_apply]

end Degree

section Divisor

variable [SmoothOfRelativeDimension 1 (C ↘ Spec (.of k))]

variable (k) in
/-- The class in `Pic(C)` of the invertible module `𝒪_C(P) = 𝓘_Pᵛ` of a closed point `P` of a
smooth curve `C` over `k`, the dual of the ideal sheaf of `P`. The ideal sheaf is invertible by
`AlgebraicGeometry.Scheme.isInvertible_vanishingIdeal_of_isClosed`. -/
noncomputable def Pic.ofClosedPoint (P : closedPoints C) : C.Pic :=
  have := (isInvertible_vanishingIdeal_of_isClosed (C ↘ Spec (.of k))
    P.2).isInvertible_dual_toModules
  Pic.ofIsInvertible (IdealSheafData.vanishingIdeal ⟨{P.1}, P.2⟩).toModulesᵛ

variable (k C) in
/-- The homomorphism `Div(C) → Pic(C)`, `D = ∑_P n_P [P] ↦ [𝒪_C(D)] = ∏_P [𝒪_C(P)]^{n_P}`, of a
smooth curve `C`, with values in `Additive C.Pic`.

This is the class map `D ↦ [𝒪_C(D)]` of blueprint `def-sc-divisor`. -/
noncomputable def Divisor.toPic : C.Divisor →+ Additive C.Pic :=
  Finsupp.liftAddHom fun P ↦ zmultiplesHom _ (.ofMul (Pic.ofClosedPoint k P))

@[simp]
lemma Divisor.toPic_single (P : closedPoints C) (n : ℤ) :
    Divisor.toPic k C (Finsupp.single P n) = n • .ofMul (Pic.ofClosedPoint k P) := by
  simp [Divisor.toPic]

/-- The class of the ideal sheaf of a product of invertible ideal sheaves is the product of the
classes. -/
lemma Pic.ofIsInvertible_toModules_mul {I J : C.IdealSheafData} (hI : I.IsInvertible)
    (hJ : J.IsInvertible) :
    haveI := hI.isInvertible_toModules
    haveI := hJ.isInvertible_toModules
    haveI := (hI.mul hJ).isInvertible_toModules
    Pic.ofIsInvertible (I * J).toModules =
      Pic.ofIsInvertible I.toModules * Pic.ofIsInvertible J.toModules := by
  have := hI.isInvertible_toModules
  have := hJ.isInvertible_toModules
  have := (hI.mul hJ).isInvertible_toModules
  obtain ⟨e⟩ := hI.nonempty_toModules_iso_dual_tensorObj_mul hJ
  have h := Pic.ofIsInvertible_eq_of_iso e
  rw [Pic.ofIsInvertible_tensorObj, Pic.ofIsInvertible_dual] at h
  rw [h, mul_right_comm, inv_mul_cancel, one_mul]

omit [SmoothOfRelativeDimension 1 (C ↘ Spec (.of k))] in
/-- The unit ideal sheaf has trivial class. -/
lemma Pic.ofIsInvertible_toModules_top :
    haveI := (IdealSheafData.isInvertible_top (X := C)).isInvertible_toModules
    Pic.ofIsInvertible (⊤ : C.IdealSheafData).toModules = 1 := by
  have hT := IdealSheafData.isInvertible_top (X := C)
  have := hT.isInvertible_toModules
  obtain ⟨e⟩ := hT.nonempty_toModules_iso_dual_tensorObj_mul hT
  have h := Pic.ofIsInvertible_eq_of_iso
    (e ≪≫ whiskerLeftIso _ (eqToIso (by rw [IdealSheafData.top_mul])))
  rw [Pic.ofIsInvertible_tensorObj, Pic.ofIsInvertible_dual, inv_mul_cancel] at h
  exact h

/-- The class of a power of an invertible ideal sheaf. -/
lemma Pic.ofIsInvertible_toModules_pow {I : C.IdealSheafData} (hI : I.IsInvertible) (n : ℕ) :
    haveI := hI.isInvertible_toModules
    haveI := (hI.pow n).isInvertible_toModules
    Pic.ofIsInvertible (I ^ n).toModules = Pic.ofIsInvertible I.toModules ^ n := by
  have := hI.isInvertible_toModules
  induction n with
  | zero =>
    have := (hI.pow 0).isInvertible_toModules
    have := (IdealSheafData.isInvertible_top (X := C)).isInvertible_toModules
    exact (Pic.ofIsInvertible_eq_of_iso (eqToIso (by rw [pow_zero]; rfl))).trans
      (Pic.ofIsInvertible_toModules_top.trans (pow_zero _).symm)
  | succ n ih =>
    have := (hI.pow n).isInvertible_toModules
    have := (hI.pow (n + 1)).isInvertible_toModules
    have := ((hI.pow n).mul hI).isInvertible_toModules
    exact (Pic.ofIsInvertible_eq_of_iso (eqToIso (by rw [pow_succ]))).trans
      ((Pic.ofIsInvertible_toModules_mul (hI.pow n) hI).trans (by rw [ih, pow_succ]))

/-- The class of the effective divisor `E` is the inverse of the class of its ideal sheaf
`𝒪_C(-E)`. -/
lemma Divisor.toMul_toPic_mapRange (E : closedPoints C →₀ ℕ) :
    haveI := (Divisor.isInvertible_idealSheaf (C ↘ Spec (.of k)) E).isInvertible_toModules
    (Divisor.toPic k C (E.mapRange Nat.cast Nat.cast_zero)).toMul =
      (Pic.ofIsInvertible (Divisor.idealSheaf E).toModules)⁻¹ := by
  induction E using Finsupp.induction_linear with
  | zero =>
    have := (IdealSheafData.isInvertible_top (X := C)).isInvertible_toModules
    have := (Divisor.isInvertible_idealSheaf (C ↘ Spec (.of k))
      (0 : closedPoints C →₀ ℕ)).isInvertible_toModules
    have h0 : Pic.ofIsInvertible (Divisor.idealSheaf (0 : closedPoints C →₀ ℕ)).toModules = 1 :=
      (Pic.ofIsInvertible_eq_of_iso (eqToIso (by rw [Divisor.idealSheaf_zero]))).trans
        Pic.ofIsInvertible_toModules_top
    rw [h0, inv_one, Finsupp.mapRange_zero, map_zero, toMul_zero]
  | add E E' hE₁ hE₂ =>
    have h₁ := Divisor.isInvertible_idealSheaf (C ↘ Spec (.of k)) E
    have h₂ := Divisor.isInvertible_idealSheaf (C ↘ Spec (.of k)) E'
    have := h₁.isInvertible_toModules
    have := h₂.isInvertible_toModules
    have := (h₁.mul h₂).isInvertible_toModules
    have := (Divisor.isInvertible_idealSheaf (C ↘ Spec (.of k)) (E + E')).isInvertible_toModules
    have hmul : Pic.ofIsInvertible (Divisor.idealSheaf (E + E')).toModules =
        Pic.ofIsInvertible (Divisor.idealSheaf E).toModules *
          Pic.ofIsInvertible (Divisor.idealSheaf E').toModules :=
      (Pic.ofIsInvertible_eq_of_iso (eqToIso (by rw [Divisor.idealSheaf_add]))).trans
        (Pic.ofIsInvertible_toModules_mul h₁ h₂)
    rw [hmul, mul_inv, Finsupp.mapRange_add (fun _ _ ↦ Nat.cast_add _ _), map_add, toMul_add,
      hE₁, hE₂]
  | single P n =>
    have hP := isInvertible_vanishingIdeal_of_smoothOfRelativeDimension_one
      (C ↘ Spec (.of k)) P.2
    have := hP.isInvertible_toModules
    have := (hP.pow n).isInvertible_toModules
    have := (Divisor.isInvertible_idealSheaf (C ↘ Spec (.of k))
      (Finsupp.single P n)).isInvertible_toModules
    have hpow : Pic.ofIsInvertible (Divisor.idealSheaf (Finsupp.single P n)).toModules =
        Pic.ofIsInvertible (IdealSheafData.vanishingIdeal ⟨{P.1}, P.2⟩).toModules ^ n :=
      (Pic.ofIsInvertible_eq_of_iso (eqToIso (by rw [Divisor.idealSheaf_single]))).trans
        (Pic.ofIsInvertible_toModules_pow hP n)
    rw [hpow, Finsupp.mapRange_single, Divisor.toPic_single, toMul_zsmul, toMul_ofMul,
      Pic.ofClosedPoint, Pic.ofIsInvertible_dual, inv_zpow, zpow_natCast]

/-- **The two modules `𝒪_C(E)` of an effective divisor agree.** For an effective divisor
`E = ∑_P n_P [P]` on a smooth curve `C`, the class `[𝒪_C(E)]` of the divisor theory
(`AlgebraicGeometry.Scheme.Divisor.toPic`, i.e. `∏_P [𝓘_Pᵛ]^{n_P}`) is the class of the dual
`𝓘_Eᵛ` of the ideal sheaf `𝓘_E = 𝒪_C(-E)` of the effective Cartier divisor `E`.

The blueprint compares two sheaves: `𝒪_C(E) ⊆ k(C)` (functions `g` with `div g + E ≥ 0`) and
`𝓘_Eᵛ = 𝓗om(𝓘_E, 𝒪_C)`. The constant sheaf `k(C)` is not available here, and the first module
enters the formalisation only through its class `AlgebraicGeometry.Scheme.Divisor.toPic`; the
statement is therefore the equality of the classes in `Pic(C)`, which is the content used
downstream. See `AlgebraicGeometry.Scheme.IdealSheafData.IsInvertible.toMul_toPic_eq` for the
version starting from an effective Cartier divisor, an invertible ideal sheaf.

(blueprint: `theorem-riemann-roch-coherent-serre-duality`) -/
lemma Divisor.toMul_toPic_mapRange_eq_dual (E : closedPoints C →₀ ℕ) :
    haveI := (Divisor.isInvertible_idealSheaf (C ↘ Spec (.of k)) E).isInvertible_dual_toModules
    (Divisor.toPic k C (E.mapRange Nat.cast Nat.cast_zero)).toMul =
      Pic.ofIsInvertible (Divisor.idealSheaf E).toModulesᵛ := by
  have := (Divisor.isInvertible_idealSheaf (C ↘ Spec (.of k)) E).isInvertible_toModules
  rw [Divisor.toMul_toPic_mapRange, Pic.ofIsInvertible_dual]

/-- **The two modules `𝒪_C(D)` of an effective Cartier divisor agree.** Let `C` be a smooth
integral Noetherian curve and `𝓘` an invertible ideal sheaf, i.e. an effective Cartier divisor,
with divisor `D = ∑_P ord_P(𝓘) [P]`. Then the class `[𝒪_C(D)]` of the divisor theory
(`AlgebraicGeometry.Scheme.Divisor.toPic`) is the class of `𝒪_C(D) = 𝓘ᵛ`. Indeed `𝓘` is the
ideal sheaf of the effective divisor `D`
(`AlgebraicGeometry.Scheme.IdealSheafData.IsInvertible.exists_eq_idealSheaf`), and
`AlgebraicGeometry.Scheme.Divisor.toMul_toPic_mapRange_eq_dual` applies.

(blueprint: `theorem-riemann-roch-coherent-serre-duality`) -/
theorem IdealSheafData.IsInvertible.toMul_toPic_eq [IsIntegral C] [IsNoetherian C]
    {I : C.IdealSheafData} (hI : I.IsInvertible) :
    haveI := hI.isInvertible_dual_toModules
    ∃ D : C.Divisor, (∀ P : closedPoints C, D P = I.ordAt P.1) ∧
      (Divisor.toPic k C D).toMul = Pic.ofIsInvertible I.toModulesᵛ := by
  obtain ⟨E, rfl⟩ := hI.exists_eq_idealSheaf (C ↘ Spec (.of k))
  exact ⟨E.mapRange Nat.cast Nat.cast_zero, fun P ↦ by
    rw [Finsupp.mapRange_apply, Divisor.ordAt_idealSheaf (C ↘ Spec (.of k))],
    Divisor.toMul_toPic_mapRange_eq_dual E⟩

/-- The class of a divisor `D = E₁ - E₂` with `E₁, E₂` effective is `[𝒪_C(-E₁)]⁻¹ [𝒪_C(-E₂)]`. -/
lemma Divisor.toMul_toPic_mapRange_sub (E₁ E₂ : closedPoints C →₀ ℕ) :
    haveI := (Divisor.isInvertible_idealSheaf (C ↘ Spec (.of k)) E₁).isInvertible_toModules
    haveI := (Divisor.isInvertible_idealSheaf (C ↘ Spec (.of k)) E₂).isInvertible_toModules
    (Divisor.toPic k C (E₁.mapRange Nat.cast Nat.cast_zero -
        E₂.mapRange Nat.cast Nat.cast_zero)).toMul =
      (Pic.ofIsInvertible (Divisor.idealSheaf E₁).toModules)⁻¹ *
        Pic.ofIsInvertible (Divisor.idealSheaf E₂).toModules := by
  rw [map_sub, toMul_sub, Divisor.toMul_toPic_mapRange, Divisor.toMul_toPic_mapRange,
    div_inv_eq_mul]

/-- Every divisor is `E₁ - E₂` for effective divisors `E₁` and `E₂`, its positive and negative
parts. -/
lemma Divisor.mapRange_toNat_sub (D : C.Divisor) :
    (D.mapRange Int.toNat Int.toNat_zero).mapRange Nat.cast Nat.cast_zero -
      ((-D).mapRange Int.toNat Int.toNat_zero).mapRange Nat.cast Nat.cast_zero = D := by
  ext P
  simp only [Finsupp.coe_sub, Pi.sub_apply, Finsupp.mapRange_apply, Finsupp.coe_neg,
    Pi.neg_apply]
  exact Int.toNat_sub_toNat_neg (D P)

/-- Blueprint `proposition-cohomology-smooth-affine-curve`: `Pic` is the divisor class group for
smooth curves

Let `C` be a smooth integral (equivalently, connected) curve over `k`, proper or not. Then the
map `Cl(C) → Pic(C)`, `D ↦ [𝒪_C(D)]`, is a well-defined isomorphism of abelian groups.

Write `D = E₁ - E₂` with `E₁, E₂` effective, so that `[𝒪_C(D)] = [𝒪_C(-E₁)]⁻¹ [𝒪_C(-E₂)]`
(`AlgebraicGeometry.Scheme.Divisor.toMul_toPic_mapRange_sub`). The map is well defined, since
for `D = div g` multiplication by `g` is an isomorphism `𝒪_C(-E₂) ≅ 𝒪_C(-E₁)`
(`AlgebraicGeometry.Scheme.Divisor.nonempty_toModules_idealSheaf_iso_of_ord_eq`), and injective,
since conversely every isomorphism `𝒪_C(-E₂) ≅ 𝒪_C(-E₁)` is multiplication by some `g` with
`div g = E₁ - E₂` (`AlgebraicGeometry.Scheme.Divisor.exists_ord_eq_of_nonempty_iso`). It is
surjective since every invertible module is `𝒪_C(E₁) ⊗ 𝒪_C(-E₂)`, a nonzero rational section
giving a nonzero morphism `𝒪_C(-E₂) ⟶ ℒ` whose zero scheme is a sum of points
(`AlgebraicGeometry.Scheme.Modules.exists_nonempty_iso_dual_toModules_idealSheaf_tensorObj`;
blueprint `theorem-riemann-roch-coherent-serre-duality--1`).

This is the identification `Cl(C) ≅ Pic(C)` asserted in blueprint `def-sc-divisor`. -/
theorem exists_divisorClassGroup_addEquiv_pic [IsCurve (C ↘ Spec (.of k))] [IsIntegral C]
    [IsNoetherian C] :
    ∃ e : C.DivisorClassGroup ≃+ Additive C.Pic,
      ∀ D : C.Divisor, e (QuotientAddGroup.mk D) = Divisor.toPic k C D := by
  have hker : (Divisor.toPic k C).ker = C.principalDivisors := by
    ext D
    set E₁ := D.mapRange Int.toNat Int.toNat_zero
    set E₂ := (-D).mapRange Int.toNat Int.toNat_zero
    have hJ₁ := Divisor.isInvertible_idealSheaf (C ↘ Spec (.of k)) E₁
    have hJ₂ := Divisor.isInvertible_idealSheaf (C ↘ Spec (.of k)) E₂
    have := hJ₁.isInvertible_toModules
    have := hJ₂.isInvertible_toModules
    have hD := Divisor.toMul_toPic_mapRange_sub (k := k) E₁ E₂
    rw [Divisor.mapRange_toNat_sub] at hD
    have hE (P : closedPoints C) : D P = E₁ P - E₂ P := by
      simp only [E₁, E₂, Finsupp.mapRange_apply, Finsupp.coe_neg, Pi.neg_apply]
      exact (Int.toNat_sub_toNat_neg (D P)).symm
    rw [AddMonoidHom.mem_ker]
    constructor
    · intro h0
      rw [h0, toMul_zero, eq_comm, inv_mul_eq_one] at hD
      obtain ⟨e⟩ := Pic.nonempty_iso_of_ofIsInvertible_eq hD.symm
      obtain ⟨g, hg, hgD⟩ := Divisor.exists_ord_eq_of_nonempty_iso (C ↘ Spec (.of k)) e
      refine ⟨Additive.ofMul (Units.mk0 g hg), ?_⟩
      ext P
      rw [div_apply, hE, ← hgD]
      rfl
    · rintro ⟨g, rfl⟩
      have hg : (g.toMul : C.functionField) ≠ 0 := g.toMul.ne_zero
      obtain ⟨e⟩ := Divisor.nonempty_toModules_idealSheaf_iso_of_ord_eq (C ↘ Spec (.of k))
        (E₁ := E₁) (E₂ := E₂) hg fun P ↦ by rw [← hE, div_apply]
      rw [← toMul_eq_one, hD, Pic.ofIsInvertible_eq_of_iso e, inv_mul_cancel]
  have hsurj : Function.Surjective (Divisor.toPic k C) := by
    intro L
    obtain ⟨E₁, E₂, ⟨e⟩⟩ :=
      Modules.exists_nonempty_iso_dual_toModules_idealSheaf_tensorObj (C ↘ Spec (.of k))
        ((fromSkeleton C.Modules).obj L.toMul.val)
    have hJ₁ := Divisor.isInvertible_idealSheaf (C ↘ Spec (.of k)) E₁
    have hJ₂ := Divisor.isInvertible_idealSheaf (C ↘ Spec (.of k)) E₂
    have := hJ₁.isInvertible_toModules
    have := hJ₂.isInvertible_toModules
    refine ⟨E₁.mapRange Nat.cast Nat.cast_zero - E₂.mapRange Nat.cast Nat.cast_zero, ?_⟩
    apply Additive.toMul.injective
    rw [Divisor.toMul_toPic_mapRange_sub, ← Pic.ofIsInvertible_fromSkeleton L.toMul,
      Pic.ofIsInvertible_eq_of_iso e, Pic.ofIsInvertible_tensorObj, Pic.ofIsInvertible_dual]
  exact ⟨(QuotientAddGroup.quotientAddEquivOfEq hker.symm).trans
    (QuotientAddGroup.quotientKerEquivOfSurjective _ hsurj), fun D ↦ rfl⟩

end Divisor

section AlgClosed

variable [IsAlgClosed k]

/-- Over an algebraically closed field `k`, the ideal sheaf of the `k`-point
`AlgebraicGeometry.pointOfClosedPoint` of a closed point `P` is the ideal sheaf of `P`: the
point `Spec k` is reduced and maps onto `{P}`. -/
lemma ker_pointOfClosedPoint [LocallyOfFiniteType (C ↘ Spec (.of k))] (P : closedPoints C) :
    (pointOfClosedPoint (C ↘ Spec (.of k)) P.1 P.2).ker =
      IdealSheafData.vanishingIdeal ⟨{P.1}, P.2⟩ := by
  rw [← IdealSheafData.map_bot, ← nilradical_eq_bot, ← IdealSheafData.vanishingIdeal_top,
    IdealSheafData.map_vanishingIdeal]
  congr 1
  ext1
  have : Set.range (pointOfClosedPoint (C ↘ Spec (.of k)) P.1 P.2) = {P.1} :=
    Set.range_eq_singleton_iff.2 fun a ↦ pointOfClosedPoint_apply _ _ _ a
  rw [TopologicalSpace.Closeds.coe_closure, TopologicalSpace.Closeds.coe_top, Set.image_univ,
    this]
  exact (P.2 : IsClosed {P.1}).closure_eq

variable [SmoothOfRelativeDimension 1 (C ↘ Spec (.of k))] [IsProper (C ↘ Spec (.of k))]

/-- The `k`-point `AlgebraicGeometry.pointOfClosedPoint` of a closed point, as a `k`-rational
point. -/
noncomputable def fieldPointOfClosedPoint (P : closedPoints C) :
    (C ↘ Spec (.of k)).fieldPoints k :=
  ⟨pointOfClosedPoint (C ↘ Spec (.of k)) P.1 P.2,
    (pointOfClosedPoint_comp (C ↘ Spec (.of k)) P.1 P.2).trans (by
      rw [Algebra.algebraMap_self, CommRingCat.ofHom_id, Spec.map_id])⟩

/-- Over an algebraically closed field, the class `𝒪_C(P)` of a closed point has degree one.

(blueprint: `corollary-degree-jacobian--1`) -/
lemma picDegreeHom_ofClosedPoint (P : closedPoints C) :
    picDegreeHom k C (Pic.ofClosedPoint k P) = .ofAdd 1 := by
  have hJ := isInvertible_vanishingIdeal_of_isClosed (C ↘ Spec (.of k)) P.2
  have := hJ.isInvertible_dual_toModules
  rw [Pic.ofClosedPoint, picDegreeHom_ofIsInvertible, hJ.degree_dual_toModules_eq_one]
  have h := (C ↘ Spec (.of k)).finrankΓ_subschemeι_ker_fieldPoints (fieldPointOfClosedPoint P)
  rwa [fieldPointOfClosedPoint, ker_pointOfClosedPoint] at h

/-- **The degree on `Pic(C)` is the degree of divisors.** Over an algebraically closed field,
`deg 𝒪_C(D) = deg D` for every divisor `D` on a smooth proper curve `C`.

(blueprint: `corollary-degree-jacobian--1`) -/
theorem picDegreeHom_toPic (D : C.Divisor) :
    picDegreeHom k C (Divisor.toPic k C D).toMul = .ofAdd (Divisor.degree C D) := by
  induction D using Finsupp.induction_linear with
  | zero => simp
  | add D D' hD hD' => simp [hD, hD']
  | single P n =>
    simp [picDegreeHom_ofClosedPoint, ← ofAdd_zsmul]

/-- **The degree is surjective.** A nonempty smooth proper curve over an algebraically closed
field has a closed point `P`, and `𝒪_C(P)` has degree one. -/
theorem surjective_picDegreeHom [Nonempty C] : Function.Surjective (picDegreeHom k C) := by
  have := QuasiCompact.compactSpace_of_compactSpace (C ↘ Spec (.of k))
  obtain ⟨P, -, hP⟩ := isClosed_univ.exists_closed_singleton (X := C) Set.univ_nonempty
  intro n
  refine ⟨Pic.ofClosedPoint k ⟨P, hP⟩ ^ n.toAdd, ?_⟩
  rw [map_zpow, picDegreeHom_ofClosedPoint, ← ofAdd_zsmul, smul_eq_mul, mul_one, ofAdd_toAdd]

/-- Blueprint `corollary-degree-jacobian--1`: Structure of the Picard group of a proper curve

Let `C` be a nonempty (for instance, connected) smooth proper curve over an algebraically closed
field `k`. The degree sequence `0 → Pic⁰(C) → Pic(C) → ℤ → 0` splits, so
`Pic(C) ≅ ℤ × Pic⁰(C)`, compatibly with the degree.

The degree is surjective (`AlgebraicGeometry.Scheme.surjective_picDegreeHom`): a closed point
`P` has residue field `k` and `𝒪_C(P)` has degree one. The class of `𝒪_C(P)` generates a
section `n ↦ [𝒪_C(P)]^n` of the degree. -/
theorem exists_mulEquiv_prod_ker_picDegreeHom [Nonempty C] :
    ∃ e : C.Pic ≃* Multiplicative ℤ × (picDegreeHom k C).ker,
      ∀ L, (e L).1 = picDegreeHom k C L := by
  obtain ⟨g, hg⟩ := surjective_picDegreeHom (k := k) (C := C) (.ofAdd 1)
  let σ : Multiplicative ℤ →* C.Pic := zpowersHom C.Pic g
  have hσ (n : Multiplicative ℤ) : picDegreeHom k C (σ n) = n := by
    rw [zpowersHom_apply, map_zpow, hg, ← ofAdd_zsmul, smul_eq_mul, mul_one, ofAdd_toAdd]
  refine ⟨{
    toFun L := (picDegreeHom k C L, ⟨L * (σ (picDegreeHom k C L))⁻¹, by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hσ, mul_inv_cancel]⟩)
    invFun p := σ p.1 * p.2
    left_inv L := by simp
    right_inv p := by
      have h2 : picDegreeHom k C p.2 = 1 := p.2.2
      have h : picDegreeHom k C (σ p.1 * p.2) = p.1 := by rw [map_mul, hσ, h2, mul_one]
      ext
      · exact h
      · simp [h]
    map_mul' L L' := by
      ext
      · exact map_mul (picDegreeHom k C) L L'
      · simp only [Prod.snd_mul, Subgroup.coe_mul]
        rw [map_mul (picDegreeHom k C), map_mul σ, mul_inv]
        ac_rfl }, fun _ ↦ rfl⟩

variable [IsIntegral C] [IsNoetherian C]

variable (k) in
include k in
omit [IsAlgClosed k] [IsProper (C ↘ Spec (.of k))] in
/-- On a smooth curve, a rational function has nonzero order only at closed points: a
point of codimension one which is not closed specializes to a closed point, which would then
have codimension at least two, while the local rings at closed points have dimension one. -/
lemma isClosed_of_ord_ne_zero {f : C.functionField} {x : C} (hx : C.ord f x ≠ 0) :
    IsClosed {x} := by
  have hx1 : Order.coheight x = 1 := by
    by_contra h
    exact hx (ord_eq_zero_of_coheight_neq_one h _)
  by_contra hnc
  obtain ⟨y, hy, hyc⟩ :=
    isClosed_closure.exists_closed_singleton (S := closure {x}) ⟨x, subset_closure rfl⟩
  have hne : y ≠ x := fun h ↦ hnc (h ▸ hyc)
  have h := Order.coheight_add_one_le
    (lt_of_specializes_of_ne C (specializes_iff_mem_closure.2 hy) hne)
  have hy1 : (Order.coheight y : WithBot ℕ∞) = 1 := by
    rw [← ringKrullDim_stalk_eq_coheight,
      ringKrullDim_stalk_eq_one_of_isClosed (C ↘ Spec (.of k)) hyc]
  have hy1 : Order.coheight y = 1 := by exact_mod_cast hy1
  rw [hx1, hy1] at h
  exact absurd h (by decide)

variable (k) in
include k in
/-- **Principal divisors have degree zero** on a smooth proper integral curve over an
algebraically closed field: `deg div(f) = ∑_P v_P(f) = 0`
(`AlgebraicGeometry.Scheme.finsum_ord_eq_zero`).

(blueprint: `corollary-degree-jacobian--1`) -/
theorem degree_div_eq_zero (f : Additive C.functionFieldˣ) : Divisor.degree C (C.div f) = 0 := by
  have := QuasiCompact.compactSpace_of_compactSpace (C ↘ Spec (.of k))
  rw [← finsum_ord_eq_zero k C f.toMul.ne_zero, Divisor.degree_apply, Finsupp.sum,
    ← finsum_eq_sum_of_support_subset _ (s := (C.div f).support) (by simp)]
  simp only [div_apply]
  rw [finsum_set_coe_eq_finsum_mem (f := fun x ↦ C.ord (f.toMul : C.functionField) x),
    finsum_mem_def]
  rw [(Set.indicator_eq_self (s := closedPoints C)).2 fun y hy ↦ isClosed_of_ord_ne_zero k hy]

/-- Blueprint `corollary-degree-jacobian--1`: Picard group, degree, `Pic⁰`

Let `C` be a smooth proper integral (equivalently, connected) curve over an algebraically closed
field `k`. Its Picard group `Pic(C)` is the group of invertible `𝒪_C`-modules up to isomorphism,
with the degree homomorphism `deg : Pic(C) → ℤ` (`AlgebraicGeometry.Scheme.picDegreeHom`) and
`Pic⁰(C) = ker deg`. The two facts asserted in the definition hold.

- **(P1)** `Pic(C)` is in bijection with `H¹(C_Zar, 𝒪_Cˣ)` and with `H¹(C_ét, 𝔾ₘ)` (Hilbert 90,
  `AlgebraicGeometry.Scheme.nonempty_equiv_H_one_unitsSheaf`), and it is the divisor class
  group `Div(C) / Princ(C)` via `D ↦ [𝒪_C(D)]`
  (`AlgebraicGeometry.Scheme.exists_divisorClassGroup_addEquiv_pic`).
- **(P2)** The degree `deg (∑_P n_P [P]) = ∑_P n_P` kills principal divisors
  (`AlgebraicGeometry.Scheme.degree_div_eq_zero`), so it descends to `Pic(C)`, where it is
  `deg` (`AlgebraicGeometry.Scheme.picDegreeHom_toPic`); it is surjective since `C` has a
  closed point (`AlgebraicGeometry.Scheme.surjective_picDegreeHom`).

Only the existence of the bijections in (P1) is recorded, not that they are the canonical maps
`ℒ ↦ [Isom(𝒪, ℒ)]`, nor that they are group isomorphisms. -/
theorem nonempty_equiv_H_one_and_surjective_picDegreeHom :
    (Nonempty (C.Pic ≃ Sheaf.H C.unitsSheaf 1) ∧
        Nonempty (Sheaf.H C.unitsSheaf 1 ≃ C.CohomologicalPicardGroup) ∧
        ∃ e : C.DivisorClassGroup ≃+ Additive C.Pic,
          ∀ D : C.Divisor, e (QuotientAddGroup.mk D) = Divisor.toPic k C D) ∧
      (∀ f, Divisor.degree C (C.div f) = 0) ∧
      (∀ D, picDegreeHom k C (Divisor.toPic k C D).toMul = .ofAdd (Divisor.degree C D)) ∧
      Function.Surjective (picDegreeHom k C) := by
  have : IsCurve (C ↘ Spec (.of k)) :=
    { krullDim_le_one := topologicalKrullDim_le_of_smoothOfRelativeDimension (C ↘ Spec (.of k)) 1 }
  have : Nonempty C := ⟨genericPoint C⟩
  exact ⟨⟨(nonempty_equiv_H_one_unitsSheaf C).1, (nonempty_equiv_H_one_unitsSheaf C).2,
    exists_divisorClassGroup_addEquiv_pic⟩, degree_div_eq_zero k, picDegreeHom_toPic,
    surjective_picDegreeHom⟩

end AlgClosed

end AlgebraicGeometry.Scheme
