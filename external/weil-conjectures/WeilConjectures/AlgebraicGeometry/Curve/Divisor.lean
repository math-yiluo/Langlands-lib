/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.OrderOfVanishing
public import Mathlib.Topology.JacobsonSpace
public import WeilConjectures.Mathlib.AlgebraicGeometry.OrderOfVanishing

/-!
# Divisors, principal divisors and the divisor class group of a curve

Let `X` be a Noetherian integral scheme, for instance a connected smooth curve over a field. A
*divisor* on `X` is a finite formal sum `D = ∑_P n_P [P]` of closed points of `X` with integer
coefficients, and `deg D = ∑_P n_P`. For a nonzero rational function `f ∈ k(X)`, its divisor is
`div f = ∑_P v_P(f) [P]`, where `v_P = AlgebraicGeometry.Scheme.ord` is the order of vanishing at
`P`; such divisors are *principal*, and the divisor class group is
`Cl(X) = Div(X) / {div f : f ∈ k(X)ˣ}`.

The function field `k(X)` (blueprint `def-sc-function-field`) is Mathlib's
`AlgebraicGeometry.Scheme.functionField`, the stalk at the generic point; it is the fraction
field of `Γ(X, U)` for every nonempty affine open `U`
(`AlgebraicGeometry.functionField_isFractionRing_of_isAffineOpen`).

## Main definitions

- `AlgebraicGeometry.Scheme.Divisor`: the free abelian group `Div(X)` on the closed points.
- `AlgebraicGeometry.Scheme.Divisor.degree`: the degree `∑_P n_P` of a divisor.
- `AlgebraicGeometry.Scheme.div`: the divisor `div f` of a nonzero rational function.
- `AlgebraicGeometry.Scheme.principalDivisors`: the subgroup of principal divisors.
- `AlgebraicGeometry.Scheme.DivisorClassGroup`: the divisor class group `Cl(X)`.

## Main statements

- `AlgebraicGeometry.Scheme.finite_setOf_ord_ne_zero`: a nonzero rational function on a
  Noetherian integral scheme has finitely many zeros and poles.

## Implementation notes

As in the blueprint, divisors are supported on the closed points. On a connected curve these
are exactly the points of codimension one, the only points where `ord` can be nonzero; for a
smooth proper curve this is `AlgebraicGeometry.Scheme.isClosed_of_ord_ne_zero`.
-/

@[expose] public section

universe u

open CategoryTheory TopologicalSpace Order

namespace AlgebraicGeometry.Scheme

variable (X : Scheme.{u})

/-- Blueprint `def-sc-divisor`: Divisors, principal divisors, class group

A *divisor* on a curve `X` is a finite formal sum `D = ∑_P n_P [P]` of closed points `P` of `X`
with integer coefficients: `Div(X)` is the free abelian group on the closed points of `X`. -/
abbrev Divisor : Type u :=
  closedPoints X →₀ ℤ

/-- Blueprint `def-sc-divisor`: Divisors, principal divisors, class group

The *degree* `deg D = ∑_P n_P` of a divisor `D = ∑_P n_P [P]`. Over an algebraically closed
field, where every closed point is rational, this is the usual degree. -/
noncomputable def Divisor.degree : X.Divisor →+ ℤ :=
  Finsupp.liftAddHom fun _ ↦ AddMonoidHom.id ℤ

variable {X} in
lemma Divisor.degree_apply (D : X.Divisor) : Divisor.degree X D = D.sum fun _ n ↦ n :=
  rfl

variable {X} in
@[simp]
lemma Divisor.degree_single (P : closedPoints X) (n : ℤ) :
    Divisor.degree X (Finsupp.single P n) = n := by
  simp [Divisor.degree_apply]

/-- If two points `x ≠ y` of a scheme satisfy `y ⤳ x`, then `x < y` in the specialization
order. -/
lemma lt_of_specializes_of_ne {x y : X} (h : y ⤳ x) (hxy : x ≠ y) : x < y :=
  ⟨h, fun h' ↦ hxy (h'.antisymm h).eq⟩

variable {X}

/-- A nonzero rational function on an integral scheme is a unit on a nonempty open subset. -/
lemma exists_isUnit_germToFunctionField_eq [IsIntegral X] {f : X.functionField} (hf : f ≠ 0) :
    ∃ (W : X.Opens) (_ : Nonempty W) (s : Γ(X, W)), IsUnit s ∧ X.germToFunctionField W s = f := by
  obtain ⟨U, hU, s, hs⟩ := X.presheaf.exists_germ_eq f
  obtain ⟨V, hV, t, ht⟩ := X.presheaf.exists_germ_eq f⁻¹
  have hUV : genericPoint X ∈ U ⊓ V := ⟨hU, hV⟩
  have hst : X.presheaf.germ (U ⊓ V) _ hUV
      (X.presheaf.map (homOfLE inf_le_left).op s * X.presheaf.map (homOfLE inf_le_right).op t) =
      X.presheaf.germ ⊤ (genericPoint X) trivial 1 := by
    rw [map_mul, TopCat.Presheaf.germ_res_apply, TopCat.Presheaf.germ_res_apply, hs, ht,
      mul_inv_cancel₀ hf]
    exact (map_one _).symm
  obtain ⟨W, hW, iU, iV, e⟩ := X.presheaf.germ_eq _ _ _ _ _ hst
  have : Nonempty W := ⟨⟨_, hW⟩⟩
  refine ⟨W, this, X.presheaf.map (iU ≫ homOfLE inf_le_left).op s, ?_, ?_⟩
  · refine IsUnit.of_mul_eq_one (X.presheaf.map (iU ≫ homOfLE inf_le_right).op t) ?_
    rw [map_one] at e
    rw [← e, map_mul, op_comp, op_comp, Functor.map_comp, Functor.map_comp]
    rfl
  · change X.presheaf.germ W _ hW _ = f
    rw [TopCat.Presheaf.germ_res_apply, hs]

variable [IsIntegral X] [IsNoetherian X]

/-- **Zeros and poles of a rational function are finite.** A nonzero rational function `f` on a
Noetherian integral scheme `X` has `ord_x f = 0` for all but finitely many points `x`.

The function `f` is a unit on a nonempty open `W`, so its order vanishes on `W`. Every point `x`
of codimension one outside `W` is the generic point of an irreducible component of the closed
set `X ∖ W`: otherwise `x` would be a proper specialization of such a generic point `z`, itself a
proper specialization of the generic point of `X`, and `x` would have codimension at least two.
There are finitely many such components since `X` is Noetherian. -/
theorem finite_setOf_ord_ne_zero {f : X.functionField} (hf : f ≠ 0) :
    {x : X | X.ord f x ≠ 0}.Finite := by
  obtain ⟨W, hW, s, hs, rfl⟩ := exists_isUnit_germToFunctionField_eq hf
  obtain ⟨S, hSf, hSc, hSi, hSU⟩ :=
    NoetherianSpace.exists_finite_set_isClosed_irreducible W.isOpen.isClosed_compl
  classical
  let g : Set X → X := fun t ↦ if ht : IsIrreducible t then ht.genericPoint else genericPoint X
  refine (hSf.image g).subset fun x hx ↦ ?_
  have hx1 : coheight x = 1 := by
    by_contra h
    exact hx (ord_eq_zero_of_coheight_neq_one h _)
  have hxW : x ∉ W := fun hxW ↦ hx (ord_of_isUnit hs hxW)
  obtain ⟨t, htS, hxt⟩ : x ∈ ⋃₀ S := hSU ▸ hxW
  refine ⟨t, htS, ?_⟩
  have hgt : IsGenericPoint (g t) t := by
    simp only [g, dite_eq_left (hSi t htS)]
    exact (hSi t htS).isGenericPoint_genericPoint (hSc t htS)
  by_contra hne
  have hgW : g t ∉ W := by
    have : g t ∈ ⋃₀ S := Set.mem_sUnion_of_mem hgt.mem htS
    rwa [← hSU] at this
  have hηW : genericPoint X ∈ W :=
    ((genericPoint_spec X).mem_open_set_iff W.isOpen).mpr (by simpa using hW)
  have h₁ := coheight_add_one_le (lt_of_specializes_of_ne X (hgt.specializes hxt) (Ne.symm hne))
  have h₂ := coheight_add_one_le (lt_of_specializes_of_ne X (genericPoint_specializes (g t))
    (fun h ↦ hgW (h ▸ hηW)))
  have : (1 : ℕ∞) + 1 ≤ 1 := by
    calc (1 : ℕ∞) + 1 ≤ coheight (genericPoint X) + 1 + 1 := by gcongr; exact le_add_self
      _ ≤ coheight (g t) + 1 := by gcongr
      _ ≤ 1 := hx1 ▸ h₁
  exact absurd this (by decide)

lemma ord_one (x : X) : X.ord 1 x = 0 := by
  have h := ord_mul (x := x) (one_ne_zero (α := X.functionField))
    (one_ne_zero (α := X.functionField))
  rw [mul_one] at h
  omega

variable (X) in
/-- Blueprint `def-sc-divisor`: Divisors, principal divisors, class group

The *divisor* `div f = ∑_P v_P(f) [P]` of a nonzero rational function `f ∈ k(X)ˣ` on a Noetherian
integral scheme `X`, where `v_P` is the order of vanishing
`AlgebraicGeometry.Scheme.ord` at the closed point `P`. Its support is finite by
`AlgebraicGeometry.Scheme.finite_setOf_ord_ne_zero`. On a smooth curve, `v_P` is the normalized
valuation of the discrete valuation ring `𝒪_{X,P}`. -/
noncomputable def div : Additive X.functionFieldˣ →+ X.Divisor where
  toFun f := Finsupp.ofSupportFinite (fun P : closedPoints X ↦ X.ord (f.toMul : X.functionField) P)
    ((finite_setOf_ord_ne_zero f.toMul.ne_zero).preimage Subtype.val_injective.injOn)
  map_zero' := by
    ext P
    simp [Finsupp.ofSupportFinite_coe, ord_one]
  map_add' f g := by
    ext P
    simp only [toMul_add, Units.val_mul, Finsupp.coe_add, Pi.add_apply,
      Finsupp.ofSupportFinite_coe]
    exact ord_mul f.toMul.ne_zero g.toMul.ne_zero

@[simp]
lemma div_apply (f : Additive X.functionFieldˣ) (P : closedPoints X) :
    X.div f P = X.ord (f.toMul : X.functionField) P :=
  rfl

variable (X) in
/-- Blueprint `def-sc-divisor`: Divisors, principal divisors, class group

The subgroup of *principal divisors* `div f`, for `f ∈ k(X)ˣ`. -/
noncomputable def principalDivisors : AddSubgroup X.Divisor :=
  X.div.range

variable (X) in
/-- Blueprint `def-sc-divisor`: Divisors, principal divisors, class group

The *divisor class group* `Cl(X) = Div(X) / {div f : f ∈ k(X)ˣ}`. -/
abbrev DivisorClassGroup : Type u :=
  X.Divisor ⧸ X.principalDivisors

end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.Scheme

section OpenImmersion

variable {U X : Scheme.{u}} (i : U ⟶ X) [IsOpenImmersion i] [JacobsonSpace X]

/-- An open immersion into a Jacobson scheme maps closed points to closed points. -/
noncomputable def Hom.closedPointsMap (P : closedPoints U) : closedPoints X :=
  ⟨i P.1, by
    have h : P.1 ∈ i ⁻¹' closedPoints X := by
      rw [i.isOpenEmbedding.preimage_closedPoints]; exact P.2
    exact h⟩

lemma Hom.closedPointsMap_injective : Function.Injective i.closedPointsMap :=
  fun _ _ h ↦ Subtype.ext (i.isOpenEmbedding.injective (congrArg Subtype.val h))

/-- The restriction `Div(X) → Div(U)` of divisors along an open immersion `i : U ⟶ X`. -/
noncomputable def Divisor.comap : X.Divisor →+ U.Divisor :=
  Finsupp.comapDomain.addMonoidHom i.closedPointsMap_injective

@[simp]
lemma Divisor.comap_apply (D : X.Divisor) (P : closedPoints U) :
    Divisor.comap i D P = D (i.closedPointsMap P) :=
  rfl

lemma Divisor.surjective_comap : Function.Surjective (Divisor.comap i) := by
  intro D
  refine ⟨Finsupp.mapDomain i.closedPointsMap D, ?_⟩
  ext P
  rw [comap_apply, Finsupp.mapDomain_apply_of_injective i.closedPointsMap_injective]


/-- A divisor restricts to zero on `U` iff it is supported outside the image of `U`. -/
lemma Divisor.comap_eq_zero_iff (D : X.Divisor) :
    Divisor.comap i D = 0 ↔ ∀ P : closedPoints X, D P ≠ 0 → P.1 ∉ Set.range i := by
  constructor
  · rintro h P hP ⟨y, hy⟩
    have hy' : y ∈ i ⁻¹' closedPoints X := by rw [Set.mem_preimage, hy]; exact P.2
    rw [i.isOpenEmbedding.preimage_closedPoints] at hy'
    have hP' : i.closedPointsMap ⟨y, hy'⟩ = P := Subtype.ext hy
    exact hP (by simpa [hP'] using DFunLike.congr_fun h ⟨y, hy'⟩)
  · intro h
    ext P
    by_contra hP
    exact h _ hP ⟨P.1, rfl⟩

variable [IsIntegral X] [IsNoetherian X] [IsIntegral U] [IsNoetherian U]

/-- Restriction of divisors along an open immersion commutes with taking divisors of rational
functions. -/
theorem Divisor.comap_div (g : Additive X.functionFieldˣ) :
    Divisor.comap i (X.div g) =
      U.div (.ofMul (Units.map i.functionFieldIso.commRingCatIsoToRingEquiv.toMonoidHom
        g.toMul)) := by
  ext P
  rw [comap_apply, div_apply, div_apply]
  exact (ord_functionFieldIso i P.1 _).symm

end OpenImmersion

end AlgebraicGeometry.Scheme
