/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import WeilConjectures.AlgebraicGeometry.Curve
public import WeilConjectures.AlgebraicGeometry.Curve.CohomologicalDimension
public import WeilConjectures.AlgebraicGeometry.Curve.RiemannRoch

/-!
# The curve estimate

For a smooth proper connected curve `C` of genus `g` over an algebraically closed field `k`
and `n` prime to the characteristic, the cohomology of the constant sheaf `ℤ/n` on `C_ét` is

`H⁰ = ℤ/n`, `H¹ = (ℤ/n)^{2g}`, `H² = ℤ/n`, `H^q = 0` for `q ≥ 3`.

A smooth proper connected curve is recorded by the class `AlgebraicGeometry.IsConnectedCurve`
together with `Smooth` and `IsProper`. Dimension exactly one is needed in degree two: `Spec k`
is a smooth proper connected scheme of dimension zero with `H² = 0`. Degree zero holds for every
connected scheme (`AlgebraicGeometry.Scheme.nonempty_addEquiv_sheafH_zero_constantZMod`). The
vanishing for `q ≥ 3` is `AlgebraicGeometry.IsCurve.subsingleton_sheafH_of_three_le` applied to
`C.constantZMod n`.

After choosing a primitive `n`-th root of unity, `ℤ/n ≅ μₙ`, and the Kummer sequence identifies
`H¹(C, μₙ)` with `Pic(C)[n]` and `H²(C, μₙ)` with `Pic(C)/n`. The degree splits
`Pic(C) = ℤ × Pic⁰(C)`, and `Pic⁰(C)` is the group of `k`-points of the Jacobian of `C`, an
abelian variety of dimension `g`; its `n`-torsion is `(ℤ/n)^{2g}` and it is `n`-divisible.

## Main statements

- `AlgebraicGeometry.Scheme.nonempty_addEquiv_torsionBy_pic_and_quotient`:
  `Pic(C)[n] ≅ (ℤ/n)^{2g}` and `Pic(C)/n ≅ ℤ/n`.
- `AlgebraicGeometry.IsCurve.nonempty_addEquiv_sheafH_constantZMod_zero`:
  `H⁰(C, ℤ/n) ≅ ℤ/n`.
- `AlgebraicGeometry.IsCurve.nonempty_addEquiv_sheafH_constantZMod_one`:
  `H¹(C, ℤ/n) ≅ (ℤ/n)^{2g}`.
- `AlgebraicGeometry.IsCurve.nonempty_addEquiv_sheafH_constantZMod_two`:
  `H²(C, ℤ/n) ≅ ℤ/n`.
- `AlgebraicGeometry.IsConnectedCurve.sheafH_constantZMod_of_isProper`: all degrees at once.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

variable {k : Type u} [Field k] [IsAlgClosed k] {C : Scheme.{u}}

omit [IsAlgClosed k] in
/-- **The curve estimate in degree zero.** Let `C` be a smooth proper connected curve over a
field `k`, and let `n ≥ 1` be prime to `char k`. Then `H⁰(C_ét, ℤ/n) ≅ ℤ/n`; this only uses
that `C` is connected, so `k` need not be algebraically closed.
(blueprint: `proposition-smooth-proper-curves-torsion-prime`) -/
theorem IsCurve.nonempty_addEquiv_sheafH_constantZMod_zero (f : C ⟶ Spec (.of k))
    [IsConnectedCurve f] [Smooth f] [IsProper f] (n : ℕ) (_hn : (n : k) ≠ 0) :
    Nonempty (Sheaf.H (C.constantZMod n) 0 ≃+ ZMod n) :=
  have := IsConnectedCurve.connectedSpace (f := f)
  Scheme.nonempty_addEquiv_sheafH_zero_constantZMod C n

/-- A primitive `n`-th root of unity identifies `H^q(C, ℤ/n)` with `H^q(C, μₙ)`. -/
lemma Scheme.nonempty_addEquiv_sheafH_constantZMod_rootsOfUnitySheaf (f : C ⟶ Spec (.of k))
    (n : ℕ) (hn : (n : k) ≠ 0) (q : ℕ) :
    Nonempty (Sheaf.H (C.constantZMod n) q ≃+ Sheaf.H (C.rootsOfUnitySheaf n) q) := by
  have : NeZero (n : k) := ⟨hn⟩
  have : NeZero n := .of_neZero_natCast k
  obtain ⟨-, -, ζ, hζ, -⟩ := IsSepClosed.exists_isPrimitiveRoot.{u, u} k n
  exact ⟨((Sheaf.functorH _ q).mapIso
    (C.constantZModIsoRootsOfUnitySheaf n f hζ)).addCommGroupIsoToAddEquiv⟩

/-- **The curve estimate in degree one.** Let `C` be a smooth proper connected curve of genus
`g` over an algebraically closed field `k`, and let `n ≥ 1` be prime to `char k`. Then
`H¹(C_ét, ℤ/n) ≅ (ℤ/n)^{2g}`.

The genus is `f.genus = dim_k H⁰(C, Ω¹_{C/k})`, the definition of the blueprint
(`def-sc-curves`). For a smooth proper curve it agrees, by Serre duality, with the arithmetic genus
`AlgebraicGeometry.Scheme.arithmeticGenus = dim_k H¹(C, 𝒪_C)` of the Riemann–Roch block
(`AlgebraicGeometry.Scheme.genus_eq_arithmeticGenus`), which is the dimension of the Jacobian.

After choosing a primitive `n`-th root of unity, `ℤ/n ≅ μₙ`, and `H¹(C, μₙ) ≅ Pic(C)[n]`
(`AlgebraicGeometry.nonempty_addEquiv_sheafH_rootsOfUnitySheaf_one_of_isProper`), which is
`(ℤ/n)^{2g}` by `AlgebraicGeometry.Scheme.nonempty_addEquiv_torsionBy_pic_and_quotient`.
(blueprint: `proposition-smooth-proper-curves-torsion-prime`) -/
theorem IsCurve.nonempty_addEquiv_sheafH_constantZMod_one (f : C ⟶ Spec (.of k))
    [IsConnectedCurve f] [Smooth f] [IsProper f] (n : ℕ) (hn : (n : k) ≠ 0) :
    Nonempty (Sheaf.H (C.constantZMod n) 1 ≃+ (Fin (2 * f.genus) → ZMod n)) := by
  have := IsConnectedCurve.connectedSpace (f := f)
  let : C.Over (Spec (.of k)) := ⟨f⟩
  have : SmoothOfRelativeDimension 1 (C ↘ Spec (.of k)) :=
    IsConnectedCurve.smoothOfRelativeDimension_one f
  have : IsProper (C ↘ Spec (.of k)) := ‹IsProper f›
  obtain ⟨e₁⟩ := Scheme.nonempty_addEquiv_sheafH_constantZMod_rootsOfUnitySheaf f n hn 1
  obtain ⟨e₂⟩ := nonempty_addEquiv_sheafH_rootsOfUnitySheaf_one_of_isProper f n hn
  obtain ⟨ePic⟩ := C.nonempty_addEquiv_cohomologicalPicardGroup
  obtain ⟨⟨e₃⟩, -, -⟩ := Scheme.nonempty_addEquiv_torsionBy_pic_and_quotient (C := C) hn
  exact ⟨e₁.trans (e₂.trans ((AddSubgroup.torsionByCongr ePic.symm n).trans e₃))⟩

/-- **The curve estimate in degree two.** Let `C` be a smooth proper connected curve over an
algebraically closed field `k`, and let `n ≥ 1` be prime to `char k`. Then
`H²(C_ét, ℤ/n) ≅ ℤ/n`.

The isomorphism depends on the choice of a primitive `n`-th root of unity, that is, of an
isomorphism `μₙ ≅ ℤ/n` of étale sheaves, so it is only asserted to exist. A connected curve has
dimension exactly one (`AlgebraicGeometry.IsConnectedCurve.krullDim_eq_one`); without this
`Spec k` would be a smooth proper connected curve with `H² = 0`.

After choosing a primitive `n`-th root of unity, `ℤ/n ≅ μₙ`, and `H²(C, μₙ) ≅ Pic(C)/n`
(`AlgebraicGeometry.IsCurve.nonempty_addEquiv_sheafH_rootsOfUnitySheaf_two_of_smooth`), which is
`ℤ/n` by `AlgebraicGeometry.Scheme.nonempty_addEquiv_torsionBy_pic_and_quotient`.
(blueprint: `proposition-smooth-proper-curves-torsion-prime`) -/
theorem IsCurve.nonempty_addEquiv_sheafH_constantZMod_two (f : C ⟶ Spec (.of k))
    [IsConnectedCurve f] [Smooth f] [IsProper f] (n : ℕ) (hn : (n : k) ≠ 0) :
    Nonempty (Sheaf.H (C.constantZMod n) 2 ≃+ ZMod n) := by
  have := IsConnectedCurve.connectedSpace (f := f)
  let : C.Over (Spec (.of k)) := ⟨f⟩
  have : SmoothOfRelativeDimension 1 (C ↘ Spec (.of k)) :=
    IsConnectedCurve.smoothOfRelativeDimension_one f
  have : IsProper (C ↘ Spec (.of k)) := ‹IsProper f›
  obtain ⟨e₁⟩ := Scheme.nonempty_addEquiv_sheafH_constantZMod_rootsOfUnitySheaf f n hn 2
  obtain ⟨e₂⟩ := IsCurve.nonempty_addEquiv_sheafH_rootsOfUnitySheaf_two_of_smooth f n hn
  obtain ⟨ePic⟩ := C.nonempty_addEquiv_cohomologicalPicardGroup
  obtain ⟨-, ⟨e₃⟩, -⟩ := Scheme.nonempty_addEquiv_torsionBy_pic_and_quotient (C := C) hn
  exact ⟨e₁.trans (e₂.trans ((AddSubgroup.quotientRangeZsmulCongr ePic.symm n).trans e₃))⟩

/-- **Kummer computation on a proper curve.** Let `C` be a smooth proper connected curve of
genus `g` over an algebraically closed field `k` and let `n ≥ 1` be prime to `char k`. Then

`H⁰(C, ℤ/n) ≅ ℤ/n`, `H¹(C, ℤ/n) ≅ (ℤ/n)^{2g}`, `H²(C, ℤ/n) ≅ ℤ/n`, `H^q(C, ℤ/n) = 0` for
`q > 2`.

The proof is the one of the remark closing the curve estimates: degree zero is `μₙ(k) = ℤ/n`,
degree one is `Pic(C)[n] = J(C)[n]`, degree two is `Pic(C)/n = ℤ/n` via the Kummer sequence and
`H²(C, μₙ) ≅ Pic(C)/n` (blueprint `lem-sc-second-kummer-divisors`), and the vanishing above two is
the bound on the cohomological dimension (blueprint `theorem-cohomology-curves`).
(blueprint: `proposition-smooth-proper-curves-torsion-prime`,
`sk-the-final-theorem-the-curve-estimate--remark-1`,
`the-final-theorem-the-curve-estimate--remark-1`) -/
theorem IsConnectedCurve.sheafH_constantZMod_of_isProper (f : C ⟶ Spec (.of k))
    [IsConnectedCurve f] [Smooth f] [IsProper f] (n : ℕ) (hn : (n : k) ≠ 0) :
    Nonempty (Sheaf.H (C.constantZMod n) 0 ≃+ ZMod n) ∧
      Nonempty (Sheaf.H (C.constantZMod n) 1 ≃+ (Fin (2 * f.genus) → ZMod n)) ∧
      Nonempty (Sheaf.H (C.constantZMod n) 2 ≃+ ZMod n) ∧
      ∀ q, 2 < q → Subsingleton (Sheaf.H (C.constantZMod n) q) :=
  ⟨IsCurve.nonempty_addEquiv_sheafH_constantZMod_zero f n hn,
    IsCurve.nonempty_addEquiv_sheafH_constantZMod_one f n hn,
    IsCurve.nonempty_addEquiv_sheafH_constantZMod_two f n hn,
    fun q hq ↦ IsCurve.subsingleton_sheafH_of_three_le f (C.constantZMod n)
      (C.isTorsion_constantZMod (by rintro rfl; exact hn Nat.cast_zero)) q hq⟩

end AlgebraicGeometry
