/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Curve.Brauer
public import WeilConjectures.AlgebraicGeometry.GlobalSectionsBijective
public import WeilConjectures.AlgebraicGeometry.Sites.Kummer
public import WeilConjectures.AlgebraicGeometry.Sites.RootsOfUnity
public import WeilConjectures.Mathlib.RingTheory.Artinian.Ring
public import WeilConjectures.Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed

/-!
# The cohomology of `μₙ` on a curve

For a curve `C` over an algebraically closed field `k` and `n` prime to the characteristic, the
Kummer sequence `0 → μₙ → 𝔾ₘ → 𝔾ₘ → 0` computes the cohomology of `μₙ` in low degrees:
`H⁰(C, μₙ) = ℤ/n` for connected `C`, `0 → 𝒪(C)ˣ/n → H¹(C, μₙ) → Pic(C)[n] → 0`, and
`H²(C, μₙ) ≅ Pic(C)/n` as the Brauer group of `C` vanishes. The `H¹` and `H²` sequences are
`AlgebraicGeometry.Scheme.exists_exact_sheafH_rootsOfUnitySheaf_one` and
`AlgebraicGeometry.Scheme.exists_exact_sheafH_rootsOfUnitySheaf_two`, which hold for every
scheme on which `n` is invertible.

## Main statements

- `AlgebraicGeometry.nonempty_addEquiv_sheafH_rootsOfUnitySheaf_one_of_isProper`:
  `H¹(C, μₙ) ≅ Pic(C)[n]` for `C` proper over `k`.
- `AlgebraicGeometry.IsCurve.sheafH_rootsOfUnitySheaf_of_subsingleton`: the cohomology of `μₙ`
  in degrees `0`, `1`, `2` for a curve with vanishing Brauer group.
- `AlgebraicGeometry.IsCurve.nonempty_addEquiv_sheafH_rootsOfUnitySheaf_two_of_smooth`:
  `H²(C, μₙ) ≅ Pic(C)/n·Pic(C)` for smooth `C`.
- `AlgebraicGeometry.IsCurve.nonempty_addEquiv_sheafH_rootsOfUnitySheaf_two`:
  `H²(C, μₙ) ≅ Pic(C)/n·Pic(C)` for every curve, using that the Brauer group of every curve
  vanishes.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

variable {k : Type u} [Field k] {C : Scheme.{u}}

/-- **`H¹(C, μₙ) = Pic(C)[n]` for proper `C`.** Let `C` be a proper scheme over an algebraically
closed field `k` and let `n ≥ 1` be prime to `char k`. Then `H¹(C, μₙ) ≅ H¹(C, 𝔾ₘ)[n]`.

The ring `𝒪(C)` is a finite `k`-algebra
(`AlgebraicGeometry.Scheme.finite_globalSectionsRingHom_of_isProper`), so its units are `n`-th
powers (`IsAlgClosed.exists_pow_eq_of_finite`) and the first term `𝒪(C)ˣ/n` of the short exact
sequence of
`AlgebraicGeometry.Scheme.exists_exact_sheafH_rootsOfUnitySheaf_one` vanishes.
(blueprint: `proposition-smooth-proper-curves-torsion-prime--2`) -/
theorem nonempty_addEquiv_sheafH_rootsOfUnitySheaf_one_of_isProper [IsAlgClosed k]
    (f : C ⟶ Spec (.of k)) [IsProper f] (n : ℕ) (hn : (n : k) ≠ 0) :
    Nonempty (Sheaf.H (C.rootsOfUnitySheaf n) 1 ≃+
      AddSubgroup.torsionBy C.CohomologicalPicardGroup n) := by
  have hn' : IsUnit (n : Γ(C, ⊤)) := by
    simpa using hn.isUnit.map ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop).hom
  let : C.Over (Spec (.of k)) := ⟨f⟩
  have : IsProper (C ↘ Spec (.of k)) := ‹IsProper f›
  let := (Scheme.globalSectionsRingHom k (X := C)).toAlgebra
  have : Module.Finite k Γ(C, ⊤) := Scheme.finite_globalSectionsRingHom_of_isProper
  exact C.nonempty_addEquiv_sheafH_rootsOfUnitySheaf_one n hn'
    (IsAlgClosed.exists_pow_eq_of_finite hn)

namespace IsCurve

/-- **Consequences of the Kummer sequence.** Let `C` be a curve over an algebraically closed
field `k` (not necessarily connected, reduced or smooth), let `n` be prime to `char k`, and
assume `H²(C, 𝔾ₘ) = 0`. Then:

* there is a short exact sequence `0 → 𝒪(C)ˣ/𝒪(C)ˣⁿ → H¹(C, μₙ) → H¹(C, 𝔾ₘ)[n] → 0`, where
  `H¹(C, 𝔾ₘ) = Pic(C)` (`AlgebraicGeometry.Scheme.nonempty_equiv_cohomologicalPicardGroup`);
* `H²(C, μₙ) ≅ H¹(C, 𝔾ₘ)/n`, the cokernel of multiplication by `n`;
* if `C` is connected, `H⁰(C, μₙ) ≅ ℤ/n`;
* if every unit of `𝒪(C)` is an `n`-th power, `H¹(C, μₙ) ≅ H¹(C, 𝔾ₘ)[n]`. This holds when `C`
  is proper, see `AlgebraicGeometry.nonempty_addEquiv_sheafH_rootsOfUnitySheaf_one_of_isProper`.

All four come from the long exact cohomology sequence of the Kummer sequence. In degree zero a
primitive `n`-th root of unity of `k` (`IsSepClosed.exists_isPrimitiveRoot`) identifies `μₙ` with
`ℤ/n` (`AlgebraicGeometry.Scheme.constantZModIsoRootsOfUnitySheaf`), whose global sections on a
connected scheme are `ℤ/n`.
(blueprint: `proposition-smooth-proper-curves-torsion-prime`) -/
theorem sheafH_rootsOfUnitySheaf_of_subsingleton [IsAlgClosed k] (f : C ⟶ Spec (.of k))
    [IsCurve f] (n : ℕ) (hn : (n : k) ≠ 0) (hBr : Subsingleton C.CohomologicalBrauerGroup) :
    (∃ (α : Additive Γ(C, ⊤)ˣ →+ Sheaf.H (C.rootsOfUnitySheaf n) 1)
      (β : Sheaf.H (C.rootsOfUnitySheaf n) 1 →+ C.CohomologicalPicardGroup),
      α.ker = (zsmulAddGroupHom (α := Additive Γ(C, ⊤)ˣ) (n : ℤ)).range ∧
        Function.Exact α β ∧ β.range = AddSubgroup.torsionBy C.CohomologicalPicardGroup n) ∧
    Nonempty (Sheaf.H (C.rootsOfUnitySheaf n) 2 ≃+
      C.CohomologicalPicardGroup ⧸
        (zsmulAddGroupHom (α := C.CohomologicalPicardGroup) (n : ℤ)).range) ∧
    (ConnectedSpace C → Nonempty (Sheaf.H (C.rootsOfUnitySheaf n) 0 ≃+ ZMod n)) ∧
    ((∀ u : Γ(C, ⊤)ˣ, ∃ v : Γ(C, ⊤)ˣ, v ^ n = u) →
      Nonempty (Sheaf.H (C.rootsOfUnitySheaf n) 1 ≃+
        AddSubgroup.torsionBy C.CohomologicalPicardGroup n)) := by
  have hn' : IsUnit (n : Γ(C, ⊤)) := by
    simpa using hn.isUnit.map ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop).hom
  refine ⟨C.exists_exact_sheafH_rootsOfUnitySheaf_one n hn', ?_, fun _ ↦ ?_,
    C.nonempty_addEquiv_sheafH_rootsOfUnitySheaf_one n hn'⟩
  · obtain ⟨α, β, hα, hαβ, -⟩ := C.exists_exact_sheafH_rootsOfUnitySheaf_two n hn'
    rw [← hα]
    exact ⟨(QuotientAddGroup.quotientKerEquivOfSurjective α
      fun y ↦ (hαβ y).1 (Subsingleton.elim _ _)).symm⟩
  · have : NeZero (n : k) := ⟨hn⟩
    have : NeZero n := .of_neZero_natCast k
    obtain ⟨-, -, ζ, hζ, -⟩ := IsSepClosed.exists_isPrimitiveRoot.{u, u} k n
    obtain ⟨e⟩ := Scheme.nonempty_addEquiv_sheafH_zero_constantZMod C n
    exact ⟨((Sheaf.functorH _ 0).mapIso
      (C.constantZModIsoRootsOfUnitySheaf n f hζ)).addCommGroupIsoToAddEquiv.symm.trans e⟩

/-- **`H²` via the Kummer sequence, smooth case.** For a smooth curve `C` over an algebraically
closed field `k` and every `n ≥ 1` prime to `char k`,

`H²(C, μₙ) ≅ Pic(C)/n·Pic(C)`.

In the long exact sequence of the Kummer sequence
(`AlgebraicGeometry.Scheme.exists_exact_sheafH_rootsOfUnitySheaf_two`) the last term is the
Brauer group `H²(C, 𝔾ₘ)`, which vanishes for smooth curves
(`AlgebraicGeometry.IsCurve.subsingleton_cohomologicalBrauerGroup_of_smooth`, blueprint
`lemma-cohomology-multiplicative-group`),
so `H²(C, μₙ)` is the cokernel of multiplication by `n` on `Pic(C) = H¹(C, 𝔾ₘ)`. The blueprint
states this for smooth proper curves; properness is not needed.
(blueprint: `lem-sc-second-kummer-divisors`) -/
theorem nonempty_addEquiv_sheafH_rootsOfUnitySheaf_two_of_smooth [IsAlgClosed k]
    (f : C ⟶ Spec (.of k)) [IsCurve f] [Smooth f] (n : ℕ) (hn : (n : k) ≠ 0) :
    Nonempty (Sheaf.H (C.rootsOfUnitySheaf n) 2 ≃+
      C.CohomologicalPicardGroup ⧸
        (zsmulAddGroupHom (α := C.CohomologicalPicardGroup) (n : ℤ)).range) := by
  have hn' : IsUnit (n : Γ(C, ⊤)) := by
    simpa using hn.isUnit.map ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop).hom
  obtain ⟨α, β, hα, hαβ, -⟩ := C.exists_exact_sheafH_rootsOfUnitySheaf_two n hn'
  have := subsingleton_cohomologicalBrauerGroup_of_smooth f
  rw [← hα]
  exact ⟨(QuotientAddGroup.quotientKerEquivOfSurjective α
    fun y ↦ (hαβ y).1 (Subsingleton.elim _ _)).symm⟩

/-- **`H²` via the Kummer sequence.** For a curve `C` over an algebraically closed field `k`
(not necessarily smooth) and every `n ≥ 1` prime to `char k`,

`H²(C, μₙ) ≅ Pic(C)/n·Pic(C)`.

This is the remark of blueprint `lem-sc-second-kummer-divisors` that the identity holds for every
curve, since the Brauer group of every curve vanishes
(`AlgebraicGeometry.IsCurve.subsingleton_cohomologicalBrauerGroup`, blueprint
`lemma-cohomology-multiplicative-group--6`); for smooth curves see
`AlgebraicGeometry.IsCurve.nonempty_addEquiv_sheafH_rootsOfUnitySheaf_two_of_smooth`.
(blueprint: `lem-sc-second-kummer-divisors`) -/
theorem nonempty_addEquiv_sheafH_rootsOfUnitySheaf_two [IsAlgClosed k] (f : C ⟶ Spec (.of k))
    [IsCurve f] (n : ℕ) (hn : (n : k) ≠ 0) :
    Nonempty (Sheaf.H (C.rootsOfUnitySheaf n) 2 ≃+
      C.CohomologicalPicardGroup ⧸
        (zsmulAddGroupHom (α := C.CohomologicalPicardGroup) (n : ℤ)).range) := by
  have hn' : IsUnit (n : Γ(C, ⊤)) := by
    simpa using hn.isUnit.map ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop).hom
  obtain ⟨α, β, hα, hαβ, -⟩ := C.exists_exact_sheafH_rootsOfUnitySheaf_two n hn'
  have := subsingleton_cohomologicalBrauerGroup f
  rw [← hα]
  exact ⟨(QuotientAddGroup.quotientKerEquivOfSurjective α
    fun y ↦ (hαβ y).1 (Subsingleton.elim _ _)).symm⟩

end IsCurve

end AlgebraicGeometry
