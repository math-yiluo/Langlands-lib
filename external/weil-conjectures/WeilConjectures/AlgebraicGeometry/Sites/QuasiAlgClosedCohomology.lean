/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Sites.ArtinSchreier
public import WeilConjectures.AlgebraicGeometry.Sites.BrauerGroup
public import WeilConjectures.AlgebraicGeometry.Sites.Hilbert90
public import WeilConjectures.AlgebraicGeometry.Sites.RootsOfUnity
public import WeilConjectures.Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed

/-!
# `H²(Spec E, ℤ/ℓ)` vanishes for a quasi-algebraically closed field `E`

Let `E` be a quasi-algebraically closed (`C₁`) field and `ℓ` a prime. Then
`H²(Spec(E)_ét, ℤ/ℓ) = 0`, provided `E` contains a primitive `ℓ`-th root of unity whenever `ℓ`
is invertible in `E`.

* If `ℓ = char E`, this is the Artin–Schreier vanishing
  `AlgebraicGeometry.Scheme.subsingleton_sheafH_constantZMod_of_isAffine`.
* If `ℓ` is invertible in `E`, a primitive `ℓ`-th root of unity identifies `ℤ/ℓ` with `μ_ℓ`
  (`AlgebraicGeometry.Scheme.constantZModIsoRootsOfUnitySheaf`), and the Kummer sequence
  `0 → H¹(𝔾ₘ)/ℓ → H²(μ_ℓ) → H²(𝔾ₘ)[ℓ] → 0`
  (`AlgebraicGeometry.Scheme.exists_exact_sheafH_rootsOfUnitySheaf_two`) shows that `H²(μ_ℓ)`
  vanishes, as `H¹(Spec E, 𝔾ₘ) = 0` by Hilbert 90 and `H²(Spec E, 𝔾ₘ) = 0` since `E` is `C₁`.

## Main statements

- `AlgebraicGeometry.Scheme.subsingleton_sheafH_two_constantZMod_of_isQuasiAlgClosed`.
- `AlgebraicGeometry.Scheme.subsingleton_sheafH_two_constantZMod_of_isAlgClosed_subfield`: the
  same for a `C₁` field containing an algebraically closed field.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- **`H²(Spec E, ℤ/ℓ) = 0` for a `C₁` field `E`.** Let `E` be a quasi-algebraically closed
field and `ℓ` a prime such that `E` contains a primitive `ℓ`-th root of unity if `ℓ ≠ char E`.
Then `H²(Spec(E)_ét, ℤ/ℓ) = 0`. -/
theorem subsingleton_sheafH_two_constantZMod_of_isQuasiAlgClosed
    (E : Type u) [Field E] [IsQuasiAlgClosed E] (ℓ : ℕ) [Fact ℓ.Prime]
    (hζ : (ℓ : E) ≠ 0 → ∃ ζ : E, IsPrimitiveRoot ζ ℓ) :
    Subsingleton (Sheaf.H ((Spec (.of E)).constantZMod ℓ) 2) := by
  by_cases hℓ : (ℓ : E) = 0
  · refine (Spec (.of E)).subsingleton_sheafH_constantZMod_of_isAffine ℓ ?_ 2 le_rfl
    simpa using congrArg (ΓSpecIso (.of E)).inv.hom hℓ
  obtain ⟨ζ, hζ⟩ := hζ hℓ
  have : NeZero ℓ := ⟨(Fact.out : ℓ.Prime).ne_zero⟩
  have hn : IsUnit (ℓ : Γ(Spec (.of E), ⊤)) := by
    simpa using (Ne.isUnit hℓ).map (ΓSpecIso (.of E)).inv.hom
  obtain ⟨α, β, -, hαβ, -⟩ := (Spec (.of E)).exists_exact_sheafH_rootsOfUnitySheaf_two ℓ hn
  have := IsQuasiAlgClosed.subsingleton_cohomologicalBrauerGroup E
  have hμ : Subsingleton (Sheaf.H ((Spec (.of E)).rootsOfUnitySheaf ℓ) 2) := by
    refine ⟨fun x y ↦ ?_⟩
    obtain ⟨a, rfl⟩ := (hαβ x).1 (Subsingleton.elim _ _)
    obtain ⟨b, rfl⟩ := (hαβ y).1 (Subsingleton.elim _ _)
    rw [Subsingleton.elim a b]
  exact ((Sheaf.functorH _ 2).mapIso ((Spec (.of E)).constantZModIsoRootsOfUnitySheaf ℓ
    (𝟙 _) hζ)).addCommGroupIsoToAddEquiv.toEquiv.subsingleton_congr.2 hμ

/-- **`H²(Spec E, ℤ/ℓ) = 0` for a `C₁` field over an algebraically closed field.** Let `E` be a
quasi-algebraically closed field containing an algebraically closed field `k` and `ℓ` a prime.
Then `H²(Spec(E)_ét, ℤ/ℓ) = 0`. -/
theorem subsingleton_sheafH_two_constantZMod_of_isAlgClosed_subfield (k E : Type u) [Field k]
    [IsAlgClosed k] [Field E] [Algebra k E] [IsQuasiAlgClosed E] (ℓ : ℕ) [Fact ℓ.Prime] :
    Subsingleton (Sheaf.H ((Spec (.of E)).constantZMod ℓ) 2) := by
  refine subsingleton_sheafH_two_constantZMod_of_isQuasiAlgClosed E ℓ fun hℓ ↦ ?_
  have : NeZero (ℓ : k) := ⟨fun h ↦ hℓ (by rw [← map_natCast (algebraMap k E), h, map_zero])⟩
  obtain ⟨-, -, ζ, -, hζ⟩ := IsSepClosed.exists_isPrimitiveRoot k ℓ
  exact ⟨_, hζ E (algebraMap k E)⟩

end AlgebraicGeometry.Scheme
