/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.RingTheory.Noetherian.Nilpotent
public import WeilConjectures.Mathlib.Algebra.CharP.Lemmas
public import Mathlib.AlgebraicGeometry.IdealSheaf.Basic

/-!
# The absolute Frobenius of a scheme in characteristic `p`

Let `X` be a scheme in which the prime `p` vanishes, i.e. `(p : Γ(X, ⊤)) = 0`. The
`p ^ n`-power absolute Frobenius `F : X ⟶ X` is the identity on the underlying space and
`s ↦ s ^ p ^ n` on every ring of sections. It is an affine morphism, since it is the identity on
the underlying space.

If moreover `X` is quasi-compact and locally noetherian, its nilradical is nilpotent, so for `n`
large `F` kills the nilradical (`exists_nilradical_le_ker_iterateFrobenius`) and hence factors
through the reduced subscheme `X_red ⟶ X`. This is the morphism used to descend ample families
from `X_red` to `X` (Stacks 0BD4).

## Main definitions

- `AlgebraicGeometry.Scheme.iterateFrobenius`: the `p ^ n`-power absolute Frobenius of `X`.

## Main statements

- `AlgebraicGeometry.Scheme.exists_nilradical_le_ker_iterateFrobenius`: on a quasi-compact
  locally noetherian scheme, some power of the Frobenius kills the nilradical.
-/

@[expose] public section

universe u

open CategoryTheory Opposite

namespace AlgebraicGeometry.Scheme

/-- If `p` vanishes in the global sections of `X`, it vanishes in every ring of sections. -/
lemma natCast_eq_zero_of_natCast_top_eq_zero {X : Scheme.{u}} {p : ℕ} (hX : (p : Γ(X, ⊤)) = 0)
    (U : X.Opens) : (p : Γ(X, U)) = 0 := by
  rw [← map_natCast (X.presheaf.map (homOfLE le_top).op).hom, hX, map_zero]

variable (X : Scheme.{u}) {p : ℕ} (hp : p.Prime) (hX : (p : Γ(X, ⊤)) = 0) (n : ℕ)

/-- The `p ^ n`-power absolute Frobenius of a scheme `X` in which the prime `p` vanishes: the
identity on the underlying space and `s ↦ s ^ p ^ n` on sections. -/
noncomputable def iterateFrobenius : X ⟶ X where
  base := 𝟙 _
  c :=
    { app U := CommRingCat.ofHom (iterateFrobeniusOfPrime Γ(X, U.unop) hp
        (natCast_eq_zero_of_natCast_top_eq_zero hX U.unop) n)
      naturality U V i := by
        ext x
        exact (map_pow (X.presheaf.map i).hom x (p ^ n)).symm }
  prop x := by
    refine ⟨fun y hy ↦ ?_⟩
    obtain ⟨U, hxU, s, rfl⟩ := X.presheaf.exists_germ_eq y
    rw [PresheafedSpace.stalkMap_germ_apply] at hy
    refine (isUnit_pow_iff (pow_ne_zero n hp.ne_zero)).1 ?_
    rw [← map_pow]
    exact hy

@[simp]
lemma iterateFrobenius_apply (x : X) : X.iterateFrobenius hp hX n x = x :=
  rfl

@[simp]
lemma preimage_iterateFrobenius (U : X.Opens) : X.iterateFrobenius hp hX n ⁻¹ᵁ U = U :=
  rfl

lemma iterateFrobenius_app_apply (U : X.Opens) (s : Γ(X, U)) :
    (X.iterateFrobenius hp hX n).app U s = s ^ p ^ n :=
  rfl

/-- The absolute Frobenius is affine: it is the identity on the underlying space. -/
instance : IsAffineHom (X.iterateFrobenius hp hX n) :=
  ⟨fun _ hU ↦ hU⟩

/-- On a quasi-compact locally noetherian scheme in which the prime `p` vanishes, some power
`p ^ n` of the absolute Frobenius kills the nilradical: the nilradical of each of finitely many
noetherian affine charts is nilpotent. -/
lemma exists_nilradical_le_ker_iterateFrobenius [IsLocallyNoetherian X] [CompactSpace X] :
    ∃ n, X.nilradical ≤ (X.iterateFrobenius hp hX n).ker := by
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun U : X.affineOpens ↦ (U : Set X))
    (fun U ↦ U.1.isOpen) fun x _ ↦ by
      obtain ⟨_, ⟨U, hU, rfl⟩, hx, -⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open
        (Set.mem_univ x) isOpen_univ
      exact Set.mem_iUnion.2 ⟨⟨U, hU⟩, hx⟩
  choose m hm using fun U : X.affineOpens ↦
    have := IsLocallyNoetherian.component_noetherian U
    IsNoetherianRing.isNilpotent_nilradical Γ(X, U)
  refine ⟨t.sup m, IdealSheafData.le_of_iSup_eq_top (fun U : t ↦ U.1) ?_ fun U x hx ↦ ?_⟩
  · refine eq_top_iff.2 fun x _ ↦ ?_
    obtain ⟨U, hU, hx⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ x))
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨U, hU⟩, hx⟩
  rw [Hom.ker_apply, RingHom.mem_ker, iterateFrobenius_app_apply]
  refine pow_eq_zero_of_le ((Finset.le_sup U.2).trans (Nat.lt_pow_self hp.one_lt).le) ?_
  have : x ^ m U ∈ _root_.nilradical Γ(X, U) ^ m U := Ideal.pow_mem_pow hx _
  rwa [hm, Submodule.zero_eq_bot, Ideal.mem_bot] at this

end AlgebraicGeometry.Scheme
