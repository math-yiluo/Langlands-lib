/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.CategoryTheory.Monoidal.Tor
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Defs
import Mathlib.RingTheory.Flat.Tensor
import WeilConjectures.Algebra.Category.ModuleCat.TorSymmetry
import WeilConjectures.AlgebraicGeometry.TorLongExactFirstVariable

/-!
# Flatness characterized by first Tor with ideal quotients

Source: literature/stacks-project/algebra.tex, Algebra, Lemma Tag 00M5
(blueprint: lem-weil-pbc-flat-tor-ideal-criterion).
-/

@[expose] public section

universe u

open CategoryTheory
open CategoryTheory.Limits

namespace CategoryTheory

/--
Source: literature/stacks-project/algebra.tex, Algebra, Lemma Tag 00M5
(blueprint: lem-weil-pbc-flat-tor-ideal-criterion).
The proof uses the first-variable Tor exact sequence, Tor symmetry, and the
finitely generated ideal criterion for flatness, as detailed in the node proof.
-/
theorem flat_iff_tor_one_quotient_ideal
    (R : Type u) [CommRing R]
    (C : Type u) [AddCommGroup C] [Module R C] :
    Module.Flat R C ↔
      ∀ I : Ideal R,
        IsZero (((Tor' (ModuleCat R) 1).obj (ModuleCat.of R C)).obj
          (ModuleCat.of R (R ⧸ I))) := by
  classical
  obtain ⟨symmetry⟩ := nonempty_tor'_flip_iso R 1
  have ideal_iff (I : Ideal R) :
      IsZero (((Tor' (ModuleCat R) 1).obj (ModuleCat.of R C)).obj
        (ModuleCat.of R (R ⧸ I))) ↔ Function.Injective (I.subtype.rTensor C) := by
    obtain ⟨δ, hδ, _⟩ := tor_long_exact_first_variable I.subtype I.mkQ
      Subtype.val_injective I.mkQ_surjective (LinearMap.exact_subtype_mkQ I)
    obtain ⟨hleft, hright, _, _⟩ := hδ C
    have hfree := isZero_Tor'_succ_of_projective (ModuleCat R)
      (ModuleCat.of R R) (ModuleCat.of R C) 0
    have : Subsingleton (((Tor' (ModuleCat R) 1).obj (ModuleCat.of R R)).obj
        (ModuleCat.of R C)) := ModuleCat.subsingleton_of_isZero hfree
    have hinj : Function.Injective (δ C).hom := by
      apply (injective_iff_map_eq_zero _).mpr
      intro x hx
      obtain ⟨y, hy⟩ := (hleft x).mp hx
      simpa only [Subsingleton.elim y 0, map_zero] using hy.symm
    let e := (symmetry.app (ModuleCat.of R C)).app (ModuleCat.of R (R ⧸ I))
    constructor
    · intro hz
      have hz' := hz.of_iso e.symm
      have : Subsingleton (((Tor' (ModuleCat R) 1).obj
          (ModuleCat.of R (R ⧸ I))).obj (ModuleCat.of R C)) :=
        ModuleCat.subsingleton_of_isZero hz'
      apply (injective_iff_map_eq_zero _).mpr
      intro x hx
      obtain ⟨y, hy⟩ := (hright x).mp hx
      simpa only [Subsingleton.elim y 0, map_zero] using hy.symm
    · intro hi
      have hz' : IsZero (((Tor' (ModuleCat R) 1).obj
          (ModuleCat.of R (R ⧸ I))).obj (ModuleCat.of R C)) := by
        apply ModuleCat.isZero_iff_subsingleton.mpr
        refine ⟨fun x y ↦ ?_⟩
        have hzero (z) : (δ C).hom z = 0 := by
          apply hi
          simpa only [map_zero] using hright.apply_apply_eq_zero z
        exact hinj ((hzero x).trans (hzero y).symm)
      exact hz'.of_iso e
  constructor
  · intro hflat I
    have : Module.Flat R C := hflat
    exact (ideal_iff I).mpr
      (Module.Flat.rTensor_preserves_injective_linearMap I.subtype Subtype.val_injective)
  · intro htor
    apply Module.Flat.iff_rTensor_injective.mpr
    intro I _
    exact (ideal_iff I).mp (htor I)

end CategoryTheory
