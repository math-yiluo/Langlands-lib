/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.PullbackStalkTensorComparison
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
import WeilConjectures.Algebra.Category.ModuleCat.TorSymmetry
import Mathlib.RingTheory.Flat.CategoryTheory

/-! # Flat morphisms give stalkwise Tor-independent squares
Source: Stacks Project, Tags 00M3 and 08IB.
(blueprint: lem-sc-flat-pullback-tor-independent).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
namespace AlgebraicGeometry

/-- Flatness of the left morphism makes every pair of stalks Tor independent.
Source: Stacks Project, Algebra, Tag 00M3, and perfect.tex, Tag 08IB.
(blueprint: lem-sc-flat-pullback-tor-independent).

Proof: the left stalk is flat over the base stalk by the stalk criterion for flat
morphisms. By symmetry of Tor, resolve the other stalk by projectives and tensor
with the flat left stalk. Tensoring preserves the exactness of the resolution
in positive degrees. Its positive homology is therefore zero. Transport through
Tor symmetry and the projective-resolution computation of Tor. This applies to
all pairs over the same base point; the right stalk's transported scalar action
requires no flatness assumption. For an empty scheme there are no such pairs. -/
theorem flat_pullback_torIndependent {X S T : Scheme.{u}}
    (f : X ⟶ S) (g : T ⟶ S) [Flat f] :
    PullbackStalkTensor.IsTorIndependent f g := by
  intro x t h
  let := (f.stalkMap x).hom.toAlgebra
  let := ((S.presheaf.stalkCongr (.of_eq h)).hom ≫ g.stalkMap t).hom.toAlgebra
  have : Module.Flat (S.presheaf.stalk (f x)) (X.presheaf.stalk x) :=
    Flat.stalkMap f x
  intro i hi
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_zero_of_lt hi)
  let A := ModuleCat.of (S.presheaf.stalk (f x)) (X.presheaf.stalk x)
  let B := ModuleCat.of (S.presheaf.stalk (f x)) (T.presheaf.stalk t)
  obtain ⟨e⟩ := nonempty_tor'_flip_iso (S.presheaf.stalk (f x)) (n + 1)
  let P := projectiveResolution B
  have hz : IsZero (((Tor' (ModuleCat (S.presheaf.stalk (f x))) (n + 1)).obj B).obj A) := by
    apply IsZero.of_iso _ (P.isoLeftDerivedObj (tensorRight A) (n + 1))
    erw [← HomologicalComplex.exactAt_iff_isZero_homology]
    rw [HomologicalComplex.exactAt_iff' _ (n + 2) (n + 1) n (by simp) (by simp)]
    exact Module.Flat.rTensor_shortComplex_exact A _ (P.exact_succ n)
  exact hz.of_iso ((e.app A).app B)

/-- Flatness of the right morphism makes every pair of stalks Tor independent.
Source: Stacks Project, Algebra, Tag 00M3, and perfect.tex, Tag 08IB. -/
theorem flat_right_pullback_torIndependent {X S T : Scheme.{u}}
    (f : X ⟶ S) (g : T ⟶ S) [Flat g] :
    PullbackStalkTensor.IsTorIndependent f g := by
  intro x t h
  let := (f.stalkMap x).hom.toAlgebra
  let := ((S.presheaf.stalkCongr (.of_eq h)).hom ≫ g.stalkMap t).hom.toAlgebra
  have hflat : ((S.presheaf.stalkCongr (.of_eq h)).hom ≫ g.stalkMap t).hom.Flat := by
    rw [CommRingCat.hom_comp]
    exact RingHom.Flat.comp
      (.of_bijective (ConcreteCategory.bijective_of_isIso _)) (Flat.stalkMap g t)
  have : Module.Flat (S.presheaf.stalk (f x)) (T.presheaf.stalk t) := hflat
  intro i hi
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_zero_of_lt hi)
  let A := ModuleCat.of (S.presheaf.stalk (f x)) (X.presheaf.stalk x)
  let B := ModuleCat.of (S.presheaf.stalk (f x)) (T.presheaf.stalk t)
  let P := projectiveResolution A
  apply IsZero.of_iso _ (P.isoLeftDerivedObj (tensorRight B) (n + 1))
  erw [← HomologicalComplex.exactAt_iff_isZero_homology]
  rw [HomologicalComplex.exactAt_iff' _ (n + 2) (n + 1) n (by simp) (by simp)]
  exact Module.Flat.rTensor_shortComplex_exact B _ (P.exact_succ n)

end AlgebraicGeometry
