/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Modules.ExteriorPower
public import WeilConjectures.RingTheory.KoszulRegularSequence
public import WeilConjectures.AlgebraicGeometry.TensorPullback
public import WeilConjectures.AlgebraicGeometry.DerivedCategory
public import WeilConjectures.Algebra.Homology.DerivedInternalHom
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module

import WeilConjectures.AlgebraicGeometry.KoszulSelfExtYonedaSurjection
import WeilConjectures.AlgebraicGeometry.KoszulSelfExtStalkBases
import Mathlib.RingTheory.FiniteType

/-! # Self-coefficient Koszul Ext and exterior powers

Source: Stacks Project, Tag 0BQZ, lemma-regular-immersion-ext. -/

@[expose] public section

set_option autoImplicit false

universe u w

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- Self-coefficient Ext on the Koszul-regular locus is the full exterior algebra
of the conormal dual, in every nonnegative degree, without a rank hypothesis.

Source: Stacks Project, Tags 0BQW and 0BQY, as used in the first paragraph of
Tag 0BQZ, lemma-regular-immersion-ext.
(blueprint: lem-sc-koszul-self-ext-exterior).

Proof: On an affine chart put A = O_Y(U), I = ker(i)(U), and B = A/I, and resolve
B by the augmented finite free Koszul complex of the supplied regular sequence.
After Hom into B all differentials vanish. The conormal basis identifies the
degree-one contractions with Hom_B(I/I^2,B); ordered products of contractions
identify degree n with its nth exterior power. The quotient action is the
ordinary B-action. Sheafification is exact, and the finite free Hom comparison
and restriction of derived internal Hom identify this with the self-coefficient
Ext sheaf. Taking tensor pullback after cohomology leaves these B-modules
unchanged. The affine conormal frame and the finite free internal Hom formulas
identify the target with the specified exterior sheaf. The contraction product
is intrinsic: degree one is the boundary identification for
0 -> I/I² -> O_Y/I² -> i_* O_Z -> 0, and higher degrees are its alternating Yoneda
products. A change of regular generators transforms degree one by the dual
conormal matrix and degree n by its exterior power, so the comparisons agree.
Localization preserves the same formulas. On arbitrary chart intersections
refine by affine standard opens, then glue the comparisons and their inverses
by the sheaf condition on V. No affine-intersection or quasi-separatedness
assumption is used. A common K-injective Hom complex compares derived universes.
The argument includes n greater than the local sequence length (both objects
vanish), n = 0 (the empty product gives the unit), and empty V. -/
theorem koszulRegularImmersion_self_ext_exterior
    {Z Y : Scheme.{u}} (i : Z ⟶ Y)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [IsClosedImmersion i] (V : Z.Opens) (n : ℕ)
    (hregular : ∀ z : Z, z ∈ V → ∃ U : Y.affineOpens, i z ∈ U.1 ∧
      ∃ (m : ℕ) (f : Fin m → Γ(Y, U.1)),
        Ideal.span (Set.range f) = i.ker.ideal U ∧
          RingTheory.Sequence.IsKoszulRegular f) :
    let B := (Scheme.Modules.pushforward i).obj (SheafOfModules.unit Z.ringCatSheaf)
    let S := DerivedCategory.singleFunctor
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0
    let H := derivedInternalHom (Opens.grothendieckTopology Y) Y.toRingedSpace.sheaf
    let G := (DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) (n : ℤ)).obj
        (H.obj (op (S.obj B), S.obj B))
    Nonempty ((Scheme.Modules.restrictFunctor V.ι).obj
      ((Scheme.Modules.tensorPullback i).obj G) ≅
      Scheme.Modules.exteriorPower
        ((Scheme.Modules.restrictFunctor V.ι).obj
          (SheafOfModules.homObj (R := Z.sheaf)
            ((Scheme.Modules.tensorPullback i).obj i.ker.toModules)
            (SheafOfModules.unit Z.ringCatSheaf))) n) := by
  classical
  dsimp only
  obtain ⟨φ, hφ⟩ := koszulRegularImmersion_self_ext_yoneda_surjection i V n hregular
  have : IsIso φ := by
    apply Scheme.Modules.isIso_of_bijective_stalkLinearMap
    intro z
    obtain ⟨U, hzU, m, f, hf, hreg⟩ := hregular z.1 z.2
    obtain ⟨⟨bT⟩, ⟨bE⟩⟩ :=
      koszulRegularImmersion_self_ext_stalk_bases i V n z U hzU m f hf hreg
    let := Module.Finite.of_basis bT
    let e := bE.equiv bT (Equiv.refl _)
    exact OrzechProperty.bijective_of_surjective_of_injective
      e.toLinearMap (φ.stalkLinearMap z) e.injective (hφ z)
  exact ⟨(asIso φ).symm⟩

end AlgebraicGeometry
