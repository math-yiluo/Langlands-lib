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
public import WeilConjectures.Algebra.Homology.ModuleStalkFunctor
public import Mathlib.LinearAlgebra.Dimension.Finrank

import WeilConjectures.AlgebraicGeometry.KoszulExtCoefficientStalkIso
import WeilConjectures.AlgebraicGeometry.KoszulSelfExtExterior
import WeilConjectures.RingTheory.KoszulConormalBasis
import WeilConjectures.AlgebraicGeometry.AffineConormalFrame
import WeilConjectures.AlgebraicGeometry.Modules.FlatPullbackStalk

/-! # Constant-rank top scalar Koszul Ext

Source: Stacks Project, Tag 0BQZ. -/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- The top scalar Ext on a constant conormal-rank open is its dual determinant.

Source: Stacks Project, Tag 0BQZ, proof of lemma-regular-immersion-ext.
(blueprint: lem-sc-koszul-ext-constant-rank-top).

Proof: Fix z in V and choose an affine Koszul chart of length m. The conormal
basis and affine conormal frame compute its stalk finrank as m; hVrank gives
m=n. The structure-sheaf coefficient map induces a morphism from scalar Ext to
self-coefficient Ext. Restrict its tensor pullback to V. The local coefficient
comparison is bijective on each stalk by the length-n Koszul calculation, hence
this restricted morphism is an isomorphism. Self-coefficient Ext is canonically
the exterior power of the conormal dual on the regular locus, in every degree.
Compose these isomorphisms. This argument uses no rank or regularity away from V;
empty V is covered by the vacuous stalk criterion, and n=0 by the empty Koszul
coefficient calculation. -/
theorem koszulRegularImmersion_ext_constantRank_top
    {Z Y : Scheme.{u}} (i : Z ⟶ Y) [IsClosedImmersion i]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    (V : Z.Opens) (n : ℕ)
    (hregular : ∀ z : Z, z ∈ V → ∃ U : Y.affineOpens, i z ∈ U.1 ∧
      ∃ (m : ℕ) (f : Fin m → Γ(Y, U.1)),
        Ideal.span (Set.range f) = i.ker.ideal U ∧
          RingTheory.Sequence.IsKoszulRegular f)
    (hVrank : ∀ z : Z, z ∈ V →
      Module.finrank (Z.presheaf.stalk z)
        ((RingedSpace.moduleStalkFunctor Z.toRingedSpace z).obj
          ((Scheme.Modules.tensorPullback i).obj i.ker.toModules)) = n) :
    let F : Y.Modules := (DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) (n : ℤ)).obj
        ((derivedInternalHom (Opens.grothendieckTopology Y) Y.toRingedSpace.sheaf).obj
          (op ((DerivedCategory.singleFunctor
            (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0).obj
              ((Scheme.Modules.pushforward i).obj (SheafOfModules.unit Z.ringCatSheaf))),
            (DerivedCategory.singleFunctor
              (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0).obj
                (SheafOfModules.unit Y.ringCatSheaf)))
    Nonempty ((Scheme.Modules.restrictFunctor V.ι).obj
      ((Scheme.Modules.tensorPullback i).obj F) ≅
      Scheme.Modules.exteriorPower
        ((Scheme.Modules.restrictFunctor V.ι).obj
          (SheafOfModules.homObj (R := Z.sheaf)
            ((Scheme.Modules.tensorPullback i).obj i.ker.toModules)
            (SheafOfModules.unit Z.ringCatSheaf))) n) := by
  classical
  dsimp only
  let φ := (Scheme.Modules.restrictFunctor V.ι).map
    (koszulScalarExtCoefficientMap i n)
  have : IsIso φ := by
    apply Scheme.Modules.isIso_of_bijective_stalkLinearMap
    intro z
    obtain ⟨U, hzU, m, f, hf, hreg⟩ := hregular z.1 z.2
    let b := (ExteriorAlgebra.exists_koszul_conormal_basis
      Γ(Y, U.1) (i.ker.ideal U) m f hreg hf).choose
    have hdim := (affine_conormal_frame i U m b).2 z.1 hzU
    have hmn : m = n := hdim.symm.trans (hVrank z.1 z.2)
    cases hmn
    exact koszulRegularImmersion_ext_coefficient_stalk_iso i V n z U hzU f hf hreg
  exact (koszulRegularImmersion_self_ext_exterior i V n hregular).map
    (fun e ↦ asIso φ ≪≫ e)


end AlgebraicGeometry
