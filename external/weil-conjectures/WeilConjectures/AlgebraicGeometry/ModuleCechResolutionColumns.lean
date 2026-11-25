/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.ModuleCechComparison
public import WeilConjectures.Topology.OpenModuleCohomology
import WeilConjectures.AlgebraicGeometry.ModuleCechResolutionColumnZero
import WeilConjectures.AlgebraicGeometry.ModuleCechResolutionColumnPositive

/-! # Acyclic intersections give quasi-isomorphisms on resolution columns

Source: Stacks Project, Cohomology, Tags 01EQ and 01ET.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.Modules

/-- The Cech cochain products of an injective resolution are augmented resolutions
when positive cohomology vanishes on all the intersections. No totalization or
quasi-coherence assumption occurs in this statement.
Source: Stacks Project, Tags 01EQ and 01ET.
(blueprint: lem-sc-module-cech-resolution-columns).

Proof: evaluate the prescribed injective resolution on each finite intersection.
Restriction preserves injectivity and exactness, so this computes cohomology on
that open. The assumed positive-degree vanishing gives exactness in positive
resolution degrees. Left exactness of sections identifies the degree-zero kernel
with sections of F, and its augmentation is the evaluated I.ι.f 0. Restriction
of scalars to the global section ring preserves the underlying exact sequence.
For a fixed Cech degree take the product over all tuples: kernels are computed
coordinatewise and products of surjections are surjective by choosing preimages.
Thus the augmented product column is quasi-isomorphic to its degree-zero section
module. The augmentation squares to zero because I.ι.f 0 does, functoriality of
the Cech functor preserves this equality, and the transposed column maps are
exactly the maps constructed by fromSingle₀Equiv. -/
theorem moduleCech_resolution_columns {X : Scheme.{u}} {ι : Type u}
    (U : ι → X.Opens) (F : X.Modules) (I : InjectiveResolution F)
    (hvan : ∀ n : ℕ, ∀ y : Fin (n + 1) → ι, ∀ p : ℕ, 0 < p →
      Subsingleton ((RingedSpace.openModuleCohomology X.toRingedSpace p
        (⨅ l, U (y l))).obj F)) :
    let A := (CategoryTheory.cechComplexFunctor U).obj F.presheafModuleCat
    let a : A ⟶ (moduleCechDouble U I).X 0 :=
      (CategoryTheory.cechComplexFunctor U).map
        ((PresheafOfModules.forgetToPresheafModuleCat (op ⊤) isTerminalTop.op).map
          (I.ι.f 0).val)
    ∀ ha : a ≫ (moduleCechDouble U I).d 0 1 = 0,
      ∀ n : ℕ, QuasiIso
        ((CochainComplex.fromSingle₀Equiv ((moduleCechDouble U I).flip.X n)
          (A.X n)).symm
          ⟨a.f n, by simpa using congrArg (fun f ↦ f.f n) ha⟩) := by
  dsimp
  intro ha n
  apply (quasiIso_iff _).2
  intro p
  cases p with
  | zero => exact moduleCech_resolution_column_zero U F I ha n
  | succ p =>
    apply (quasiIsoAt_iff_isIso_homologyMap _ _).2
    exact (HomologicalComplex.isZero_single_obj_homology
      (ComplexShape.up ℕ) 0 _ (p + 1) (by simp)).isIso
      (moduleCech_resolution_column_positive U F I n (p + 1) (Nat.zero_lt_succ p)
        (fun y ↦ hvan n y (p + 1) (Nat.zero_lt_succ p))) _

end AlgebraicGeometry.Scheme.Modules
