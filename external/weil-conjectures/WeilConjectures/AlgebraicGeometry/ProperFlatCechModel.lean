/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Sections
import WeilConjectures.AlgebraicGeometry.DescentFirstProperFlatCechModel

/-! # Bounded flat models for proper relatively flat cohomology

The geometric, pseudo-coherent part of the construction of Mumford's complex.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme.Modules

/-- A proper finitely presented morphism and a finitely presented relatively flat module
admit, near each base point, a bounded nonnegative flat complex `C` computing every
base-changed higher direct image. It has a bounded-above finite-free resolution `Q`.
Unlike the desired finite-free model, `C` need not have finite terms, and `Q` can have
infinitely many nonzero negative terms.

Source: the coherence unit, part (a), and Stacks Project, Tags 0A1H, 0B91, 064U.
Proof:
1. Choose an affine neighbourhood of the base point and a finite affine cover of its
   inverse image. Properness supplies separatedness, so all finite intersections are
   affine. The alternating section complex of this cover is bounded in degrees `[0,d]`.
   Its terms are flat over the affine base because the module is relatively flat.
   Sheafify this complex to obtain `C`; flatness gives the stated flatness over the identity.
2. Affine quasi-coherent acyclicity and the Cech comparison identify its cohomology,
   after any base change, with the higher direct images of the pulled-back module.
   For a nonaffine new base these identifications glue from affine opens. An arbitrary
   cartesian square is transported from the standard fibre product by its unique isomorphism.
3. Descend the finitely presented proper morphism and the finitely presented module to
   a Noetherian affine stage; relative flatness holds after increasing the stage. There
   the bounded flat section complex has finite cohomology by proper coherence, and is
   pseudo-coherent. Derived base change pulls pseudo-coherence back to the original base
   (the Noetherian approximation argument of 0A1H). The affine pseudo-coherent resolution
   of 064U gives `Q -> C`, with finite free terms and upper bound `d`, since `C` vanishes
   above `d`. Shrink the initial affine neighbourhood if necessary for this resolution.

(blueprint: lem-pc-proper-flat-cech-model). -/
theorem exists_proper_flat_cech_model {X T : Scheme.{u}} (f : X ⟶ T) (F : X.Modules)
    [IsProper f] [LocallyOfFinitePresentation f] [QuasiCompact f]
    [HasInjectiveResolutions X.Modules] [F.IsFinitePresentation]
    (hF : F.IsFlatOver f) (t : T) :
    ∃ (U : T.Opens) (C Q : CochainComplex U.toScheme.Modules ℤ) (d : ℕ),
      t ∈ U ∧ C.IsStrictlyGE 0 ∧ C.IsStrictlyLE d ∧
      (∀ n : ℤ, (C.X n).IsFlatOver (𝟙 U.toScheme)) ∧ Q.IsStrictlyLE d ∧
      (∀ n : ℤ, ∃ r : ℕ,
        Nonempty (Q.X n ≅ SheafOfModules.free
          (R := U.toScheme.ringCatSheaf) (ULift.{u} (Fin r)))) ∧
      (∃ e : Q ⟶ C, QuasiIso e) ∧
      ∀ {T' X' : Scheme.{u}} (g : T' ⟶ U.toScheme) (g' : X' ⟶ X) (f' : X' ⟶ T')
        [HasInjectiveResolutions X'.Modules], IsPullback g' f' f (g ≫ U.ι) → ∀ q : ℕ,
        Nonempty ((((Modules.pullback g).mapHomologicalComplex _).obj C).homology q ≅
          (higherDirectImage f' q).obj ((Modules.pullback g').obj F))  := by
  exact descent_first_exists_proper_flat_cech_model f F hF t

end AlgebraicGeometry.Scheme.Modules
