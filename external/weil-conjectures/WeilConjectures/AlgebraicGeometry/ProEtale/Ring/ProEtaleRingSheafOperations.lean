/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
public import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
public import Mathlib.CategoryTheory.Sites.Equivalence
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.Defs
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.Sites.Sheafification
public import WeilConjectures.CategoryTheory.Adjunction.LiftsGroupRingObjects
public import Mathlib.CategoryTheory.Monoidal.CommGrp_
public import Mathlib.CategoryTheory.Monoidal.Ring
public import Mathlib.CategoryTheory.Adjunction.Limits
public import WeilConjectures.CategoryTheory.Adjunction.LiftedCommRingBranch
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Iso
public import Mathlib.Algebra.Homology.ExactSequence
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact

/-!
# Operations on module objects over arbitrary pro-etale ring sheaves

These are the existing transparent operations, factored out for use by the localization
and base-change arguments.

## References

* Stacks, Tags 03D2 and 09A5
* Stacks, Tag 03D3 and Pro-etale Cohomology, section 09A5
* Stacks, Tags 03DI, 03DJ and 09AE
* Stacks, Tags 03CB and 03CC
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

/-- Module inverse image, with inverse-image coefficients and the transported action. -/
abbrev ringSheafInverseImage {T X : Scheme.{u}} (f : T ⟶ X)
    (B : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) [MonObj B] :=
  (upperStar Ab.{u + 1} f).mapMod B

/-- Module direct image, with scalars restricted through the canonical ring unit. -/
abbrev ringSheafDirectImage {T X : Scheme.{u}} (f : T ⟶ X)
    (B : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) [MonObj B] :=
  (lowerStar Ab.{u + 1} f).mapMod ((upperStar Ab.{u + 1} f).obj B) ⋙
    Mod.comap ((upperStarLowerStarAdjunction Ab.{u + 1} f).unitAlgHom B)

/-- The actual inverse-image/direct-image module adjunction. -/
abbrev ringSheafAdjunction {T X : Scheme.{u}} (f : T ⟶ X)
    (B : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) [MonObj B] :
    ringSheafInverseImage f B ⊣ ringSheafDirectImage f B :=
  (upperStarLowerStarAdjunction Ab.{u + 1} f).mapModAdjunction B

/-- Extension by zero with its coefficient action supplied by the existing projection
formula linearization. Its carrier is the sheafification of extension by zero of the
underlying abelian presheaf, and its action is the sheafified original action. -/
abbrev ringSheafOpenExtension {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (B : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) [MonObj B] :=
  (openImmersionLowerShriekUpperStarAdjunction Ab.{u + 1} j).mapModLeft B

/-- The extension-by-zero adjunction with its specified underlying abelian unit and counit. -/
abbrev ringSheafOpenAdjunction {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (B : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) [MonObj B] :
    ringSheafOpenExtension j B ⊣ ringSheafInverseImage j B :=
  (openImmersionLowerShriekUpperStarAdjunction Ab.{u + 1} j).mapModLeftAdjunction

/-- The fixed inverse-image composition comparison on a pullback square. -/
def ringSheafSquareComparison {X' T X : Scheme.{u}} (g : X' ⟶ X) (f : T ⟶ X) :
    upperStar Ab.{u + 1} g ⋙ upperStar Ab.{u + 1} (pullback.fst g f) ≅
      upperStar Ab.{u + 1} f ⋙ upperStar Ab.{u + 1} (pullback.snd g f) :=
  Classical.choose (show ∃ e :
      upperStar Ab.{u + 1} g ⋙ upperStar Ab.{u + 1} (pullback.fst g f) ≅
        upperStar Ab.{u + 1} f ⋙ upperStar Ab.{u + 1} (pullback.snd g f),
      e = upperStarCompIso Ab.{u + 1} (pullback.condition (f := g) (g := f)) from
    ⟨upperStarCompIso Ab.{u + 1} (pullback.condition (f := g) (g := f)), rfl⟩)

/-- The square comparison is the specified inverse-image compositor.

The equality in the choice predicate uniquely determines the comparison. Keeping that
predicate behind a definition boundary prevents kernel conversion from expanding the
chosen sheafification left adjoints in every component equation. -/
theorem ringSheafSquareComparison_eq {X' T X : Scheme.{u}}
    (g : X' ⟶ X) (f : T ⟶ X) :
    ringSheafSquareComparison g f =
      upperStarCompIso Ab.{u + 1} (pullback.condition (f := g) (g := f)) := by
  unfold ringSheafSquareComparison
  exact Classical.choose_spec (show ∃ e :
      upperStar Ab.{u + 1} g ⋙ upperStar Ab.{u + 1} (pullback.fst g f) ≅
        upperStar Ab.{u + 1} f ⋙ upperStar Ab.{u + 1} (pullback.snd g f),
      e = upperStarCompIso Ab.{u + 1} (pullback.condition (f := g) (g := f)) from
    ⟨_, rfl⟩)

/-- The canonical coefficient identification, with the two successive inverse-image
ring structures made explicit, rather than the structure on a composite functor. -/
def ringSheafSquareCoefficient {X' T X : Scheme.{u}} (g : X' ⟶ X) (f : T ⟶ X)
    (B : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) :
    (upperStar Ab.{u + 1} (pullback.fst g f)).obj ((upperStar Ab.{u + 1} g).obj B) ⟶
      (upperStar Ab.{u + 1} (pullback.snd g f)).obj ((upperStar Ab.{u + 1} f).obj B) :=
  (ringSheafSquareComparison g f).hom.app B

/-- Pullback along the fibre projection, with scalars identified by the fixed canonical
composition comparison. Multiplicativity of this comparison is concluded in the theorem. -/
abbrev ringSheafSquarePullback {X' T X : Scheme.{u}} (g : X' ⟶ X) (f : T ⟶ X)
    (B : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) [MonObj B]
    [IsMonHom (ringSheafSquareCoefficient g f B)] :
    Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) ((upperStar Ab.{u + 1} f).obj B) ⥤
      Mod (Sheaf (Scheme.ProEt.topology (pullback g f)) Ab.{u + 1})
        ((upperStar Ab.{u + 1} (pullback.fst g f)).obj
          ((upperStar Ab.{u + 1} g).obj B)) :=
  ringSheafInverseImage (pullback.snd g f) ((upperStar Ab.{u + 1} f).obj B) ⋙
    Mod.comap (ringSheafSquareCoefficient g f B)

end AlgebraicGeometry.ProEtale
