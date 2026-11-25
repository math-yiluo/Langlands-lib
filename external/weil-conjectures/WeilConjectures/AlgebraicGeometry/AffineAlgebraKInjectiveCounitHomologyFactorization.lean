/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DirectImageAlgebraDerivedCategory
public import WeilConjectures.AlgebraicGeometry.RingedSpaceDerivedDirectImage
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
public import WeilConjectures.FromJoel.Algebra.Homology.PreservesQuasiIso
import WeilConjectures.AlgebraicGeometry.AffineAlgebraCounitHomologyComparisonIsIso
import WeilConjectures.AlgebraicGeometry.AffineAlgebraKInjectiveCounitCompatibility

/-! # The affine algebra counit on K-injective cohomology

Source: Stacks Project, Tag 0AVW, proof of perfect-lemma-affine-morphism-equivalence.
(blueprint: lem-sc-affine-algebra-kinjective-counit-homology-factorization).
-/

@[expose] public section

universe v

open CategoryTheory

namespace AlgebraicGeometry

/-- The cohomology of the termwise counit on a K-injective complex is the ordinary
module counit, under the affine cohomology comparison and the exact pullback comparison.
Source: Stacks Project, Tag 0AVW, proof, using the unbounded bound of Tag 08D4.
(blueprint: lem-sc-affine-algebra-kinjective-counit-homology-factorization).

Proof: Cover Y by affine opens V. Their inverse images are affine since f is affine.
Apply the unbounded affine sections calculation (Tag 08D4, with bound one) to I,
whose cohomology modules are quasi-coherent. K-injectivity makes sections of I on
these inverse images compute derived sections. Thus H^n(g_* I) is canonically
identified with g_* H^n(I). Keep the f_*O_X action on each sections complex: the
comparison is linear for this action and commutes with restrictions, so it glues
as a comparison of modules over the direct-image algebra. Exact P commutes with
cohomology. The preceding comparison is e. The canonical exact-functor homology
comparison identifies the contribution of P to the displayed composite. Naturality
of the kernel and image maps identifies the homology of
the termwise counit with the module counit under e: on an affine chart both send
b tensor s to b*s. For arbitrary a, transport this identity from tensor pullback
by the unique adjunction-compatible isomorphism of left adjoints. This computation
uses no derived unit, no derived counit invertibility, and no boundedness of I.
The same maps apply to the zero complex, empty schemes and all integer degrees. -/
theorem affine_algebra_kinjective_counit_homology_factorization
    {X Y : Scheme.{v}} (f : X ⟶ Y) [IsAffineHom f]
    (P : SheafOfModules.{v} (moduleRings (directImageAlgebraSpace f)) ⥤
      SheafOfModules.{v} (moduleRings X.toRingedSpace))
    [P.Additive] [Limits.PreservesFiniteLimits P] [Limits.PreservesFiniteColimits P]
    (a : P ⊣ RingedSpace.moduleDirectImage (toDirectImageAlgebraSpace f))
    (I : CochainComplex (SheafOfModules.{v} (moduleRings X.toRingedSpace)) ℤ)
    [I.IsKInjective] (hI : ∀ n : ℤ, (I.homology n).IsQuasicoherent) (n : ℤ) :
    ∃ e : (((RingedSpace.moduleDirectImage
          (toDirectImageAlgebraSpace f)).mapHomologicalComplex (.up ℤ)).obj I).homology n ≅
        (RingedSpace.moduleDirectImage (toDirectImageAlgebraSpace f)).obj (I.homology n),
      HomologicalComplex.homologyMap ((a.mapHomologicalComplex (.up ℤ)).counit.app I) n =
        (P.mapHomologicalComplexHomologyIso (.up ℤ) n).hom.app
            (((RingedSpace.moduleDirectImage
              (toDirectImageAlgebraSpace f)).mapHomologicalComplex (.up ℤ)).obj I) ≫
          P.map e.hom ≫ a.counit.app (I.homology n) := by
  have := affineAlgebraCounitHomologyComparison_isIso f P a I hI n
  exact ⟨asIso (affineAlgebraCounitHomologyComparison f P a I n),
    affine_algebra_kinjective_counit_compatibility f P a I n⟩

end AlgebraicGeometry
