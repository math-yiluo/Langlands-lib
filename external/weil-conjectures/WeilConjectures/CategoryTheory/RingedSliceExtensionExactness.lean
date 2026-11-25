/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Category.Ring.Limits
public import WeilConjectures.CategoryTheory.ExtensionByZeroPresheaf
public import WeilConjectures.CategoryTheory.RingedSiteModules
import WeilConjectures.CategoryTheory.RingedSliceExtensionPreservesExact
import WeilConjectures.CategoryTheory.RingedSliceExtensionReflectsExact

/-!
# Exactness detected by extension from a ringed-site slice

Source: Stacks Project, Modules on Sites, Tag 0E8G
(auxiliary; not a blueprint node).
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits

namespace SheafOfModules

/-- Extension from a slice, constructed by sheafifying the direct-sum presheaf,
preserves and reflects exactness at the middle term. Equality is equality of
subobjects of the middle module sheaf, so it expresses precisely `im(a) = ker(b)`.
The module universe `max u v` contains both the objects and arrows of the site.

Source: Stacks Project, Modules on Sites, Tag 0E8G
(auxiliary; not a blueprint node).

Proof plan:
1. By `lem-pur-site-restriction-module-adjunction-exact`, the sheafified direct-sum
extension is exact, hence preserves the equality of image and kernel.
2. The adjunction unit sends a section over `(V, φ)` into the `φ` summand and then
into its sheafification. This is natural and module-linear. The underlying abelian
and set sheafification comparisons (`lem-pc-sites-module-sheafification-interface`
and `lem-pc-sites-sheafification-underlying-sets`) and the local equality criterion
(`lem-weil-pbc-site-sheafification-sections-local`) show that a section in its kernel
vanishes locally. Coordinate injection into a direct sum is injective, and sheaf
separatedness makes the section zero. This includes empty covering families.
3. This monic unit implies that extension detects zero objects: if the extension
of a module is zero, that module injects into its zero restriction.
4. Factor the first arrow through the kernel of the second and take the cokernel
of this factorization. The original complex is exact precisely when this cokernel
is zero. Exact extension identifies its extension with the analogous cokernel of
the extended complex. Exactness there makes that extension zero; step 3 makes the
original cokernel zero and proves reflection. -/
theorem ringedSliceExtension_exact_iff
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    (O : Sheaf J CommRingCat.{max u v}) (U : C)
    (S : ShortComplex (CategoryTheory.ringedSiteModules.{max u v}
      (((sheafCompose J
          (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj O).over U))) :
    imageSubobject S.f = kernelSubobject S.g ↔
      imageSubobject
          ((extensionByZeroPresheaf.{max u v}
              ((sheafCompose J
                (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj O) U ⋙
            PresheafOfModules.sheafification.{max u v}
              (𝟙 ((sheafCompose J
                (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj O).obj)).map S.f) =
        kernelSubobject
          ((extensionByZeroPresheaf.{max u v}
              ((sheafCompose J
                (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj O) U ⋙
            PresheafOfModules.sheafification.{max u v}
              (𝟙 ((sheafCompose J
                (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj O).obj)).map S.g) := by
  rw [← ShortComplex.exact_iff_image_eq_kernel S]
  exact ⟨ringedSliceExtension_preserves_exact J O U S,
    ringedSliceExtension_reflects_exact J O U S⟩

end SheafOfModules
