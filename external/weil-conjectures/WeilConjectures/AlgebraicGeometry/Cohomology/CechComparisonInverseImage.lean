/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Cohomology.CechComparisonSystem
import WeilConjectures.AlgebraicGeometry.Cohomology.CechComparisonSystemExistence
import WeilConjectures.AlgebraicGeometry.Cohomology.CechComparisonInverseImageCompatibility

/-! # Inverse-image naturality before affine degeneration

Source: Stacks Project, Tag 01FD, with the normalized comparison of Tag 01EQ.
(blueprint: lem-pc-cech-comparison-inverse-image)
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

namespace AlgebraicGeometry.Scheme.Modules

attribute [local instance] cohomologyHasSheafify cohomologyHasExt

/-- Normalized additive Čech comparisons can be chosen compatibly with inverse image.
There is no acyclicity hypothesis and no assertion that either comparison is invertible.

Source: Stacks Project, Tags 01EQ and 01FD.
(blueprint: lem-pc-cech-comparison-inverse-image)

Proof: Resolve abelian sheaves by injectives and form the augmented ordered Čech
bicomplex. The augmentation from the global-section resolution is a quasi-isomorphism
because positive Čech cohomology of injectives vanishes. Invert it on total cohomology
and compose with the coefficient augmentation to obtain a natural transformation in
all degrees. In degree zero this is gluing followed by the sections-to-Ext identification.
A short exact coefficient sequence that is sectionwise surjective on tuple intersections
induces a short exact Čech sequence; comparing its resolution sequences proves the
connecting-map law. For the displayed coefficient map, resolve the direct image of the
target resolution and compare with the source resolution. The augmented pentagon and
the two global-section squares in 01FD commute. The coordinate hypothesis identifies
the two coefficient augmentations. Taking total cohomology and inverting the injective
Čech quasi-isomorphisms gives the asserted equality. The global-section comparison is
exact inverse image on Ext with the inverse constant-sheaf isomorphism, followed by the
adjoint coefficient map. The same construction works for all modules, including those
which are not quasi-coherent, and for infinite covers. On an empty scheme all complexes
and cohomology groups are zero; degree zero is the ordinary section map. -/
theorem exists_cechComparison_inverseImage
    {R S : Type u} [CommRing R] [CommRing S] {X Y : Scheme.{u}} {ι : Type u}
    (g : Y ⟶ X) (f : X ⟶ Spec (.of R)) (f' : Y ⟶ Spec (.of S))
    (U : ι → X.Opens) (V : ι → Y.Opens)
    (hcover : iSup U = ⊤) (hcover' : iSup V = ⊤)
    (M : X.Modules) (N : Y.Modules)
    (φ : M ⟶ (pushforward g).obj N)
    (hinter : ∀ (k : ℕ) (y : Fin (k + 1) → ι),
      (⨅ l, V (y l)) ≤ g ⁻¹ᵁ (⨅ l, U (y l))) :
    ∃ c : CechComparisonSystem U hcover,
    ∃ c' : CechComparisonSystem V hcover',
    ∀ (q : ℕ) (z : (cechOver f U M).cycles q) (z' : (cechOver f' V N).cycles q),
      (∀ y : Fin (q + 1) → ι,
        cechCoordinate f' V N q y ((cechOver f' V N).iCycles q z') =
          N.presheaf.map (homOfLE (hinter q y)).op
            (φ.val.app (op (⨅ l, U (y l)))
              (cechCoordinate f U M q y ((cechOver f U M).iCycles q z)))) →
      c'.overMap f' N q ((cechOver f' V N).homologyπ q z') =
        Sheaf.H.map (coeff g φ) q
          (Sheaf.H.mapFunctor (invImage g) (constIso g).symm
            ((SheafOfModules.toSheaf X.ringCatSheaf).obj M) q
              (c.overMap f M q ((cechOver f U M).homologyπ q z))) := by
  obtain ⟨c⟩ := exists_cechComparisonSystem U hcover
  obtain ⟨c'⟩ := exists_cechComparisonSystem V hcover'
  refine ⟨c, c', ?_⟩
  exact cechComparison_inverseImage_compatibility g f f' U V hcover hcover'
    M N φ hinter c c'

end AlgebraicGeometry.Scheme.Modules
