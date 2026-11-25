/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.CanonicalDerivedTensorHomModel
import WeilConjectures.AlgebraicGeometry.CanonicalTensorHomUncurryDescent
import WeilConjectures.AlgebraicGeometry.CanonicalTensorHomUncurryDescentNaturality

/-! # Normalized derived tensor-Hom maps
Source: Stacks Project, cohomology.tex, Tag 08DJ, and sites-cohomology.tex, Tag 0A90.
(blueprint: lem-pc-canonical-derived-tensor-hom-map-existence).
-/

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe uCD wCD
open CategoryTheory CategoryTheory.MonoidalCategory Opposite TopologicalSpace
namespace AlgebraicGeometry

/-- Existence of normalized natural uncurrying maps, without asserting bijectivity.
Source: Stacks Project, cohomology.tex, Tag 08DJ (lemma-internal-hom), using
sites-cohomology.tex, Tag 0A90 (Hom complexes).
(blueprint: lem-pc-canonical-derived-tensor-hom-map-existence).
Proof: Reuse `homTensorDegreewiseMap_spec`, `homTensorDegreewiseMap_comm`, and
`homTensorDegreewiseMap_natural` for the normalized degreewise construction,
differential compatibility and functoriality. The global-cochain comparison
`homComplex_global_cochains` identifies chain maps with degree-zero cocycles and
homotopies with degree-minus-one boundaries; hence this comparison gives precisely
the stated map on homotopy classes. The pure-tensor condition in the degreewise
specification agrees with `schemeTensorHomUncurryComponent` by the sheaf tensor-Hom
adjunction and symmetry. Thus these existing lemmas supply the component calculation,
including its normalization, rather than an arbitrary existential isomorphism.
Choose K-flat complex representatives of K and L and the fixed K-injective
replacement I(M). A derived map to RHom(L,M) lifts to a homotopy class of maps into
Hom(L,I(M)), since this complex is K-injective for K-flat L. Lift that class to a
chain map. Uncurry its components by the sheaf tensor-Hom adjunction and use tensor
symmetry to put P before L. The total-tensor differential and the Hom differential
agree on each (p,q) summand, so these components define a chain map. Homotopic input
maps give homotopic uncurried maps by the same componentwise calculation. Transport
its localization along the tensor model comparison and inverse resolution map.
Common K-flat resolutions and quasi-isomorphisms into K-injectives show independence
of representatives; componentwise composition gives the three-variable naturality.
For an arbitrary L in the representative equation, replace L by a K-flat Lc.
Hom(-,I(M)) and P tensor - both invert this quasi-isomorphism; the componentwise
construction commutes with it. Cancel the localized comparison to obtain the exact
representative equation for L. This constructs functions only; their inverse laws
are not asserted here. -/
theorem exists_canonicalDerivedTensorHomMap (X : Scheme.{uCD})
    [HasDerivedCategory.{wCD} (SheafOfModules.{uCD} (moduleRings X.toRingedSpace))] :
    ∃ t : ∀ K L M : schemeDerivedCategory X,
      (K ⟶ (derivedInternalHom (Opens.grothendieckTopology X.toRingedSpace)
        X.toRingedSpace.sheaf).obj (op L, M)) → (K ⊗ L ⟶ M),
      IsCanonicalDerivedTensorHomMap X t := by
  obtain ⟨t, ht, hi⟩ := exists_tensorHomUncurry_descent X
  refine ⟨t, tensorHomUncurry_descent_natural X t ht hi, ?_⟩
  intro P L M hP φ
  refine ⟨schemeTensorHomUncurry X P L M φ, ?_, ht P L M hP φ⟩
  intro p q n h h'
  exact schemeTensorHomUncurry_component X P L M φ p q n h h'

end AlgebraicGeometry
