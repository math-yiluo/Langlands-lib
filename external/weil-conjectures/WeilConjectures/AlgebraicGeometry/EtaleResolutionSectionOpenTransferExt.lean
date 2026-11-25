/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.CategoryTheory.Abelian.Injective.Ext
public import WeilConjectures.AlgebraicGeometry.EtaleResolutionSectionTransfer
public import WeilConjectures.AlgebraicGeometry.EtaleOpenCohomologyComparison
import WeilConjectures.AlgebraicGeometry.EtaleResolutionSectionTransferExtClass
import WeilConjectures.AlgebraicGeometry.EtaleOpenObjectCohomologyPullback

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace AlgebraicGeometry.Etale

/-- Transfer of Ext cocycles represented by sections over an open.
Source: Stacks Project, Tags 01F8 and 01FB (resolution functoriality),
03F3 (localization), and 0A50 (section complexes).
(blueprint: lem-weil-pbc-etale-resolution-section-open-transfer-ext)

Proof: Adjoint α to β : g*I → J. The augmentation equation hα makes β a
comparison from the exact pullback resolution of g*G to J. Write I.extMk fX
using InjectiveResolution.extMk_hom in the derived category and apply the
exact functor g*. Cancel the augmentation identifications using hα. This
expresses the pulled-back Ext class by the cocycle β composed with g*fX.
Precompose with the free-representable map induced by openSectionPullback.
The sections adjunction, natural in coefficients, identifies its section
with the degree-q section transfer of the section of fX. By hsections and
injectivity of sectionsEquiv this cocycle is fY. Expand
etaleOpenObjectCohomologyMap: it applies the exact inverse-image functor for
the open inclusion and precomposes with etaleOpenFreeSheafUnit. Naturality
of the adjunction unit identifies the pulled-back identity generator with
the identity generator of g⁻¹W. The square
(morphismRestrict g W) ≫ W.ι = (g⁻¹W).ι ≫ g and inverse-image composition
comparison identify the resulting coefficient transport with that in
openCohomologyPullback. Ext.mapExactFunctor_comp and associativity complete
the equality. This calculation concerns Hom cocycles and Ext only; it does
not assume any canonical homology comparison. It is valid at q = 0, on
empty opens, and for the zero coefficient sheaf. -/
theorem resolutionSection_transfer_open_ext
    {X Y : Scheme.{u}} (g : Y ⟶ X)
    (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (I : InjectiveResolution G)
    (J : InjectiveResolution ((upperStar AddCommGrpCat.{u + 1} g).obj G))
    (α : I.cocomplex ⟶
      ((lowerStar AddCommGrpCat.{u + 1} g).mapHomologicalComplex (.up ℕ)).obj J.cocomplex)
    (hα : I.ι.f 0 ≫ α.f 0 =
      (upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} g).unit.app G ≫
        (lowerStar AddCommGrpCat.{u + 1} g).map (J.ι.f 0))
    (W : X.Opens) (q : ℕ)
    (fX : (etaleOpenFreeSheaf X).obj (Scheme.Etale.mk W.ι) ⟶ I.cocomplex.X q)
    (hfX : fX ≫ I.cocomplex.d q (q + 1) = 0)
    (fY : (etaleOpenFreeSheaf Y).obj (Scheme.Etale.mk (g ⁻¹ᵁ W).ι) ⟶ J.cocomplex.X q)
    (hfY : fY ≫ J.cocomplex.d q (q + 1) = 0)
    (hsections : EtaleOpenComparison.sectionsEquiv Y.smallEtaleTopology
      (Scheme.Etale.mk (g ⁻¹ᵁ W).ι) (J.cocomplex.X q) fY =
      (openResolutionSectionTransfer g I.cocomplex J.cocomplex α W).f q
        (EtaleOpenComparison.sectionsEquiv X.smallEtaleTopology
          (Scheme.Etale.mk W.ι) (I.cocomplex.X q) fX)) :
    etaleOpenObjectCohomologyMap ((upperStar AddCommGrpCat.{u + 1} g).obj G)
      q (g ⁻¹ᵁ W) (J.extMk fY (q + 1) rfl hfY) =
      openCohomologyPullback g W G q
        (etaleOpenObjectCohomologyMap G q W (I.extMk fX (q + 1) rfl hfX)) := by
  rw [resolutionSection_transfer_ext g G I J α hα W q fX hfX fY hfY hsections]
  exact etaleOpenObjectCohomologyMap_pullback g W G q (I.extMk fX (q + 1) rfl hfX)

end AlgebraicGeometry.Etale
