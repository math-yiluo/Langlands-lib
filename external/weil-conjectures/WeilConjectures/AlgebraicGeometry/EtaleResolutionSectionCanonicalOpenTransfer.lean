/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.EtaleResolutionSectionCanonicalComparison
import WeilConjectures.AlgebraicGeometry.EtaleResolutionSectionOpenTransferExt
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageExact
import WeilConjectures.AlgebraicGeometry.EtaleOpenObjectCohomologyMap
import WeilConjectures.AlgebraicGeometry.EtaleResolutionSectionTransfer
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance

/-!
# Transfer of normalized resolution comparisons

Source: Stacks Project, Tags 0A50 and 03F3.
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace AlgebraicGeometry.Etale

private theorem section_cocycle
    {S : Scheme.{u}}
    (K : CochainComplex (Sheaf S.smallEtaleTopology AddCommGrpCat.{u + 1}) ℕ)
    (W : S.Opens) (q : ℕ)
    (z : (((etaleSectionFunctor (Scheme.Etale.mk W.ι)).mapHomologicalComplex
      (.up ℕ)).obj K).cycles q) :
    let L := (((etaleSectionFunctor (Scheme.Etale.mk W.ι)).mapHomologicalComplex
      (.up ℕ)).obj K)
    let e := EtaleOpenComparison.sectionsEquiv S.smallEtaleTopology
      (Scheme.Etale.mk W.ι) (K.X q)
    e.symm (L.iCycles q z) ≫ K.d q (q + 1) = 0 := by
  dsimp only
  apply (EtaleOpenComparison.sectionsEquiv S.smallEtaleTopology
    (Scheme.Etale.mk W.ι) (K.X (q + 1))).injective
  rw [EtaleOpenComparison.sectionsEquiv_naturality, AddEquiv.apply_symm_apply,
    map_zero]
  let L := (((etaleSectionFunctor (Scheme.Etale.mk W.ι)).mapHomologicalComplex
    (.up ℕ)).obj K)
  exact ConcreteCategory.congr_hom (L.iCycles_d q (q + 1)) z

/-- The open component of augmentation-preserving canonical section transfer.
Source: Stacks Project, Tags 01F8 and 01FB (resolution functoriality),
Tag 03F3 (localization), and Tag 0A50 (section complexes).
(blueprint: lem-weil-pbc-etale-resolution-section-open-transfer)

Proof: Represent a homology class over W by a cycle z using surjectivity of homologyπ.
The sheafification/free-abelian/Yoneda adjunction gives a unique morphism f from the free
sheaf representing W with section equal to iCycles z; its naturality makes f a cocycle.
Adjoint α to β : g*I → J. Exactness of g* and hα identify β as a comparison of the
resolution g*I of g*G with J. The derived-category formula extMk_hom then computes
pullback of the Ext class of f by applying β to g*f. Precompose with the identity
section on g⁻¹W, pulled through the free-representable comparison. Naturality of the
adjunction unit identifies its evaluation with α at W followed by openSectionPullback.
Expand etaleOpenObjectCohomologyMap as inverse-image Ext followed by precomposition
with etaleOpenFreeSheafUnit. Functoriality of inverse image for the commuting square
(g restricted to W) ≫ W.ι = (g⁻¹W).ι ≫ g gives precisely the coefficient isomorphism
in openCohomologyPullback. Apply cX.open_cocycle and cY.open_cocycle and naturality of
homologyπ, first on z and then on all classes. Boundaries map to boundaries because α
is a chain map. Empty opens, identity morphisms and degree zero need no extra hypothesis. -/
theorem resolutionSection_canonical_transfer_open
    {X Y : Scheme.{u}} (g : Y ⟶ X)
    (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (I : InjectiveResolution G)
    (J : InjectiveResolution ((upperStar AddCommGrpCat.{u + 1} g).obj G))
    (α : I.cocomplex ⟶
      ((lowerStar AddCommGrpCat.{u + 1} g).mapHomologicalComplex (.up ℕ)).obj J.cocomplex)
    (hα : I.ι.f 0 ≫ α.f 0 =
      (upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} g).unit.app G ≫
        (lowerStar AddCommGrpCat.{u + 1} g).map (J.ι.f 0))
    (cX : ResolutionSectionCanonicalComparison G I)
    (cY : ResolutionSectionCanonicalComparison
      ((upperStar AddCommGrpCat.{u + 1} g).obj G) J) :
    ∀ W q x, cY.openEquiv (g ⁻¹ᵁ W) q (HomologicalComplex.homologyMap
      (openResolutionSectionTransfer g I.cocomplex J.cocomplex α W) q x) =
      openCohomologyPullback g W G q (cX.openEquiv W q x) := by
  intro W q x
  let K := (((etaleSectionFunctor (Scheme.Etale.mk W.ι)).mapHomologicalComplex
    (.up ℕ)).obj I.cocomplex)
  let L := (((etaleSectionFunctor (Scheme.Etale.mk (g ⁻¹ᵁ W).ι)).mapHomologicalComplex
    (.up ℕ)).obj J.cocomplex)
  let φ := openResolutionSectionTransfer g I.cocomplex J.cocomplex α W
  have hs : Function.Surjective (K.homologyπ q) :=
    (AddCommGrpCat.epi_iff_surjective (K.homologyπ q)).mp inferInstance
  obtain ⟨z, rfl⟩ := hs x
  let zY := (HomologicalComplex.cyclesMap φ q) z
  let eX := EtaleOpenComparison.sectionsEquiv X.smallEtaleTopology
    (Scheme.Etale.mk W.ι) (I.cocomplex.X q)
  let eY := EtaleOpenComparison.sectionsEquiv Y.smallEtaleTopology
    (Scheme.Etale.mk (g ⁻¹ᵁ W).ι) (J.cocomplex.X q)
  let fX := eX.symm (K.iCycles q z)
  let fY := eY.symm (L.iCycles q zY)
  have hfX : fX ≫ I.cocomplex.d q (q + 1) = 0 :=
    section_cocycle I.cocomplex W q z
  have hfY : fY ≫ J.cocomplex.d q (q + 1) = 0 :=
    section_cocycle J.cocomplex (g ⁻¹ᵁ W) q zY
  have hmap : HomologicalComplex.homologyMap φ q (K.homologyπ q z) =
      L.homologyπ q zY :=
    congrArg (fun f => f z) (HomologicalComplex.homologyπ_naturality φ q)
  rw [hmap, cY.open_cocycle (g ⁻¹ᵁ W) q fY hfY zY
    (eY.apply_symm_apply _).symm,
    cX.open_cocycle W q fX hfX z (eX.apply_symm_apply _).symm]
  apply resolutionSection_transfer_open_ext g G I J α hα W q fX hfX fY hfY
  change eY (eY.symm _) = φ.f q (eX (eX.symm _))
  rw [eY.apply_symm_apply, eX.apply_symm_apply]
  exact congrArg (fun f => f z) (HomologicalComplex.cyclesMap_i φ q)

end AlgebraicGeometry.Etale
