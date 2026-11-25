/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.CategoryTheory.Abelian.Injective.Ext
public import WeilConjectures.AlgebraicGeometry.EtaleOpenFreeSheafPullback
import WeilConjectures.CategoryTheory.ExactFunctorResolutionCocycle

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace AlgebraicGeometry.Etale

set_option backward.isDefEq.respectTransparency false in
/-- Transfer of a represented Ext class before applying the open-object map.
Source: Stacks Project, Tags 01F8 and 01FB (resolution functoriality), and 0A50.
(blueprint: lem-weil-pbc-etale-resolution-section-transfer-ext-class)

Proof: Adjoint each component of α to a morphism β from g*I to J. Naturality of
adjunction gives its chain-map equations; hα gives the augmentation equation.
Exactness of g* preserves the quasi-isomorphism from G to I. In the derived
category β therefore represents the identity of g*G under the augmentation
identifications. Apply `InjectiveResolution.extMk_hom` and
`Abelian.Ext.mapExactFunctor_hom` to compute the image of the class represented
by fX as the cocycle g*fX followed by β. Precompose with
etaleOpenFreeSheafPullback. Naturality of the adjunction unit with fX and the
counit identity express the section of this composite as α applied to the
section of fX, then restricted along openSectionPullback. This is precisely
openResolutionSectionTransfer. By hsections and injectivity of sectionsEquiv
this cocycle equals fY. Precomposition of Ext by a degree-zero morphism agrees
with precomposition of its representing cocycle, giving the stated equality.
No localization or open cohomology comparison is involved. -/
theorem resolutionSection_transfer_ext
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
    J.extMk fY (q + 1) rfl hfY =
      (Abelian.Ext.mk₀ (etaleOpenFreeSheafPullback g W)).comp
        ((I.extMk fX (q + 1) rfl hfX).mapExactFunctor
          (upperStar AddCommGrpCat.{u + 1} g)) (zero_add q) := by
  let L := upperStar AddCommGrpCat.{u + 1} g
  let R := lowerStar AddCommGrpCat.{u + 1} g
  let adj := upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} g
  let e : (L.mapHomologicalComplex (.up ℕ)).obj I.cocomplex ⟶ J.cocomplex :=
    { f := fun n ↦ (adj.homEquiv _ _).symm (α.f n)
      comm' := by
        intro n m _
        change (adj.homEquiv _ _).symm (α.f n) ≫ J.cocomplex.d n m =
          L.map (I.cocomplex.d n m) ≫ (adj.homEquiv _ _).symm (α.f m)
        apply (adj.homEquiv _ _).injective
        rw [adj.homEquiv_naturality_left, adj.homEquiv_naturality_right]
        simpa using (α.comm n m) }
  have he : L.map (I.ι.f 0) ≫ e.f 0 = 𝟙 (L.obj G) ≫ J.ι.f 0 := by
    change L.map (I.ι.f 0) ≫ (adj.homEquiv _ _).symm (α.f 0) = _
    rw [← adj.homEquiv_naturality_left_symm, hα]
    rw [adj.homEquiv_naturality_right_symm]
    change (adj.homEquiv G (L.obj G)).symm (adj.unit.app G) ≫ J.ι.f 0 = _
    rw [← adj.homEquiv_id, Equiv.symm_apply_apply, Category.id_comp]
  have hc : (L.map fX ≫ e.f q) ≫ J.cocomplex.d q (q + 1) = 0 := by
    have hecomm := e.comm q (q + 1)
    change e.f q ≫ J.cocomplex.d q (q + 1) =
      L.map (I.cocomplex.d q (q + 1)) ≫ e.f (q + 1) at hecomm
    rw [Category.assoc, hecomm, ← L.map_comp_assoc, hfX, L.map_zero, zero_comp]
  have hfe : etaleOpenFreeSheafPullback g W ≫ (L.map fX ≫ e.f q) = fY := by
    apply (EtaleOpenComparison.sectionsEquiv Y.smallEtaleTopology
      (Scheme.Etale.mk (g ⁻¹ᵁ W).ι) (J.cocomplex.X q)).injective
    rw [EtaleOpenComparison.sectionsEquiv_naturality]
    dsimp only [etaleOpenFreeSheafPullback]
    rw [AddEquiv.apply_symm_apply]
    have hn : fX ≫ adj.unit.app (I.cocomplex.X q) =
        adj.unit.app _ ≫ R.map (L.map fX) := adj.unit.naturality fX
    have hαe : adj.unit.app (I.cocomplex.X q) ≫ R.map (e.f q) = α.f q :=
      (adj.homEquiv _ _).apply_symm_apply (α.f q)
    have hn' : adj.unit.app _ ≫ R.map (L.map fX ≫ e.f q) = fX ≫ α.f q := by
      rw [R.map_comp, ← Category.assoc, ← hn, Category.assoc, hαe]
    have hs := congrArg (EtaleOpenComparison.sectionsEquiv X.smallEtaleTopology
      (Scheme.Etale.mk W.ι) (R.obj (J.cocomplex.X q))) hn'
    rw [EtaleOpenComparison.sectionsEquiv_naturality,
      EtaleOpenComparison.sectionsEquiv_naturality] at hs
    rw [hsections]
    change (L.map fX ≫ e.f q).hom.app _
      (((L.obj _).obj.map (openSectionPullback g W).op)
        ((adj.unit.app _).hom.app _
          (EtaleOpenComparison.sectionsEquiv X.smallEtaleTopology
            (Scheme.Etale.mk W.ι) _ (𝟙 _)))) =
      (J.cocomplex.X q).obj.map (openSectionPullback g W).op
        ((α.f q).hom.app _
          (EtaleOpenComparison.sectionsEquiv X.smallEtaleTopology
            (Scheme.Etale.mk W.ι) _ fX))
    rw [NatTrans.naturality_apply]
    exact congrArg ((J.cocomplex.X q).obj.map (openSectionPullback g W).op) hs
  have hExt := exactFunctor_resolution_cocycle L (𝟙 (L.obj G)) I J e he q fX hfX hc
  rw [Abelian.Ext.comp_mk₀_id] at hExt
  rw [hExt, J.mk₀_comp_extMk]
  simp only [hfe]

end AlgebraicGeometry.Etale
