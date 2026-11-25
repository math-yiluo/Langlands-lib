/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.EtaleRestrictScalarsFunctorComparisons
import WeilConjectures.AlgebraicGeometry.EtaleRestrictScalarsAdjunctionIdentities
import WeilConjectures.AlgebraicGeometry.EtaleRestrictScalarsPullbackSquare

/-! # Coefficient compatibility of the derived étale exchange morphism -/

@[expose] public section

universe u

open CategoryTheory
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale

namespace AlgebraicGeometry.Etale

private theorem exchange_compatibility
    {CS CT CX CY CS' CT' CX' CY' : Type*}
    [Category CS] [Category CT] [Category CX] [Category CY]
    [Category CS'] [Category CT'] [Category CX'] [Category CY']
    (rS : CS' ⥤ CS) (rT : CT' ⥤ CT) (rX : CX' ⥤ CX) (rY : CY' ⥤ CY)
    (P : CS ⥤ CX) (G : CS ⥤ CT) (E : CT ⥤ CY) (H : CX ⥤ CY)
    (Rg : CT ⥤ CS) (Rh : CY ⥤ CX)
    (P' : CS' ⥤ CX') (G' : CS' ⥤ CT') (E' : CT' ⥤ CY') (H' : CX' ⥤ CY')
    (Rg' : CT' ⥤ CS') (Rh' : CY' ⥤ CX')
    (αp : rS ⋙ P ⟶ P' ⋙ rX) (αg : rS ⋙ G ⟶ G' ⋙ rT)
    (αh : rX ⋙ H ⟶ H' ⋙ rY) (αe : rT ⋙ E ⟶ E' ⋙ rY)
    (βg : rT ⋙ Rg ⟶ Rg' ⋙ rS) (βh : rY ⋙ Rh ⟶ Rh' ⋙ rX)
    (θ : P ⋙ H ⟶ G ⋙ E) (θ' : P' ⋙ H' ⟶ G' ⋙ E')
    (η : 𝟭 CX ⟶ H ⋙ Rh) (η' : 𝟭 CX' ⟶ H' ⋙ Rh')
    (ε : Rg ⋙ G ⟶ 𝟭 CT) (ε' : Rg' ⋙ G' ⟶ 𝟭 CT')
    (hunit : ∀ M, η.app (rX.obj M) ≫ (Rh.map (αh.app M) ≫ βh.app (H'.obj M)) =
      rX.map (η'.app M))
    (hcounit : ∀ N, (G.map (βg.app N) ≫ αg.app (Rg'.obj N)) ≫
      rT.map (ε'.app N) = ε.app (rT.obj N))
    (hsquare : ∀ L, H.map (αp.app L) ≫ αh.app (P'.obj L) ≫ rY.map (θ'.app L) =
      θ.app (rS.obj L) ≫ E.map (αg.app L) ≫ αe.app (G'.obj L))
    (K : CT') :
    (P.map (βg.app K) ≫ αp.app (Rg'.obj K)) ≫
      rX.map (η'.app (P'.obj (Rg'.obj K)) ≫ Rh'.map (θ'.app (Rg'.obj K)) ≫
        Rh'.map (E'.map (ε'.app K))) =
    (η.app (P.obj (Rg.obj (rT.obj K))) ≫ Rh.map (θ.app (Rg.obj (rT.obj K))) ≫
      Rh.map (E.map (ε.app (rT.obj K)))) ≫
        (Rh.map (αe.app K) ≫ βh.app (E'.obj K)) := by
  let L := Rg'.obj K
  let d : Rg.obj (rT.obj K) ⟶ rS.obj L := βg.app K
  let ap : P.obj (rS.obj L) ⟶ rX.obj (P'.obj L) := αp.app L
  let ag : G.obj (rS.obj L) ⟶ rT.obj (G'.obj L) := αg.app L
  let ah : H.obj (rX.obj (P'.obj L)) ⟶ rY.obj (H'.obj (P'.obj L)) :=
    αh.app (P'.obj L)
  let ae : E.obj (rT.obj (G'.obj L)) ⟶ rY.obj (E'.obj (G'.obj L)) :=
    αe.app (G'.obj L)
  let a := P.map d ≫ ap
  let v := G.map d ≫ ag
  let t₁ := Rh.map (H.map a ≫ ah) ≫
    βh.app (H'.obj (P'.obj L))
  let t₂ := Rh.map (E.map v ≫ ae) ≫
    βh.app (E'.obj (G'.obj L))
  have hu : a ≫ rX.map (η'.app (P'.obj L)) =
      η.app (P.obj (Rg.obj (rT.obj K))) ≫ t₁ := by
    have hi := hunit (P'.obj L)
    change η.app (rX.obj (P'.obj L)) ≫
      (Rh.map ah ≫ βh.app _) =
        rX.map (η'.app (P'.obj L)) at hi
    rw [← hi]
    dsimp only [t₁]
    simp only [Functor.map_comp, Category.assoc]
    have hn := η.naturality a
    change a ≫ η.app (rX.obj (P'.obj L)) =
      η.app (P.obj (Rg.obj (rT.obj K))) ≫ Rh.map (H.map a) at hn
    rw [← Category.assoc a, hn]
    simp only [Category.assoc]
  have hs : t₁ ≫ rX.map (Rh'.map (θ'.app L)) =
      Rh.map (θ.app (Rg.obj (rT.obj K))) ≫ t₂ := by
    have hd := βh.naturality (θ'.app L)
    change Rh.map (rY.map (θ'.app L)) ≫
      βh.app (E'.obj (G'.obj L)) =
      βh.app (H'.obj (P'.obj L)) ≫
        rX.map (Rh'.map (θ'.app L)) at hd
    have hsq : H.map ap ≫ ah ≫ rY.map (θ'.app L) =
        θ.app (rS.obj L) ≫ E.map ag ≫ ae :=
      hsquare L
    have hn := θ.naturality d
    change H.map (P.map d) ≫ θ.app (rS.obj L) =
      θ.app (Rg.obj (rT.obj K)) ≫ E.map (G.map d) at hn
    have hy : (H.map a ≫ ah) ≫ rY.map (θ'.app L) =
        θ.app (Rg.obj (rT.obj K)) ≫ (E.map v ≫ ae) := by
      dsimp only [a, v]
      simp only [Functor.map_comp, Category.assoc]
      rw [hsq, ← Category.assoc (H.map (P.map d)), hn]
      simp only [Category.assoc]
    dsimp only [t₁, t₂]
    rw [Category.assoc, ← hd, ← Category.assoc, ← Rh.map_comp, hy, Rh.map_comp]
    simp only [Category.assoc]
  have hc : t₂ ≫ rX.map (Rh'.map (E'.map (ε'.app K))) =
      Rh.map (E.map (ε.app (rT.obj K))) ≫
        (Rh.map (αe.app K) ≫ βh.app (E'.obj K)) := by
    have hd := βh.naturality
      (E'.map (ε'.app K))
    change Rh.map (rY.map (E'.map (ε'.app K))) ≫
      βh.app (E'.obj K) =
      βh.app (E'.obj (G'.obj L)) ≫
        rX.map (Rh'.map (E'.map (ε'.app K))) at hd
    have hn := αe.naturality (ε'.app K)
    change E.map (rT.map (ε'.app K)) ≫
      αe.app K =
      ae ≫ rY.map (E'.map (ε'.app K)) at hn
    have hi := hcounit K
    change v ≫ rT.map (ε'.app K) = ε.app (rT.obj K) at hi
    have hy : (E.map v ≫ ae) ≫ rY.map (E'.map (ε'.app K)) =
        E.map (ε.app (rT.obj K)) ≫
          αe.app K := by
      rw [Category.assoc, ← hn, ← Category.assoc, ← E.map_comp, hi]
    dsimp only [t₂]
    rw [Category.assoc, ← hd, ← Category.assoc, ← Rh.map_comp, hy, Rh.map_comp]
    change (Rh.map (E.map (ε.app (rT.obj K))) ≫
        Rh.map (αe.app K)) ≫ _ =
      Rh.map (E.map (ε.app (rT.obj K))) ≫
        (Rh.map (αe.app K) ≫ _)
    exact Category.assoc _ _ _
  change a ≫ rX.map (η'.app (P'.obj L) ≫
      Rh'.map (θ'.app L) ≫ Rh'.map (E'.map (ε'.app K))) = _
  simp only [Functor.map_comp, Category.assoc]
  rw [← Category.assoc a, hu, Category.assoc, ← Category.assoc t₁, hs,
    Category.assoc, hc]

/-- The canonical inverse- and direct-image coefficient comparisons intertwine the
derived exchange morphisms. The endpoint comparisons are already constructed as
isomorphisms; this theorem asserts only the compatibility of the morphisms.

Source: Stacks Project, Remark 21.19.3, Tag 07A7, and Lemma 21.20.7(3), Tag 0D6J.
Proof: direct image and coextension of coefficients commute sectionwise. The
inverse-image coefficient isomorphism is the uniqueness isomorphism between the
two left adjoints of this composite, so it respects their units and counits. The
direct-image coefficient comparison is the unique morphism compatible with the
right-derived units. These characterizations show that the two composites in the
assertion have the same adjoint: apply inverse image along h, use the equality of
the two composite inverse images coming from the commutative square, and then
apply the inverse image along e of the counit for g. This is exactly the mate
construction in 07A7. The coefficient comparisons commute with each operation:
composition by uniqueness of adjoints and derived functors, and the counit by
the unit/counit identities of the uniqueness isomorphism. Equality of adjoints
gives the asserted equality. One may check the right-derived comparison identities
on bounded below injective resolutions; their restricted complexes are acyclic
for direct image, so their derived units are invertible. No base-change
isomorphism assertion, smoothness, or torsion hypothesis enters this argument.
(blueprint: lem-sbc-restrict-scalars-derived-exchange) -/
theorem derivedBaseChange_restrictScalars_exchange
    {Λ Λ' : Type (u + 1)} [CommRing Λ] [CommRing Λ'] (φ : Λ →+* Λ')
    {X S T Y : Scheme.{u}} {p : X ⟶ S} {g : T ⟶ S} {e : Y ⟶ T} {h : Y ⟶ X}
    (sq : IsPullback e h g p)
    (K : DerivedCategory.Plus (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ'))) :
    (derivedBaseChangeSourceRestrictScalarsIso φ p g K).hom ≫
        (Sheaf.restrictScalars X.smallEtaleTopology φ).mapDerivedCategoryPlus.map
          ((baseChange (ModuleCat.{u + 1} Λ') sq.toCommSq).app K) =
      (baseChange (ModuleCat.{u + 1} Λ) sq.toCommSq).app
          ((Sheaf.restrictScalars T.smallEtaleTopology φ).mapDerivedCategoryPlus.obj K) ≫
        (derivedBaseChangeTargetRestrictScalarsIso φ e h K).hom := by
  rw [baseChange_app, baseChange_app]
  rw [baseChangeUnitStep_app, baseChangeSquareStep_hom_app, baseChangeCounitStep_app,
    baseChangeUnitStep_app, baseChangeSquareStep_hom_app, baseChangeCounitStep_app]
  exact exchange_compatibility
    (Sheaf.restrictScalars S.smallEtaleTopology φ).mapDerivedCategoryPlus
    (Sheaf.restrictScalars T.smallEtaleTopology φ).mapDerivedCategoryPlus
    (Sheaf.restrictScalars X.smallEtaleTopology φ).mapDerivedCategoryPlus
    (Sheaf.restrictScalars Y.smallEtaleTopology φ).mapDerivedCategoryPlus
    D+((p)^*[ModuleCat.{u + 1} Λ]) D+((g)^*[ModuleCat.{u + 1} Λ])
    D+((e)^*[ModuleCat.{u + 1} Λ]) D+((h)^*[ModuleCat.{u + 1} Λ])
    R+((g)_*[ModuleCat.{u + 1} Λ]) R+((h)_*[ModuleCat.{u + 1} Λ])
    D+((p)^*[ModuleCat.{u + 1} Λ']) D+((g)^*[ModuleCat.{u + 1} Λ'])
    D+((e)^*[ModuleCat.{u + 1} Λ']) D+((h)^*[ModuleCat.{u + 1} Λ'])
    R+((g)_*[ModuleCat.{u + 1} Λ']) R+((h)_*[ModuleCat.{u + 1} Λ'])
    (derivedUpperStarRestrictScalarsIso φ p).hom
    (derivedUpperStarRestrictScalarsIso φ g).hom
    (derivedUpperStarRestrictScalarsIso φ h).hom
    (derivedUpperStarRestrictScalarsIso φ e).hom
    (derivedLowerStarRestrictScalarsIso φ g).inv
    (derivedLowerStarRestrictScalarsIso φ h).inv
    (pullbackSquareComparison (ModuleCat.{u + 1} Λ) sq.toCommSq).hom
    (pullbackSquareComparison (ModuleCat.{u + 1} Λ') sq.toCommSq).hom
    (derivedUpperStarLowerStarAdjunctionPlus (ModuleCat.{u + 1} Λ) h).unit
    (derivedUpperStarLowerStarAdjunctionPlus (ModuleCat.{u + 1} Λ') h).unit
    (derivedUpperStarLowerStarAdjunctionPlus (ModuleCat.{u + 1} Λ) g).counit
    (derivedUpperStarLowerStarAdjunctionPlus (ModuleCat.{u + 1} Λ') g).counit
    (derivedRestrictScalars_adjunction_identities φ h).1
    (derivedRestrictScalars_adjunction_identities φ g).2
    (pullbackSquareComparison_restrictScalars φ sq.toCommSq) K

end AlgebraicGeometry.Etale
