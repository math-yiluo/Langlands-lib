/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Defs
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.RestrictScalars
public import Mathlib.CategoryTheory.Comma.Arrow
import WeilConjectures.AlgebraicGeometry.EtaleRestrictScalarsExchange

/-!
# Compatibility of étale base change with restriction of coefficients

The comparison identifies the entire base-change arrow, including its map, rather than
only identifying its source and target.
-/

@[expose] public section

universe u

open CategoryTheory
open scoped AlgebraicGeometry.Etale

namespace AlgebraicGeometry.Etale

/-- The coefficient comparison supplies isomorphisms on the source and target of the
base-change arrow, and these isomorphisms intertwine the two arrows.  This is the
derived-functor comparison part; the arrow-category packaging is proved below.

Source: Stacks Project, Lemma 21.20.7(3), Tag 0D6J, and Remark 21.19.3, Tag 07A7.
Proof: compare inverse and direct images sectionwise, derive the comparison using an
injective resolution, and check compatibility with the adjunction units and counits.
(blueprint: lem-sbc-base-change-restrict-scalars-comparison) -/
theorem restrictScalars_baseChange_comparison
    {Λ Λ' : Type (u + 1)} [CommRing Λ] [CommRing Λ'] (φ : Λ →+* Λ')
    {X S T Y : Scheme.{u}} {p : X ⟶ S} {g : T ⟶ S} {e : Y ⟶ T} {h : Y ⟶ X}
    (sq : IsPullback e h g p) [QuasiCompact g] [QuasiSeparated g] (q : ℤ)
    (G : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ')) :
    ∃ (a : (baseChangeSourceFunctor Λ p g q).obj
        ((Sheaf.restrictScalars T.smallEtaleTopology φ).obj G) ≅
        (Sheaf.restrictScalars X.smallEtaleTopology φ).obj
          ((baseChangeSourceFunctor Λ' p g q).obj G))
      (b : (baseChangeTargetFunctor Λ e h q).obj
        ((Sheaf.restrictScalars T.smallEtaleTopology φ).obj G) ≅
        (Sheaf.restrictScalars X.smallEtaleTopology φ).obj
          ((baseChangeTargetFunctor Λ' e h q).obj G)),
      a.hom ≫ (Sheaf.restrictScalars X.smallEtaleTopology φ).map
          (baseChangeHomologyMap Λ' sq q G) =
        baseChangeHomologyMap Λ sq q
          ((Sheaf.restrictScalars T.smallEtaleTopology φ).obj G) ≫ b.hom := by
  let K := (DerivedCategory.Plus.singleFunctor _ 0).obj G
  let d := ((Sheaf.restrictScalars T.smallEtaleTopology φ).mapDerivedCategoryPlusSingleFunctor
    0).symm.app G
  let A := ((g)_*[ModuleCat.{u + 1} Λ]).rightDerivedFunctorPlus ⋙
    ((p)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlus
  let B := ((e)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlus ⋙
    ((h)_*[ModuleCat.{u + 1} Λ]).rightDerivedFunctorPlus
  let aD := A.mapIso d ≪≫ derivedBaseChangeSourceRestrictScalarsIso φ p g K
  let bD := B.mapIso d ≪≫ derivedBaseChangeTargetRestrictScalarsIso φ e h K
  let res := Sheaf.restrictScalars X.smallEtaleTopology φ
  let bc := baseChange (ModuleCat.{u + 1} Λ) sq.toCommSq
  let bc' := baseChange (ModuleCat.{u + 1} Λ') sq.toCommSq
  have wD : aD.hom ≫ res.mapDerivedCategoryPlus.map (bc'.app K) =
      bc.app _ ≫ bD.hom := by
    dsimp only [aD, bD, Functor.mapIso_hom, Iso.trans_hom]
    rw [Category.assoc, derivedBaseChange_restrictScalars_exchange φ sq K]
    have hd : A.map d.hom ≫ bc.app _ = bc.app _ ≫ B.map d.hom :=
      bc.naturality d.hom
    change A.map d.hom ≫ (bc.app _ ≫ _) = _
    rw [← Category.assoc, hd, Category.assoc]
  let H := DerivedCategory.Plus.homologyFunctor
    (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) q
  let c := res.mapDerivedCategoryPlusHomologyFunctorIso q
  let a := H.mapIso aD ≪≫ c.symm.app _
  let b := H.mapIso bD ≪≫ c.symm.app _
  refine ⟨a, b, ?_⟩
  have w := congrArg H.map wD
  simp only [Functor.map_comp] at w
  have hn : H.map (res.mapDerivedCategoryPlus.map (bc'.app K)) ≫
      c.inv.app ((((h)_*[ModuleCat.{u + 1} Λ']).rightDerivedFunctorPlus).obj
        ((((e)^*[ModuleCat.{u + 1} Λ']).mapDerivedCategoryPlus).obj K)) =
    c.inv.app ((((p)^*[ModuleCat.{u + 1} Λ']).mapDerivedCategoryPlus).obj
        ((((g)_*[ModuleCat.{u + 1} Λ']).rightDerivedFunctorPlus).obj K)) ≫
      res.map ((DerivedCategory.Plus.homologyFunctor _ q).map (bc'.app K)) :=
    c.inv.naturality (bc'.app K)
  change (H.map aD.hom ≫ c.inv.app _) ≫
      res.map ((DerivedCategory.Plus.homologyFunctor _ q).map (bc'.app K)) =
    H.map (bc.app _) ≫ (H.map bD.hom ≫ c.inv.app _)
  rw [Category.assoc, ← hn, ← Category.assoc, w, Category.assoc]

/-- Restriction of coefficients identifies the degreewise base-change arrows.

Sources: Stacks Project, Lemma 21.20.7(3), Tag 0D6J
(https://stacks.math.columbia.edu/tag/0D6J), for coefficient-independent derived direct
image; Remark 21.19.3, Tag 07A7 (https://stacks.math.columbia.edu/tag/07A7), for construction
of the base-change map by adjunction. The assembly below is the comparison part of
`WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Coefficients`, the
change-of-rings paragraph in the module docstring and in
`isIso_baseChangeHomologyMap_of_nsmul_eq_zero`; the following is the coefficient-comparison
part of that argument, without any base-change-isomorphism hypothesis.

Proof: restriction of scalars is exact and is computed on the same underlying sheaves.
Inverse image commutes with it: the underlying inverse image is the inverse image of the
underlying abelian sheaf, with the restricted scalar action. Direct image commutes with it
sectionwise. Higher direct images commute with it as well: resolve a module sheaf by
injective module sheaves; their underlying sheaves are acyclic for direct image on every
étale slice, so the same resolution computes direct-image cohomology after restriction.
This gives the comparison on derived direct images, compatible with their units and with
composition. The underived exchange map is obtained from the pullback/direct-image
adjunction units and counits, which agree under these comparisons. Taking its derived
mate, then the degree-q homology, therefore gives a commutative square with invertible
vertical maps. These two maps and their commutativity give the asserted arrow isomorphism.
The construction also works for negative q, when both arrows have zero endpoints.

(blueprint: lem-sbc-base-change-restrict-scalars-arrow) -/
theorem exists_baseChangeHomologyMap_restrictScalars_arrow_iso
    {Λ Λ' : Type (u + 1)} [CommRing Λ] [CommRing Λ'] (φ : Λ →+* Λ')
    {X S T Y : Scheme.{u}} {p : X ⟶ S} {g : T ⟶ S} {e : Y ⟶ T} {h : Y ⟶ X}
    (sq : IsPullback e h g p) [QuasiCompact g] [QuasiSeparated g] (q : ℤ)
    (G : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ')) :
    Nonempty (Arrow.mk (baseChangeHomologyMap Λ sq q
      ((Sheaf.restrictScalars T.smallEtaleTopology φ).obj G)) ≅
      Arrow.mk ((Sheaf.restrictScalars X.smallEtaleTopology φ).map
        (baseChangeHomologyMap Λ' sq q G))) := by
  obtain ⟨a, b, hab⟩ := restrictScalars_baseChange_comparison φ sq q G
  exact ⟨Arrow.isoMk' _ _ a b hab⟩

end AlgebraicGeometry.Etale
