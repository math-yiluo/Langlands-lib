/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarCoherence
public import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.FullyFaithful
public import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
import WeilConjectures.SixFunctors.Etale.LowerShriek.Proper
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusExact

/-!
# Direct image from an open and closed section

Source: blueprint, sec-smooth-purity/sk-def-sf-operations,
lemma proposition-construction-independence-rf-shriek--7
(blueprint: proposition-construction-independence-rf-shriek--7).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Etale

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

/-- Exact right adjoints with invertible counit retain an invertible derived counit.
On localized bounded below complexes use `Adjunction.derivedPlus_counit_app_fac`,
then transport along the essential-surjectivity isomorphism of localization. -/
private theorem exact_derived_counit_isIso
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D] [EnoughInjectives D]
    {L : C ⥤ D} {R : D ⥤ C} [L.Additive] [R.Additive]
    [Limits.PreservesFiniteLimits L] [Limits.PreservesFiniteColimits L]
    [Limits.PreservesFiniteLimits R] [Limits.PreservesFiniteColimits R]
    (adj : L ⊣ R) [IsIso adj.counit] : IsIso adj.derivedPlus.counit := by
  have hc (N : HomotopyCategory.Plus D) :
      IsIso (adj.derivedPlus.counit.app (DerivedCategory.Plus.Qh.obj N)) := by
    have : R.Full := adj.fullyFaithfulROfIsIsoCounit.full
    have : R.Faithful := adj.fullyFaithfulROfIsIsoCounit.faithful
    have : IsIso adj.mapHomotopyCategoryPlus.counit := inferInstance
    have : IsIso R.rightDerivedFunctorPlusUnith :=
      Functor.isIso_rightDerivedFunctorPlusUnit R
    have : IsIso (R.rightDerivedFunctorPlusUnith.app N) :=
      NatIso.isIso_app_of_isIso R.rightDerivedFunctorPlusUnith N
    have : IsIso (L.mapDerivedCategoryPlus.map (R.rightDerivedFunctorPlusUnith.app N)) :=
      Functor.map_isIso _ _
    have : IsIso (L.mapDerivedCategoryPlus.map (R.rightDerivedFunctorPlusUnith.app N) ≫
        adj.derivedPlus.counit.app (DerivedCategory.Plus.Qh.obj N)) := by
      rw [adj.derivedPlus_counit_app_fac]
      infer_instance
    exact IsIso.of_isIso_comp_left
      (L.mapDerivedCategoryPlus.map (R.rightDerivedFunctorPlusUnith.app N)) _
  have : ∀ K, IsIso (adj.derivedPlus.counit.app K) := by
    intro K
    have := hc (DerivedCategory.Plus.Qh.objPreimage K)
    exact (NatTrans.isIso_app_iff_of_iso adj.derivedPlus.counit
      (DerivedCategory.Plus.Qh.objObjPreimageIso K)).mp this
  exact NatIso.isIso_of_isIso_app _

/-- Restriction to an open and closed section gives `Rp_* s_! ≅ id` on bounded below
étale derived categories with coefficients in any commutative ring. Source: blueprint,
part-six-operations/sec-six-functors-basics/sec-brown-construction/
sec-construction-of-rf/sk-prop-sf-comp-coherence, lemma
proposition-construction-independence-rf-shriek--7 (blueprint:
proposition-construction-independence-rf-shriek--7).

The equation characterizes the canonical isomorphism: after the unit identifying `K`
with `s^* s_! K`, its component is restriction along `s`, namely the derived unit for
`s^* ⊣ s_*`, followed by `Rp_* Rs_* ≅ R(ps)_* ≅ id`.

Proof: The proved clopen comparison identifies `s_!` with `s_*`, so `s_*` is exact.
The counit of `s^* ⊣ s_*` is invertible, and remains so after passing to bounded below
derived categories: on the image of a bounded below complex this follows from the counit
factorization and exactness of `s_*`; essential surjectivity of localization handles
all objects. Thus `Rs_*` is fully faithful. Since the exact derived functor of `s_!`
is isomorphic to `Rs_*`, the derived unit is invertible on its image. Apply `Rp_*`
to this unit, then the composition isomorphism `Rp_* Rs_* ≅ R(ps)_* ≅ id`.
Finally invert the derived unit of `s_! ⊣ s^*`. This constructs the isomorphism with
exactly the asserted canonical-map equation. -/
theorem clopenSectionDirectImage_of_commRing (Λ : Type (u + 1)) [CommRing Λ]
    {X V : Scheme.{u}} (p : V ⟶ X) (s : X ⟶ V) [IsOpenImmersion s]
    (hs : IsClosed (Set.range s.base)) (hsp : s ≫ p = 𝟙 X) :
    ∃ e : (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) s).mapDerivedCategoryPlus ⋙
        rightDerivedLowerStarPlus (ModuleCat.{u + 1} Λ) p ≅
          𝟭 (DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))),
      ∀ K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)),
        @Eq
          (((rightDerivedLowerStarPlus (ModuleCat.{u + 1} Λ) p).obj
            ((openImmersionLowerShriek (ModuleCat.{u + 1} Λ) s).mapDerivedCategoryPlus.obj K)) ⟶
          ((upperStar (ModuleCat.{u + 1} Λ) s).mapDerivedCategoryPlus.obj
            ((openImmersionLowerShriek (ModuleCat.{u + 1} Λ) s).mapDerivedCategoryPlus.obj K)))
          (e.hom.app K ≫
            (Functor.mapDerivedCategoryPlusIdIso
              (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))).inv.app K ≫
            (Functor.mapDerivedCategoryPlusNatIso
              (asIso (openImmersionLowerShriekUpperStarAdjunction
                (ModuleCat.{u + 1} Λ) s).unit)).hom.app K ≫
            (Functor.mapDerivedCategoryPlusCompIso
              (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) s)
              (upperStar (ModuleCat.{u + 1} Λ) s)).hom.app K)
          ((rightDerivedLowerStarPlus (ModuleCat.{u + 1} Λ) p).map
            ((Adjunction.derivedPlus
              (L := upperStar (ModuleCat.{u + 1} Λ) s)
              (R := lowerStar (ModuleCat.{u + 1} Λ) s)
              (upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) s)).unit.app
              ((openImmersionLowerShriek (ModuleCat.{u + 1} Λ) s).mapDerivedCategoryPlus.obj K)) ≫
          (@Functor.rightDerivedFunctorPlusCompIso' _ _ _ _ _ _ _ _ _ _ _ _ _ _
            (lowerStar (ModuleCat.{u + 1} Λ) s) (lowerStar (ModuleCat.{u + 1} Λ) p) _ _ _ _
            (Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
              (upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) s))
            (lowerStarComp (ModuleCat.{u + 1} Λ) s p (𝟙 X) hsp.symm)).hom.app
              ((upperStar (ModuleCat.{u + 1} Λ) s).mapDerivedCategoryPlus.obj
                ((openImmersionLowerShriek (ModuleCat.{u + 1} Λ) s).mapDerivedCategoryPlus.obj K)) ≫
          (lowerStarIdDerivedPlus (ModuleCat.{u + 1} Λ) X).hom.app
            ((upperStar (ModuleCat.{u + 1} Λ) s).mapDerivedCategoryPlus.obj
              ((openImmersionLowerShriek (ModuleCat.{u + 1} Λ) s).mapDerivedCategoryPlus.obj
                K))) := by
  let A := ModuleCat.{u + 1} Λ
  let J := openImmersionLowerShriek A s
  let R := lowerStar A s
  let U := upperStar A s
  let adj := upperStarLowerStarAdjunction A s
  have hcmp : IsIso (openImmersionLowerShriekToLowerStar A s) :=
    isIso_openImmersionLowerShriekToLowerStar_of_isClosed_range A s hs
  let eJR : J ≅ R := asIso (openImmersionLowerShriekToLowerStar A s)
  have : Limits.PreservesFiniteColimits R :=
    Limits.preservesFiniteColimits_of_natIso eJR
  have : IsIso adj.derivedPlus.counit := exact_derived_counit_isIso adj
  have : R.rightDerivedFunctorPlus.Full := adj.derivedPlus.fullyFaithfulROfIsIsoCounit.full
  have : R.rightDerivedFunctorPlus.Faithful :=
    adj.derivedPlus.fullyFaithfulROfIsIsoCounit.faithful
  let eJRd : J.mapDerivedCategoryPlus ≅ R.rightDerivedFunctorPlus :=
    Functor.mapDerivedCategoryPlusNatIso eJR ≪≫
      R.rightDerivedFunctorPlusIsoMapDerivedCategoryPlus.symm
  have hη (K) : IsIso (adj.derivedPlus.unit.app (J.mapDerivedCategoryPlus.obj K)) :=
    adj.derivedPlus.isIso_unit_app_of_iso (eJRd.app K)
  have hRinj : R.PreservesInjectiveObjects :=
    Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms adj
  let P := rightDerivedLowerStarPlus A p
  let c : R.rightDerivedFunctorPlus ⋙ P ≅ 𝟭 _ :=
    Functor.rightDerivedFunctorPlusCompIso' R (lowerStar A p)
      (lowerStarComp A s p (𝟙 X) hsp.symm) ≪≫ lowerStarIdDerivedPlus A X
  let t : J.mapDerivedCategoryPlus ⋙ P ⟶ J.mapDerivedCategoryPlus ⋙
      U.mapDerivedCategoryPlus :=
    Functor.whiskerLeft J.mapDerivedCategoryPlus
        (Functor.whiskerRight adj.derivedPlus.unit P) ≫
      Functor.whiskerLeft J.mapDerivedCategoryPlus
        (Functor.associator U.mapDerivedCategoryPlus R.rightDerivedFunctorPlus P).hom ≫
      Functor.whiskerLeft J.mapDerivedCategoryPlus
        (Functor.whiskerLeft U.mapDerivedCategoryPlus c.hom) ≫
      Functor.whiskerLeft J.mapDerivedCategoryPlus
        (Functor.rightUnitor U.mapDerivedCategoryPlus).hom
  have ht (K) : IsIso (t.app K) := by
    have := hη K
    dsimp [t]
    infer_instance
  have : IsIso t := NatIso.isIso_of_isIso_app t
  let a : 𝟭 _ ≅ J.mapDerivedCategoryPlus ⋙ U.mapDerivedCategoryPlus :=
    (Functor.mapDerivedCategoryPlusIdIso _).symm ≪≫
      Functor.mapDerivedCategoryPlusNatIso
        (asIso (openImmersionLowerShriekUpperStarAdjunction A s).unit) ≪≫
      Functor.mapDerivedCategoryPlusCompIso J U
  refine ⟨asIso t ≪≫ a.symm, ?_⟩
  intro K
  change (t.app K ≫ a.inv.app K) ≫ _ = _
  have ha : a.hom.app K =
      (Functor.mapDerivedCategoryPlusIdIso _).inv.app K ≫
        (Functor.mapDerivedCategoryPlusNatIso
          (asIso (openImmersionLowerShriekUpperStarAdjunction A s).unit)).hom.app K ≫
        (Functor.mapDerivedCategoryPlusCompIso J U).hom.app K := rfl
  rw [← ha, Category.assoc, Iso.inv_hom_id_app, Category.comp_id]
  dsimp [t, c, P, U, R, J, adj, A]
  simp only [Category.id_comp, Category.comp_id]

/-- The finite-coefficient case of `clopenSectionDirectImage_of_commRing`, kept for its existing
users. Source: blueprint, lemma proposition-construction-independence-rf-shriek--7
(blueprint: proposition-construction-independence-rf-shriek--7). -/
theorem clopenSectionDirectImage (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {X V : Scheme.{u}} (p : V ⟶ X) (s : X ⟶ V) [IsOpenImmersion s]
    (hs : IsClosed (Set.range s.base)) (hsp : s ≫ p = 𝟙 X) :
    ∃ e : (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) s).mapDerivedCategoryPlus ⋙
        rightDerivedLowerStarPlus (ModuleCat.{u + 1} Λ) p ≅
          𝟭 (DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))),
      ∀ K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)),
        @Eq
          (((rightDerivedLowerStarPlus (ModuleCat.{u + 1} Λ) p).obj
            ((openImmersionLowerShriek (ModuleCat.{u + 1} Λ) s).mapDerivedCategoryPlus.obj K)) ⟶
          ((upperStar (ModuleCat.{u + 1} Λ) s).mapDerivedCategoryPlus.obj
            ((openImmersionLowerShriek (ModuleCat.{u + 1} Λ) s).mapDerivedCategoryPlus.obj K)))
          (e.hom.app K ≫
            (Functor.mapDerivedCategoryPlusIdIso
              (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))).inv.app K ≫
            (Functor.mapDerivedCategoryPlusNatIso
              (asIso (openImmersionLowerShriekUpperStarAdjunction
                (ModuleCat.{u + 1} Λ) s).unit)).hom.app K ≫
            (Functor.mapDerivedCategoryPlusCompIso
              (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) s)
              (upperStar (ModuleCat.{u + 1} Λ) s)).hom.app K)
          ((rightDerivedLowerStarPlus (ModuleCat.{u + 1} Λ) p).map
            ((Adjunction.derivedPlus
              (L := upperStar (ModuleCat.{u + 1} Λ) s)
              (R := lowerStar (ModuleCat.{u + 1} Λ) s)
              (upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) s)).unit.app
              ((openImmersionLowerShriek (ModuleCat.{u + 1} Λ) s).mapDerivedCategoryPlus.obj K)) ≫
          (@Functor.rightDerivedFunctorPlusCompIso' _ _ _ _ _ _ _ _ _ _ _ _ _ _
            (lowerStar (ModuleCat.{u + 1} Λ) s) (lowerStar (ModuleCat.{u + 1} Λ) p) _ _ _ _
            (Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
              (upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) s))
            (lowerStarComp (ModuleCat.{u + 1} Λ) s p (𝟙 X) hsp.symm)).hom.app
              ((upperStar (ModuleCat.{u + 1} Λ) s).mapDerivedCategoryPlus.obj
                ((openImmersionLowerShriek (ModuleCat.{u + 1} Λ) s).mapDerivedCategoryPlus.obj K)) ≫
          (lowerStarIdDerivedPlus (ModuleCat.{u + 1} Λ) X).hom.app
            ((upperStar (ModuleCat.{u + 1} Λ) s).mapDerivedCategoryPlus.obj
              ((openImmersionLowerShriek (ModuleCat.{u + 1} Λ) s).mapDerivedCategoryPlus.obj
                K))) :=
  clopenSectionDirectImage_of_commRing Λ p s hs hsp

end AlgebraicGeometry.Etale
