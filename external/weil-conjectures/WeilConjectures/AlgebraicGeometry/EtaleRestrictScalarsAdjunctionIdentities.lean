/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.EtaleRestrictScalarsFunctorComparisons

/-! # Coefficient compatibility of derived étale adjunctions -/

@[expose] public section

universe u

open CategoryTheory
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale

-- The exact-functor composition and natural-isomorphism factorization formulas
-- compute the transported square on the image of the homotopy category.
private theorem square_fac
    {A B C D : Type*} [Category* A] [Category* B] [Category* C] [Category* D]
    [Abelian A] [Abelian B] [Abelian C] [Abelian D]
    [HasDerivedCategory A] [HasDerivedCategory B] [HasDerivedCategory C]
    [HasDerivedCategory D]
    (G : A ⥤ C) (L : A ⥤ B) (L' : C ⥤ D) (H : B ⥤ D)
    [G.Additive] [L.Additive] [L'.Additive] [H.Additive]
    [Limits.PreservesFiniteLimits G] [Limits.PreservesFiniteColimits G]
    [Limits.PreservesFiniteLimits L] [Limits.PreservesFiniteColimits L]
    [Limits.PreservesFiniteLimits L'] [Limits.PreservesFiniteColimits L']
    [Limits.PreservesFiniteLimits H] [Limits.PreservesFiniteColimits H]
    (e : G ⋙ L' ≅ L ⋙ H) (K : HomotopyCategory.Plus A) :
    ((Functor.mapDerivedCategoryPlusCompIso G L').symm ≪≫
      Functor.mapDerivedCategoryPlusNatIso e ≪≫
      Functor.mapDerivedCategoryPlusCompIso L H).hom.app (DerivedCategory.Plus.Qh.obj K) ≫
        H.mapDerivedCategoryPlus.map (L.mapDerivedCategoryPlusFactorsh.hom.app K) ≫
        H.mapDerivedCategoryPlusFactorsh.hom.app (L.mapHomotopyCategoryPlus.obj K) =
      L'.mapDerivedCategoryPlus.map (G.mapDerivedCategoryPlusFactorsh.hom.app K) ≫
        L'.mapDerivedCategoryPlusFactorsh.hom.app (G.mapHomotopyCategoryPlus.obj K) ≫
        DerivedCategory.Plus.Qh.map ((NatTrans.mapHomotopyCategoryPlus e.hom).app K) := by
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Category.assoc]
  rw [Functor.mapDerivedCategoryPlusCompIso_hom_app_factorsh,
    Functor.mapDerivedCategoryPlusNatIso_hom_app_factorsh]
  rw [← Functor.mapDerivedCategoryPlusCompIso_hom_app_factorsh G L' K]
  simp only [Category.assoc]
  erw [Iso.inv_hom_id_app_assoc]

-- The right-derived universal property identifies two transformations once their
-- composites with the right-derived unit agree. The existing derived-mate formula
-- reduces that comparison to the preceding factorization.
private theorem derived_mate_eq
    {A B C D : Type*} [Category* A] [Category* B] [Category* C] [Category* D]
    [Abelian A] [Abelian B] [Abelian C] [Abelian D]
    [HasDerivedCategory A] [HasDerivedCategory B] [HasDerivedCategory C]
    [HasDerivedCategory D]
    (G : A ⥤ C) (L : A ⥤ B) (L' : C ⥤ D) (H : B ⥤ D)
    [G.Additive] [L.Additive] [L'.Additive] [H.Additive]
    [Limits.PreservesFiniteLimits G] [Limits.PreservesFiniteColimits G]
    [Limits.PreservesFiniteLimits L] [Limits.PreservesFiniteColimits L]
    [Limits.PreservesFiniteLimits L'] [Limits.PreservesFiniteColimits L']
    [Limits.PreservesFiniteLimits H] [Limits.PreservesFiniteColimits H]
    (R : B ⥤ A) (R' : D ⥤ C)
    [R.Additive] [R'.Additive] [EnoughInjectives B] [EnoughInjectives D]
    (adj : L ⊣ R) (adj' : L' ⊣ R') (e : G ⋙ L' ≅ L ⋙ H) :
    (mateEquiv adj.derivedPlus adj'.derivedPlus
      (TwoSquare.mk _ _ _ _ ((Functor.mapDerivedCategoryPlusCompIso G L').symm ≪≫
        Functor.mapDerivedCategoryPlusNatIso e ≪≫
        Functor.mapDerivedCategoryPlusCompIso L H).hom)) =
      Functor.rightDerivedFunctorPlusBaseChange
        (mateEquiv adj adj' (TwoSquare.mk _ _ _ _ e.hom)) := by
  refine Functor.rightDerived_ext (R.rightDerivedFunctorPlus ⋙ G.mapDerivedCategoryPlus)
    (Functor.whiskerRight R.rightDerivedFunctorPlusUnith G.mapDerivedCategoryPlus ≫
      (Functor.associator _ _ _).hom) (HomotopyCategory.Plus.quasiIso B) _ _ _ ?_
  rw [Functor.rightDerivedFunctorPlusBaseChange_fac]
  ext K : 2
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.associator_hom_app,
    Category.comp_id, Functor.whiskerLeft_app]
  rw [Adjunction.derivedPlus_mateEquiv_app_fac adj adj' _ _ (square_fac G L L' H e)]
  simp [Functor.rightDerivedFunctorPlusBaseChangeAux,
    Functor.mapHomotopyCategoryPlusCompIso_refl_hom_app,
    Functor.mapHomotopyCategoryPlusCompIso_refl_inv_app]

namespace AlgebraicGeometry.Etale

-- Taking mates twice turns the inverse-image comparison into the identity by
-- left-adjoint uniqueness. The same double mate of the sectionwise identity is
-- the restriction/coextension triangle identity, evaluated on sections.
private theorem underived_mate
    {Λ Λ' : Type (u + 1)} [CommRing Λ] [CommRing Λ'] (φ : Λ →+* Λ')
    {Z W : Scheme.{u}} (f : Z ⟶ W) :
    (mateEquiv (upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ') f)
      (upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f)
      (TwoSquare.mk _ _ _ _ (upperStarRestrictScalarsIsoSheaf φ f).hom)) =
        (lowerStarRestrictScalarsIso φ f).hom := by
  apply (mateEquiv (Sheaf.restrictCoextendScalarsAdj Z.smallEtaleTopology φ)
    (Sheaf.restrictCoextendScalarsAdj W.smallEtaleTopology φ)).injective
  rw [iterated_mateEquiv_conjugateEquiv]
  simp only [upperStarRestrictScalarsIsoSheaf, Adjunction.leftAdjointUniq, Iso.symm_hom,
    conjugateIsoEquiv_symm_apply_inv, Iso.refl_inv, TwoSquare.mk]
  erw [Equiv.apply_symm_apply]
  ext M ⟨U⟩ x
  exact congrArg (fun t ↦ t.hom x)
    ((ModuleCat.restrictCoextendScalarsAdj.{u + 1, u + 1, u + 1} φ).right_triangle_components
      (M.obj.obj (Opposite.op ((MorphismProperty.Over.pullback @Etale ⊤ f).obj U)))).symm

-- Derivation preserves the preceding mate relation, with exactly the comparison
-- maps used to define the source and target coefficient isomorphisms.
private theorem derived_mate
    {Λ Λ' : Type (u + 1)} [CommRing Λ] [CommRing Λ'] (φ : Λ →+* Λ')
    {Z W : Scheme.{u}} (f : Z ⟶ W) :
    (mateEquiv (upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ') f).derivedPlus
      (upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f).derivedPlus
      (TwoSquare.mk _ _ _ _ (derivedUpperStarRestrictScalarsIso φ f).hom)) =
        (derivedLowerStarRestrictScalarsIso φ f).hom := by
  change _ = derivedLowerStarRestrictScalarsMap φ f
  unfold derivedLowerStarRestrictScalarsMap
  rw [← underived_mate φ f]
  exact derived_mate_eq _ _ _ _ _ _
    (upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ') f)
    (upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f)
    (upperStarRestrictScalarsIsoSheaf φ f)

/-- The canonical coefficient comparisons preserve the unit and counit of a single
bounded below inverse-image/direct-image adjunction.

Source: Stacks Project, Remark 21.19.3, Tag 07A7 (adjunction construction), and
Lemma 21.20.7(3), Tag 0D6J (natural derived direct-image comparison).
Proof: before derivation, direct image commutes with restriction sectionwise. The
inverse-image comparison is the uniqueness isomorphism of the two left adjoints
to direct image followed by coextension. Transpose through the restriction/coextension
adjunction: the unit and counit identities of leftAdjointUniq give precisely the two
identities for inverse image and direct image. Derive those identities on bounded below
complexes. The exact-functor composition isomorphisms transport the inverse-image
comparison; the right-derived direct-image comparison is characterized by its
compatibility with the right-derived units. On an injective resolution, restriction
produces a direct-image-acyclic complex, so this comparison is invertible and the
underived identities give the asserted identities after localization. Every bounded
below object is isomorphic to such a resolution. Naturality transports the identities
to the given objects. This argument concerns one adjunction, without any square or
base-change morphism.
(blueprint: lem-sbc-restrict-scalars-derived-adjunction-identities) -/
theorem derivedRestrictScalars_adjunction_identities
    {Λ Λ' : Type (u + 1)} [CommRing Λ] [CommRing Λ'] (φ : Λ →+* Λ')
    {Z W : Scheme.{u}} (f : Z ⟶ W) :
    (∀ M : DerivedCategory.Plus (Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} Λ')),
      (derivedUpperStarLowerStarAdjunctionPlus (ModuleCat.{u + 1} Λ) f).unit.app
          ((Sheaf.restrictScalars W.smallEtaleTopology φ).mapDerivedCategoryPlus.obj M) ≫
        (derivedBaseChangeTargetRestrictScalarsIso φ f f M).hom =
      (Sheaf.restrictScalars W.smallEtaleTopology φ).mapDerivedCategoryPlus.map
        ((derivedUpperStarLowerStarAdjunctionPlus (ModuleCat.{u + 1} Λ') f).unit.app M)) ∧
    (∀ N : DerivedCategory.Plus (Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} Λ')),
      (derivedBaseChangeSourceRestrictScalarsIso φ f f N).hom ≫
        (Sheaf.restrictScalars Z.smallEtaleTopology φ).mapDerivedCategoryPlus.map
          ((derivedUpperStarLowerStarAdjunctionPlus (ModuleCat.{u + 1} Λ') f).counit.app N) =
      (derivedUpperStarLowerStarAdjunctionPlus (ModuleCat.{u + 1} Λ) f).counit.app
        ((Sheaf.restrictScalars Z.smallEtaleTopology φ).mapDerivedCategoryPlus.obj N)) := by
  simp only [derivedUpperStarLowerStarAdjunctionPlus,
    Adjunction.derivedAdjunctionPlus_eq_derivedPlus]
  constructor
  · intro M
    have h := unit_mateEquiv
      (upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ') f).derivedPlus
      (upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f).derivedPlus
      (TwoSquare.mk _ _ _ _ (derivedUpperStarRestrictScalarsIso φ f).hom) M
    have hm := derived_mate φ f
    rw [hm] at h
    dsimp only [TwoSquare.mk, Functor.id_obj] at h
    simp only [derivedBaseChangeTargetRestrictScalarsIso, Iso.trans_hom,
      Functor.mapIso_hom, Iso.app_hom, Iso.symm_hom]
    rw [← reassoc_of% h]
    simp
  · intro N
    have h := mateEquiv_counit
      (upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ') f).derivedPlus
      (upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f).derivedPlus
      (TwoSquare.mk _ _ _ _ (derivedUpperStarRestrictScalarsIso φ f).hom) N
    have hm := derived_mate φ f
    rw [hm] at h
    dsimp only [TwoSquare.mk, Functor.id_obj] at h
    simp only [derivedBaseChangeSourceRestrictScalarsIso, Iso.trans_hom,
      Functor.mapIso_hom, Iso.app_hom, Iso.symm_hom, Category.assoc]
    rw [← h, ← Category.assoc, ← Functor.map_comp]
    simp

end AlgebraicGeometry.Etale
