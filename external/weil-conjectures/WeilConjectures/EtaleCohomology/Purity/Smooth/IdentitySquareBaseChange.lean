/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.Identity
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekLowerStarExchange
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarIdCoherence
public import WeilConjectures.SixFunctors.Etale.Derived.UpperShriekCanonicalMaps
public import WeilConjectures.SixFunctors.Etale.Derived.EtaleLowerShriekCompactificationBaseChange
public import WeilConjectures.CategoryTheory.DerivedCategory.AdjunctionIdIso
public import WeilConjectures.CategoryTheory.Adjunction.ProjectionTensorMap

/-!
# The exceptional base change along the identity square

For an isomorphism `g' : X' ⟶ X`, the exceptional base change `Lg'^* R(𝟙 X)^! ⟶ R(𝟙 X')^! Lg'^*`
of the square `g' ≫ 𝟙 = 𝟙 ≫ g'` is, through `R(𝟙)^! ≅ 𝟭`
(`AlgebraicGeometry.Etale.rightDerivedUpperShriekIdIso`), the identity
(`AlgebraicGeometry.Etale.rightDerivedUpperShriekBaseChangeMap_id_app_comp`). The proof passes to
the compact-support base change `Ex_!` through `R(𝟙)_! ≅ 𝟭`, to `Ex_*` through `R_! ≅ R_*`, and
finally to the counit of the derived adjunction `L(𝟙)^* ⊣ R(𝟙)_*`, which is identified with the
identity isomorphisms `L(𝟙)^* ≅ 𝟭` and `R(𝟙)_* ≅ 𝟭`
(`CategoryTheory.Adjunction.mapDerivedCategoryAdjunction_counit_app_of_iso`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

open Scheme

/-- The counit of the adjunction `F ⊣ 𝟭` transported from `𝟭 ⊣ 𝟭` along `e : F ≅ 𝟭`. -/
lemma _root_.CategoryTheory.Adjunction.ofNatIsoLeft_id_counit_app {C : Type*} [Category* C]
    {F : C ⥤ C} (e : F ≅ 𝟭 C) (Z : C) :
    (Adjunction.id.ofNatIsoLeft e.symm).counit.app Z = e.hom.app Z := by
  simp [Adjunction.ofNatIsoLeft_counit]

/-- The counit of `F ⊣ G` through the identification `G ≅ 𝟭` of right adjoints induced by
`e : F ≅ 𝟭`. -/
lemma _root_.CategoryTheory.Adjunction.rightAdjointUniq_ofNatIsoLeft_id_hom_app_counit
    {C : Type*} [Category* C] {F G : C ⥤ C} (adj : F ⊣ G) (e : F ≅ 𝟭 C) (Z : C) :
    F.map ((adj.rightAdjointUniq (Adjunction.id.ofNatIsoLeft e.symm)).hom.app Z) ≫
        e.hom.app Z = adj.counit.app Z := by
  have h := Adjunction.rightAdjointUniq_hom_app_counit adj (Adjunction.id.ofNatIsoLeft e.symm) Z
  rw [Adjunction.ofNatIsoLeft_id_counit_app] at h
  exact h

section Generic

variable {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C]
  [Abelian.HasKInjectiveResolutions C]

/-- The identity isomorphism `RG ≅ 𝟭` of the total right derived functor of an exact `G ≅ 𝟭`,
through `RG ≅ R(𝟭) ≅ D(𝟭) ≅ 𝟭` or through `RG ≅ D(G) ≅ D(𝟭) ≅ 𝟭`. -/
theorem rightDerivedFunctorNatIso_trans_eq (G : C ⥤ C) [G.Additive] [PreservesFiniteLimits G]
    [PreservesFiniteColimits G] (e : G ≅ 𝟭 C) :
    Functor.rightDerivedFunctorNatIso e ≪≫
        (𝟭 C).rightDerivedFunctorIsoMapDerivedCategory ≪≫
        Functor.mapDerivedCategoryIdIso C =
      G.rightDerivedFunctorIsoMapDerivedCategory ≪≫
        Functor.mapDerivedCategoryNatIso e ≪≫ Functor.mapDerivedCategoryIdIso C := by
  apply Iso.ext
  apply G.rightDerivedFunctor.rightDerived_ext G.rightDerivedFunctorUnit
    (HomotopyCategory.quasiIso C (.up ℤ))
  ext K : 2
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.whiskerLeft_app, ← Category.assoc]
  simp only [Functor.rightDerivedFunctorNatIso, Functor.rightDerivedFunctorNatTrans,
    Functor.rightDerivedNatTrans_app]
  have hf := congr_app G.rightDerivedFunctorIsoMapDerivedCategory_hom_fac K
  have hi := congr_app (𝟭 C).rightDerivedFunctorIsoMapDerivedCategory_hom_fac K
  dsimp only [NatTrans.comp_app, Functor.whiskerLeft_app] at hf hi
  rw [hf]
  simp only [Category.assoc]
  rw [reassoc_of% hi]
  simp only [Functor.whiskerRight_app]
  have hn := Functor.mapDerivedCategoryNatIso_fach e K
  simpa only [Category.assoc, Iso.hom_inv_id_app_assoc, Iso.inv_hom_id_app_assoc] using
    congrArg (fun t ↦ G.mapDerivedCategoryFactorsh.inv.app K ≫ t ≫
      (𝟭 C).mapDerivedCategoryFactorsh.inv.app K ≫
      (Functor.mapDerivedCategoryIdIso C).hom.app (DerivedCategory.Qh.obj K)) hn.symm

end Generic

variable (Λ : Type (u + 1)) [CommRing Λ]

section LowerStar

variable (X : Scheme.{u})

/-- The identity isomorphism `R(𝟙 X)_* ≅ 𝟭` used in
`AlgebraicGeometry.Etale.rightDerivedLowerShriekIdIso`. -/
noncomputable def rightDerivedLowerStarIdNatIso :
    R((𝟙 X)_*[ModuleCat.{u + 1} Λ]) ≅ 𝟭 _ :=
  Functor.rightDerivedFunctorNatIso (lowerStarId (ModuleCat.{u + 1} Λ) X) ≪≫
    (𝟭 _).rightDerivedFunctorIsoMapDerivedCategory ≪≫ Functor.mapDerivedCategoryIdIso _

/-- The counit of the derived adjunction `L(𝟙 X)^* ⊣ R(𝟙 X)_*` is the composite of the
identity isomorphisms `L(𝟙 X)^* ≅ 𝟭` and `R(𝟙 X)_* ≅ 𝟭`. -/
theorem leftDerivedUpperStarId_inv_app_comp_counit
    (M : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (leftDerivedUpperStarId (ModuleCat.{u + 1} Λ) X).inv.app
        ((R((𝟙 X)_*[ModuleCat.{u + 1} Λ])).obj M) ≫
      (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) (𝟙 X)).counit.app M =
    (rightDerivedLowerStarIdNatIso Λ X).hom.app M := by
  let G := lowerStar (ModuleCat.{u + 1} Λ) (𝟙 X)
  let : Limits.PreservesFiniteColimits G :=
    Limits.preservesFiniteColimits_of_natIso (lowerStarId (ModuleCat.{u + 1} Λ) X).symm
  let F := upperStar (ModuleCat.{u + 1} Λ) (𝟙 X)
  let adj := upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) (𝟙 X)
  let d := G.rightDerivedFunctorIsoMapDerivedCategory
  let i := Functor.mapDerivedCategoryNatIso (upperStarId (ModuleCat.{u + 1} Λ) X) ≪≫
    Functor.mapDerivedCategoryIdIso _
  have h := adj.mapDerivedCategoryAdjunction_counit_app_of_iso
    (upperStarId (ModuleCat.{u + 1} Λ) X) (lowerStarId (ModuleCat.{u + 1} Λ) X)
    (upperStarId_inv_app_counit_app (ModuleCat.{u + 1} Λ) X) M
  rw [rightDerivedLowerStarIdNatIso, rightDerivedFunctorNatIso_trans_eq]
  change _ = d.hom.app M ≫
    (Functor.mapDerivedCategoryNatIso (lowerStarId (ModuleCat.{u + 1} Λ) X) ≪≫
      Functor.mapDerivedCategoryIdIso _).hom.app M
  rw [← h]
  change _ = d.hom.app M ≫ i.inv.app (G.mapDerivedCategory.obj M) ≫
    (F.mapDerivedCategory.map (d.inv.app M) ≫
      F.leftDerivedFunctorIsoMapDerivedCategory.inv.app _ ≫ adj.derivedAdjunction.counit.app M)
  have hi : leftDerivedUpperStarId (ModuleCat.{u + 1} Λ) X =
      F.leftDerivedFunctorIsoMapDerivedCategory ≪≫ i := by
    apply Iso.ext
    simp [leftDerivedUpperStarId, Functor.leftDerivedFunctorNatIso, F, i]
  rw [hi]
  simp only [Iso.trans_inv, NatTrans.comp_app, Category.assoc]
  have hn := i.inv.naturality (d.inv.app M)
  dsimp only [Functor.id_map] at hn
  rw [← reassoc_of% hn]
  rw [Iso.hom_inv_id_app_assoc]
  rfl

/-- The counit of `L(𝟙 X)^* ⊣ R(𝟙 X)_*`, solved. -/
theorem derivedUpperStarLowerStarAdjunction_id_counit_app
    (M : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) (𝟙 X)).counit.app M =
      (leftDerivedUpperStarId (ModuleCat.{u + 1} Λ) X).hom.app
          ((R((𝟙 X)_*[ModuleCat.{u + 1} Λ])).obj M) ≫
        (rightDerivedLowerStarIdNatIso Λ X).hom.app M := by
  rw [← leftDerivedUpperStarId_inv_app_comp_counit, Iso.hom_inv_id_app_assoc]

end LowerStar

section Square

variable {X X' : Scheme.{u}} (g' : X' ⟶ X) (sq : CommSq g' (𝟙 X') (𝟙 X) g')

/-- The square isomorphism of the identity square is the identity isomorphism of the pullback. -/
theorem derivedSquareUpperStarIso_id_hom_app_comp
    (Z : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (derivedSquareUpperStarIso (ModuleCat.{u + 1} Λ) sq).hom.app Z ≫
        (L((g')^*[ModuleCat.{u + 1} Λ])).map
          ((leftDerivedUpperStarId (ModuleCat.{u + 1} Λ) X).hom.app Z) =
      (leftDerivedUpperStarId (ModuleCat.{u + 1} Λ) X').hom.app
        ((L((g')^*[ModuleCat.{u + 1} Λ])).obj Z) := by
  rw [derivedSquareUpperStarIso_hom_app_eq (ModuleCat.{u + 1} Λ) sq g' (Category.comp_id g').symm,
    Category.assoc, leftDerivedUpperStarComp_id_right_hom_app, Category.comp_id,
    ← cancel_epi ((leftDerivedUpperStarComp (ModuleCat.{u + 1} Λ) (𝟙 X') g' g'
      (Category.id_comp g').symm).hom.app Z), Iso.hom_inv_id_app,
    leftDerivedUpperStarComp_id_left_hom_app]

/-- **The derived base change map `Ex_*` of the identity square is the identity**, through
`R(𝟙)_* ≅ 𝟭`. -/
theorem derivedBaseChangeMap_id_app
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (derivedBaseChangeMap (ModuleCat.{u + 1} Λ) sq).app K =
      (L((g')^*[ModuleCat.{u + 1} Λ])).map ((rightDerivedLowerStarIdNatIso Λ X).hom.app K) ≫
        (rightDerivedLowerStarIdNatIso Λ X').inv.app ((L((g')^*[ModuleCat.{u + 1} Λ])).obj K) := by
  apply Adjunction.ext_of_comp_counit
    (adj := derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) (𝟙 X'))
  have hm : (L((𝟙 X')^*[ModuleCat.{u + 1} Λ])).map
        ((derivedBaseChangeMap (ModuleCat.{u + 1} Λ) sq).app K) ≫
        (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) (𝟙 X')).counit.app
          ((L((g')^*[ModuleCat.{u + 1} Λ])).obj K) =
      (derivedSquareUpperStarIso (ModuleCat.{u + 1} Λ) sq).hom.app
          ((R((𝟙 X)_*[ModuleCat.{u + 1} Λ])).obj K) ≫
        (L((g')^*[ModuleCat.{u + 1} Λ])).map
          ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) (𝟙 X)).counit.app K) :=
    mateEquiv_counit (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) (𝟙 X))
      (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) (𝟙 X'))
      (TwoSquare.mk _ _ _ _ (derivedSquareUpperStarIso (ModuleCat.{u + 1} Λ) sq).hom) K
  have hn := (leftDerivedUpperStarId (ModuleCat.{u + 1} Λ) X').hom.naturality
    ((rightDerivedLowerStarIdNatIso Λ X').inv.app ((L((g')^*[ModuleCat.{u + 1} Λ])).obj K))
  have hn' := (leftDerivedUpperStarId (ModuleCat.{u + 1} Λ) X').hom.naturality
    ((L((g')^*[ModuleCat.{u + 1} Λ])).map ((rightDerivedLowerStarIdNatIso Λ X).hom.app K))
  simp only [Functor.id_map] at hn hn'
  rw [hm, derivedUpperStarLowerStarAdjunction_id_counit_app,
    derivedUpperStarLowerStarAdjunction_id_counit_app, Functor.map_comp, Functor.map_comp,
    ← Category.assoc, derivedSquareUpperStarIso_id_hom_app_comp, Category.assoc,
    reassoc_of% hn, Iso.inv_hom_id_app]
  -- the identity is stated at `𝟭.obj _`
  erw [Category.comp_id]
  exact hn'.symm

end Square

section Shriek

variable [Finite Λ] {X X' : Scheme.{u}} (g' : X' ⟶ X) (sq : IsPullback g' (𝟙 X') (𝟙 X) g')

/-- **The compact-support base change `Ex_!` of the identity square is the identity**, through
`R(𝟙)_! ≅ 𝟭` (`AlgebraicGeometry.Etale.rightDerivedLowerShriekIdIso`). -/
theorem rightDerivedLowerShriekBaseChangeMap_id_app_comp
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (rightDerivedLowerShriekBaseChangeMap Λ sq).app K ≫
        (rightDerivedLowerShriekIdIso (ModuleCat.{u + 1} Λ) X').hom.app
          ((L((g')^*[ModuleCat.{u + 1} Λ])).obj K) =
      (L((g')^*[ModuleCat.{u + 1} Λ])).map
        ((rightDerivedLowerShriekIdIso (ModuleCat.{u + 1} Λ) X).hom.app K) := by
  -- iso-level unfoldings (syntactic after delta; the hom-level `rfl` times out in the kernel)
  have hI : rightDerivedLowerShriekIdIso (ModuleCat.{u + 1} Λ) X =
      rightDerivedLowerShriekIsoRightDerivedLowerStar (ModuleCat.{u + 1} Λ) (𝟙 X) ≪≫
        rightDerivedLowerStarIdNatIso Λ X := rfl
  have hI' : rightDerivedLowerShriekIdIso (ModuleCat.{u + 1} Λ) X' =
      rightDerivedLowerShriekIsoRightDerivedLowerStar (ModuleCat.{u + 1} Λ) (𝟙 X') ≪≫
        rightDerivedLowerStarIdNatIso Λ X' := rfl
  rw [hI, hI', Iso.trans_hom, Iso.trans_hom, NatTrans.comp_app, NatTrans.comp_app,
    ← Category.assoc, rightDerivedLowerShriekBaseChangeMap_app_comp_lowerStarIso,
    Category.assoc, derivedBaseChangeMap_id_app, Category.assoc, Iso.inv_hom_id_app]
  -- the identity is stated at `𝟭.obj _`
  erw [Category.comp_id]
  rw [Functor.map_comp]

-- The kernel cannot compare `(rightDerivedUpperShriekIdIso Λ Y).hom` with the `.hom` of its
-- unfolding
-- inside a composite (projections of the heavy derived adjunction get fully reduced, measured:
-- > 1.6M heartbeats), while the unfolding at the level of the isomorphism is immediate. So the
-- identification is unfolded once, by `rw`, and the lemmas below are stated in unfolded form.
/-- The unfolding of `AlgebraicGeometry.Etale.rightDerivedUpperShriekIdIso`. -/
theorem rightDerivedUpperShriekIdIso_eq (Y : Scheme.{u}) :
    rightDerivedUpperShriekIdIso Λ Y =
      (rightDerivedUpperShriekAdjunction Λ (𝟙 Y)).rightAdjointUniq
        (Adjunction.id.ofNatIsoLeft (rightDerivedLowerShriekIdIso (ModuleCat.{u + 1} Λ) Y).symm) :=
  rfl

/-- The counit of `R(𝟙 X)_! ⊣ R(𝟙 X)^!` is the composite of the identity isomorphisms. -/
theorem rightDerivedUpperShriekAdjunction_id_counit_app (Y : Scheme.{u})
    (Z : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (R(𝟙 Y)_![ModuleCat.{u + 1} Λ]).map
        (((rightDerivedUpperShriekAdjunction Λ (𝟙 Y)).rightAdjointUniq
          (Adjunction.id.ofNatIsoLeft
            (rightDerivedLowerShriekIdIso (ModuleCat.{u + 1} Λ) Y).symm)).hom.app Z) ≫
        (rightDerivedLowerShriekIdIso (ModuleCat.{u + 1} Λ) Y).hom.app Z =
      (rightDerivedUpperShriekAdjunction Λ (𝟙 Y)).counit.app Z :=
  Adjunction.rightAdjointUniq_ofNatIsoLeft_id_hom_app_counit
    (rightDerivedUpperShriekAdjunction Λ (𝟙 Y))
    (rightDerivedLowerShriekIdIso (ModuleCat.{u + 1} Λ) Y) Z

/-- **The exceptional base change of the identity square is the identity**, through
`R(𝟙)^! ≅ 𝟭` (`AlgebraicGeometry.Etale.rightDerivedUpperShriekIdIso`): the hypothesis `H2` of
`AlgebraicGeometry.Etale.IsoSquare.compEqId_baseChange`. -/
theorem rightDerivedUpperShriekBaseChangeMap_id_app_comp
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (rightDerivedUpperShriekBaseChangeMap Λ sq).app K ≫
        (rightDerivedUpperShriekIdIso Λ X').hom.app ((L((g')^*[ModuleCat.{u + 1} Λ])).obj K) =
      (L((g')^*[ModuleCat.{u + 1} Λ])).map ((rightDerivedUpperShriekIdIso Λ X).hom.app K) := by
  rw [rightDerivedUpperShriekIdIso_eq, rightDerivedUpperShriekIdIso_eq]
  have hEx := isIso_rightDerivedLowerShriekBaseChangeMap Λ sq
  have key : (rightDerivedUpperShriekBaseChangeMap Λ sq).app K =
      (L((g')^*[ModuleCat.{u + 1} Λ])).map
        (((rightDerivedUpperShriekAdjunction Λ (𝟙 X)).rightAdjointUniq
          (Adjunction.id.ofNatIsoLeft
            (rightDerivedLowerShriekIdIso (ModuleCat.{u + 1} Λ) X).symm)).hom.app K) ≫
        ((rightDerivedUpperShriekAdjunction Λ (𝟙 X')).rightAdjointUniq
          (Adjunction.id.ofNatIsoLeft
            (rightDerivedLowerShriekIdIso (ModuleCat.{u + 1} Λ) X').symm)).inv.app
          ((L((g')^*[ModuleCat.{u + 1} Λ])).obj K) := by
    apply Adjunction.ext_of_comp_counit (adj := rightDerivedUpperShriekAdjunction Λ (𝟙 X'))
    have hm : (R(𝟙 X')_![ModuleCat.{u + 1} Λ]).map
          ((rightDerivedUpperShriekBaseChangeMap Λ sq).app K) ≫
          (rightDerivedUpperShriekAdjunction Λ (𝟙 X')).counit.app
            ((L((g')^*[ModuleCat.{u + 1} Λ])).obj K) =
        (inv (rightDerivedLowerShriekBaseChangeMap Λ sq)).app ((R(𝟙 X)^![Λ]).obj K) ≫
          (L((g')^*[ModuleCat.{u + 1} Λ])).map
            ((rightDerivedUpperShriekAdjunction Λ (𝟙 X)).counit.app K) :=
      mateEquiv_counit (rightDerivedUpperShriekAdjunction Λ (𝟙 X))
        (rightDerivedUpperShriekAdjunction Λ (𝟙 X'))
        (inv (rightDerivedLowerShriekBaseChangeMap Λ sq)) K
    have hnat := (rightDerivedLowerShriekBaseChangeMap Λ sq).naturality
      (((rightDerivedUpperShriekAdjunction Λ (𝟙 X)).rightAdjointUniq
          (Adjunction.id.ofNatIsoLeft
            (rightDerivedLowerShriekIdIso (ModuleCat.{u + 1} Λ) X).symm)).hom.app K)
    simp only [Functor.comp_map] at hnat
    rw [hm, ← rightDerivedUpperShriekAdjunction_id_counit_app Λ X K, Functor.map_comp,
      ← rightDerivedLowerShriekBaseChangeMap_id_app_comp Λ g' sq K, reassoc_of% hnat,
      ← NatTrans.comp_app_assoc, IsIso.inv_hom_id, NatTrans.id_app, Category.id_comp,
      ← rightDerivedUpperShriekAdjunction_id_counit_app Λ X'
        ((L((g')^*[ModuleCat.{u + 1} Λ])).obj K)]
    simp only [Functor.map_comp, Category.assoc]
    rw [← Functor.map_comp_assoc (R(𝟙 X')_![ModuleCat.{u + 1} Λ])
      (((rightDerivedUpperShriekAdjunction Λ (𝟙 X')).rightAdjointUniq
          (Adjunction.id.ofNatIsoLeft
            (rightDerivedLowerShriekIdIso (ModuleCat.{u + 1} Λ) X').symm)).inv.app _)
      (((rightDerivedUpperShriekAdjunction Λ (𝟙 X')).rightAdjointUniq
          (Adjunction.id.ofNatIsoLeft
            (rightDerivedLowerShriekIdIso (ModuleCat.{u + 1} Λ) X').symm)).hom.app _),
      Iso.inv_hom_id_app, CategoryTheory.Functor.map_id, Category.id_comp]
  rw [key, Category.assoc, Iso.inv_hom_id_app]
  erw [Category.comp_id]

end Shriek

end AlgebraicGeometry.Etale
