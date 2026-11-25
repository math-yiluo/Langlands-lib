/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Strict.Local.StrictLocalInjectiveSourceComparison
public import WeilConjectures.SixFunctors.BaseChange.Square
public import Mathlib.Algebra.Homology.Localization

import all Mathlib.Algebra.Homology.Localization

/-! # Target localization and derived-unit transport

Source: Stacks Project, Tag 03Q9, final injective-complex paragraph.
(blueprint: lem-weil-pbc-injective-exchange-target-transport).
-/

/- This original-model counterpart follows the proved calculation in
WeilConjectures.AlgebraicGeometry.InjectiveExchangeTargetTransport.
The spectrum and structure morphism are those of the small coordinate-ring colimit. -/

@[expose] public section

universe v

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry

namespace AlgebraicGeometry.Etale

private lemma assemble_transport {A B : Type*} [Category A] [Category B]
    (I : A ⥤ B) {X₀ X₁ X₂ X₃ X₄ : A} {W Y₁ Y₂ Y₃ Y₄ : B}
    (a : W ⟶ I.obj X₀) (b₁ : X₀ ⟶ X₁) (b₂ : X₁ ⟶ X₂)
    (c₁ : X₂ ⟶ X₃) (c₂ : X₃ ⟶ X₄)
    (d₁ : W ⟶ Y₁) (d₂ : Y₁ ⟶ I.obj X₂)
    (r₁ : I.obj X₂ ⟶ Y₂) (r₂ : Y₂ ⟶ Y₃) (r₃ : Y₃ ⟶ Y₄) (r₄ : Y₄ ⟶ I.obj X₄)
    (hp : a ≫ I.map (b₁ ≫ b₂) = d₁ ≫ d₂)
    (ht : I.map (c₁ ≫ c₂) = r₁ ≫ r₂ ≫ r₃ ≫ r₄) :
    a ≫ I.map (b₁ ≫ b₂ ≫ c₁ ≫ c₂) = d₁ ≫ d₂ ≫ r₁ ≫ r₂ ≫ r₃ ≫ r₄ := by
  have h := congrArg (fun z ↦ z ≫ I.map (c₁ ≫ c₂)) hp
  conv_rhs at h => rw [ht]
  simpa only [Functor.map_comp, Category.assoc] using h

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- Localization of the exchange prefix on a bounded-below complex.
Source: Stacks Project, Tag 03Q9, final injective-complex paragraph, and the
exact localization comparisons.
(blueprint: lem-weil-pbc-injective-exchange-target-transport).
Proof: apply the inclusion to the two factors. Its image of the exact U
comparison is mapDerivedCategoryFactorsh. At a quotient complex this is the
complex comparison, since mapHomotopyCategoryFactors is the identity.
Cancel its hom against the leading inverse. The image of the bounded-below
localized exchange is Qh of the homotopy quotient of its complex map.
Naturality of quotientCompQhIso identifies that map with Q of the complex
map followed by the inverse quotient comparison on the target. -/
private theorem exchange_localization_prefix
    {C : Type*} {B : Type*} {D : Type*} {E : Type*}
    [Category C] [Category B] [Category D] [Category E]
    [Abelian C] [Abelian B] [Abelian D] [Abelian E]
    [HasDerivedCategory C] [HasDerivedCategory B]
    [HasDerivedCategory D] [HasDerivedCategory E]
    (R : C ⥤ B) (U : B ⥤ E) (P : C ⥤ D) (F : D ⥤ E)
    [R.Additive] [U.Additive] [P.Additive] [F.Additive]
    [PreservesFiniteLimits U] [PreservesFiniteColimits U]
    [PreservesFiniteLimits P] [PreservesFiniteColimits P]
    (τ : R ⋙ U ⟶ P ⋙ F) (M : CochainComplex.Plus C) :
    let H := (HomotopyCategory.Plus.quotient _).obj M
    let L := (R.mapHomologicalComplex (.up ℤ)).obj M.obj
    let D := (P.mapHomologicalComplex (.up ℤ)).obj M.obj
    let a := (NatTrans.mapHomologicalComplex τ (.up ℤ)).app M.obj
    U.mapDerivedCategoryFactors.inv.app L ≫
      DerivedCategory.Plus.ι.map
        (U.mapDerivedCategoryPlusFactorsh.hom.app (R.mapHomotopyCategoryPlus.obj H) ≫
          DerivedCategory.Plus.Qh.map
            ((NatTrans.mapHomotopyCategoryPlus
              τ).app H)) =
    DerivedCategory.Q.map a ≫
      (DerivedCategory.quotientCompQhIso _).inv.app
        ((F.mapHomologicalComplex (.up ℤ)).obj D) := by
  dsimp only
  rw [Functor.map_comp, Functor.ι_map_mapDerivedCategoryPlusFactorsh_hom_app]
  have hu := U.mapDerivedCategoryFactorsh_hom_app
    ((R.mapHomologicalComplex (.up ℤ)).obj M.obj)
  change U.mapDerivedCategoryFactorsh.hom.app
    ((HomotopyCategory.quotient _ _).obj
      ((R.mapHomologicalComplex (.up ℤ)).obj M.obj)) = _ at hu
  erw [hu]
  dsimp only [DerivedCategory.quotientCompQhIso,
    HomologicalComplexUpToQuasiIso.quotientCompQhIso, Quotient.lift.isLift,
    Functor.mapHomotopyCategoryFactors, NatIso.ofComponents, Iso.refl]
  erw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id]
  simp only [Category.id_comp, Category.assoc]
  erw [Iso.inv_hom_id_app_assoc]
  erw [Category.id_comp, Category.id_comp, Category.comp_id]
  change DerivedCategory.Qh.map ((HomotopyCategory.Plus.ι _).map
    ((NatTrans.mapHomotopyCategoryPlus
      τ).app
      ((HomotopyCategory.Plus.quotient _).obj M))) = _
  rw [NatTrans.ι_map_mapHomotopyCategoryPlus_app]
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- Transport of a target derived unit and an exact representative map.
Source: Stacks Project, Tag 03Q9, final injective-complex paragraph, and
Functor.rightDerivedFunctorPlusCompatibility.
(blueprint: lem-weil-pbc-injective-exchange-target-transport).
Proof: the defining rightDerivedUnique identity identifies the included
bounded-below F unit with the unbounded unit followed by the inverse
compatibility. Naturality of the inverse compatibility moves this inverse
past the map of the representative transport. Full faithfulness identifies
the included inverse exact P comparison with its unbounded version, and
identifies q'.inv with quotientCompQhIso.hom followed by q.inv. Expanding
mapDerivedCategoryFactorsh at M gives the complex comparison. Insert the
quotient comparison on P(M) to express its source as Q(P(M)). This uses only
the unit compatibility and naturality, and does not invert the unit. -/
private theorem target_unit_representative_transport
    {C : Type*} {D : Type*} {E : Type*}
    [Category C] [Category D] [Category E]
    [Abelian C] [Abelian D] [Abelian E]
    [HasDerivedCategory C] [HasDerivedCategory D]
    [HasDerivedCategory E] [EnoughInjectives D]
    [CategoryTheory.Abelian.HasKInjectiveResolutions D]
    (P : C ⥤ D) (F : D ⥤ E) [P.Additive] [F.Additive]
    [PreservesFiniteLimits P] [PreservesFiniteColimits P]
    (K : DerivedCategory.Plus C) (M : CochainComplex.Plus C)
    (q : K.obj ≅ DerivedCategory.Q.obj M.obj) :
    let H := (HomotopyCategory.Plus.quotient _).obj M
    let q' : K ≅ DerivedCategory.Plus.Qh.obj H :=
      DerivedCategory.Plus.ι.preimageIso (Y := DerivedCategory.Plus.Q.obj M)
        (q ≪≫ (DerivedCategory.quotientCompQhIso _).symm.app M.obj)
    let D := (P.mapHomologicalComplex (.up ℤ)).obj M.obj
    let T := P.mapDerivedCategoryPlus.obj K
    DerivedCategory.Plus.ι.map
      (F.rightDerivedFunctorPlusUnith.app (P.mapHomotopyCategoryPlus.obj H) ≫
        F.rightDerivedFunctorPlus.map
          (P.mapDerivedCategoryPlusFactorsh.inv.app H ≫
            P.mapDerivedCategoryPlus.map q'.inv)) =
    F.rightDerivedFunctorUnit.app ((HomotopyCategory.quotient _ _).obj D) ≫
      F.rightDerivedFunctor.map ((DerivedCategory.quotientCompQhIso _).hom.app D) ≫
      F.rightDerivedFunctor.map
        (P.mapDerivedCategoryFactors.inv.app M.obj ≫ P.mapDerivedCategory.map q.inv) ≫
      F.rightDerivedFunctorPlusCompatibility.inv.app T := by
  let H := (HomotopyCategory.Plus.quotient _).obj M
  let q' : K ≅ DerivedCategory.Plus.Qh.obj H :=
    DerivedCategory.Plus.ι.preimageIso (Y := DerivedCategory.Plus.Q.obj M)
      (q ≪≫ (DerivedCategory.quotientCompQhIso _).symm.app M.obj)
  let N := P.mapHomotopyCategoryPlus.obj H
  let g := P.mapDerivedCategoryPlusFactorsh.inv.app H ≫ P.mapDerivedCategoryPlus.map q'.inv
  have hc : DerivedCategory.Plus.ι.map (F.rightDerivedFunctorPlusUnith.app N) ≫
      F.rightDerivedFunctorPlusCompatibility.hom.app (DerivedCategory.Plus.Qh.obj N) =
      F.rightDerivedFunctorUnit.app N.obj := by
    with_unfolding_all
      simpa only [Functor.rightDerivedFunctorPlusιUnit, Functor.ιRightDerivedFunctorUnit,
        Functor.whiskerRight_app, Functor.whiskerLeft_app,
        HomotopyCategory.Plus.ι, ObjectProperty.ι_obj, Functor.comp_obj] using
        (show F.rightDerivedFunctorPlusιUnit.app N ≫
          F.rightDerivedFunctorPlusCompatibility.hom.app (DerivedCategory.Plus.Qh.obj N) =
          F.ιRightDerivedFunctorUnit.app N from by
        simp [Functor.rightDerivedFunctorPlusCompatibility])
  have hu : DerivedCategory.Plus.ι.map (F.rightDerivedFunctorPlusUnith.app N) =
      F.rightDerivedFunctorUnit.app N.obj ≫
        F.rightDerivedFunctorPlusCompatibility.inv.app (DerivedCategory.Plus.Qh.obj N) := by
    erw [← hc, Category.assoc, Iso.hom_inv_id_app, Category.comp_id]
  have hn := F.rightDerivedFunctorPlusCompatibility.inv.naturality g
  dsimp only [Functor.comp_map] at hn
  have hp : DerivedCategory.Plus.ι.map (P.mapDerivedCategoryPlusFactorsh.inv.app H) =
      P.mapDerivedCategoryFactorsh.inv.app H.obj := by
    apply (cancel_mono (P.mapDerivedCategoryFactorsh.hom.app H.obj)).mp
    erw [← P.ι_map_mapDerivedCategoryPlusFactorsh_hom_app H,
      ← DerivedCategory.Plus.ι.map_comp, Iso.inv_hom_id_app,
      DerivedCategory.Plus.ι.map_id]
    erw [P.ι_map_mapDerivedCategoryPlusFactorsh_hom_app H, Iso.inv_hom_id_app]
    rfl
  have hq : DerivedCategory.Plus.ι.map q'.inv =
      (DerivedCategory.quotientCompQhIso _).hom.app M.obj ≫ q.inv := by
    simp only [q', Functor.preimageIso, Functor.map_preimage, Iso.trans_inv]
    rfl
  dsimp only
  change DerivedCategory.Plus.ι.map
    (F.rightDerivedFunctorPlusUnith.app N ≫ F.rightDerivedFunctorPlus.map g) = _
  rw [Functor.map_comp, hu, Category.assoc]
  erw [← hn]
  have hph : P.mapDerivedCategoryFactorsh.hom.app H.obj =
      P.mapDerivedCategoryFactors.hom.app M.obj := by
    change P.mapDerivedCategoryFactorsh.hom.app
      ((HomotopyCategory.quotient _ _).obj M.obj) = _
    rw [P.mapDerivedCategoryFactorsh_hom_app]
    dsimp only [DerivedCategory.quotientCompQhIso,
      HomologicalComplexUpToQuasiIso.quotientCompQhIso, Quotient.lift.isLift,
      Functor.mapHomotopyCategoryFactors, NatIso.ofComponents, Iso.refl]
    erw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id,
      Category.id_comp, Category.id_comp, Category.comp_id]
  have hpi : P.mapDerivedCategoryFactorsh.inv.app H.obj =
      P.mapDerivedCategoryFactors.inv.app M.obj := by
    apply (cancel_mono (P.mapDerivedCategoryFactorsh.hom.app H.obj)).mp
    erw [Iso.inv_hom_id_app]
    erw [hph, Iso.inv_hom_id_app]
    rfl
  have hg : DerivedCategory.Plus.ι.map g =
      P.mapDerivedCategoryFactors.inv.app M.obj ≫ P.mapDerivedCategory.map q.inv := by
    dsimp only [g]
    rw [Functor.map_comp, hp]
    change P.mapDerivedCategoryFactorsh.inv.app H.obj ≫
      P.mapDerivedCategory.map (DerivedCategory.Plus.ι.map q'.inv) = _
    rw [hq]
    dsimp only [DerivedCategory.quotientCompQhIso,
      HomologicalComplexUpToQuasiIso.quotientCompQhIso, Quotient.lift.isLift,
      NatIso.ofComponents, Iso.refl]
    erw [Category.id_comp, hpi]
  rw [hg]
  dsimp only [DerivedCategory.quotientCompQhIso,
    HomologicalComplexUpToQuasiIso.quotientCompQhIso, Quotient.lift.isLift,
    NatIso.ofComponents, Iso.refl]
  erw [CategoryTheory.Functor.map_id, Category.id_comp]
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- Transport the localized underived exchange and target unit to unbounded categories.

Source: Stacks Project, Tag 03Q9, final injective-complex paragraph; the exact
localization comparisons and defining unit compatibility of
`Functor.rightDerivedFunctorPlusCompatibility`.
(blueprint: lem-weil-pbc-injective-exchange-target-transport).

Proof: map the bounded-below composite through the inclusion and use its
compatibility with mapDerivedCategoryPlusFactorsh. The first factor is the
homotopy version of the exact comparison for U and cancels against its
complex-level inverse, because the homotopy quotient comparison is identity.
The next factor is Q of the termwise underived exchange. The defining
right-derived uniqueness isomorphism carries the bounded-below target unit to
the unbounded target unit; naturality carries the following target transport
through this isomorphism, leaving its inverse as the last factor. The inverse
exact pullback comparison maps to the unbounded inverse comparison. Full
faithfulness identifies the image of q'.inv with quotientCompQhIso.hom followed
by q.inv. Insert the canonical quotient comparisons on D and its direct image
to express these identities in the stated complex-level form. No target unit
is inverted, so no acyclicity of the pulled-back complex is assumed. -/
theorem smallModel_injectiveExchange_target_transport {X S : Scheme.{v}} (f : X ⟶ S)
    {Ω : Type v} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ S)
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{v + 1}))
    (J : CochainComplex.Plus (InjectiveObject
      (Sheaf X.smallEtaleTopology AddCommGrpCat.{v + 1})))
    (q : K.obj ≅ DerivedCategory.Q.obj
      (((InjectiveObject.ι _).mapHomologicalComplex (.up ℤ)).obj J.obj)) :
    let M₁ := ((InjectiveObject.ι _).mapHomologicalComplex (.up ℤ)).obj J.obj
    let M : CochainComplex.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{v + 1}) :=
      ⟨M₁, ((InjectiveObject.ι _).mapCochainComplexPlus.obj J).property⟩
    let H := (HomotopyCategory.Plus.quotient _).obj M
    let q' : K ≅ DerivedCategory.Plus.Qh.obj H :=
      DerivedCategory.Plus.ι.preimageIso (Y := DerivedCategory.Plus.Qh.obj H)
        (q ≪≫ (DerivedCategory.quotientCompQhIso _).symm.app M.obj)
    let R := lowerStar AddCommGrpCat.{v + 1} f
    let U := upperStar AddCommGrpCat.{v + 1} (Scheme.strictHenselizationStructuralMap s)
    let P := upperStar AddCommGrpCat.{v + 1}
      (pullback.fst f (Scheme.strictHenselizationStructuralMap s))
    let F := lowerStar AddCommGrpCat.{v + 1}
      (pullback.snd f (Scheme.strictHenselizationStructuralMap s))
    let M₀ := ((InjectiveObject.ι _).mapHomologicalComplex (.up ℤ)).obj J.obj
    let L := (R.mapHomologicalComplex (.up ℤ)).obj M₀
    let D := (P.mapHomologicalComplex (.up ℤ)).obj M₀
    let T := P.mapDerivedCategoryPlus.obj K
    let sq := (IsPullback.of_hasPullback f
      (Scheme.strictHenselizationStructuralMap s)).toCommSq
    let a : (U.mapHomologicalComplex (.up ℤ)).obj L ⟶
        (F.mapHomologicalComplex (.up ℤ)).obj D :=
      (NatTrans.mapHomologicalComplex
      (baseChangeMap AddCommGrpCat.{v + 1} sq) (.up ℤ)).app M₀
    U.mapDerivedCategoryFactors.inv.app
      ((R.mapHomologicalComplex (.up ℤ)).obj M.obj) ≫
      U.mapDerivedCategory.map ((DerivedCategory.quotientCompQhIso _).inv.app L) ≫
      DerivedCategory.Plus.ι.map
        (U.mapDerivedCategoryPlusFactorsh.hom.app (R.mapHomotopyCategoryPlus.obj H) ≫
          DerivedCategory.Plus.Qh.map
            ((NatTrans.mapHomotopyCategoryPlus
              (baseChangeMap AddCommGrpCat.{v + 1} sq)).app H) ≫
          F.rightDerivedFunctorPlusUnith.app (P.mapHomotopyCategoryPlus.obj H) ≫
          F.rightDerivedFunctorPlus.map
            (P.mapDerivedCategoryPlusFactorsh.inv.app H ≫
              P.mapDerivedCategoryPlus.map q'.inv)) =
    DerivedCategory.Q.map a ≫
      (DerivedCategory.quotientCompQhIso _).inv.app
        ((F.mapHomologicalComplex (.up ℤ)).obj D) ≫
      F.rightDerivedFunctorUnit.app ((HomotopyCategory.quotient _ _).obj D) ≫
      F.rightDerivedFunctor.map ((DerivedCategory.quotientCompQhIso _).hom.app D) ≫
      F.rightDerivedFunctor.map
        (P.mapDerivedCategoryFactors.inv.app M₀ ≫ P.mapDerivedCategory.map q.inv) ≫
      F.rightDerivedFunctorPlusCompatibility.inv.app T := by
  let M₁ := ((InjectiveObject.ι _).mapHomologicalComplex (.up ℤ)).obj J.obj
  let M : CochainComplex.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{v + 1}) :=
    ⟨M₁, ((InjectiveObject.ι _).mapCochainComplexPlus.obj J).property⟩
  let H := (HomotopyCategory.Plus.quotient _).obj M
  let q' : K ≅ DerivedCategory.Plus.Qh.obj H :=
    DerivedCategory.Plus.ι.preimageIso (Y := DerivedCategory.Plus.Q.obj M)
      (q ≪≫ (DerivedCategory.quotientCompQhIso _).symm.app M.obj)
  let P := upperStar AddCommGrpCat.{v + 1}
    (pullback.fst f (Scheme.strictHenselizationStructuralMap s))
  let F := lowerStar AddCommGrpCat.{v + 1}
    (pullback.snd f (Scheme.strictHenselizationStructuralMap s))
  let R := lowerStar AddCommGrpCat.{v + 1} f
  let U := upperStar AddCommGrpCat.{v + 1} (Scheme.strictHenselizationStructuralMap s)
  let L := (R.mapHomologicalComplex (.up ℤ)).obj M.obj
  let D := (P.mapHomologicalComplex (.up ℤ)).obj M.obj
  let sq := (IsPullback.of_hasPullback f
    (Scheme.strictHenselizationStructuralMap s)).toCommSq
  let a := (NatTrans.mapHomologicalComplex (baseChangeMap AddCommGrpCat.{v + 1} sq)
    (.up ℤ)).app M.obj
  change U.mapDerivedCategoryFactors.inv.app L ≫
    U.mapDerivedCategory.map (𝟙 _) ≫ _ = _
  erw [CategoryTheory.Functor.map_id, Category.id_comp]
  have hp := exchange_localization_prefix R U P F
    (baseChangeMap AddCommGrpCat.{v + 1} sq) M
  have ht := target_unit_representative_transport P F K M q
  dsimp only at hp ht
  exact assemble_transport DerivedCategory.Plus.ι
    (U.mapDerivedCategoryFactors.inv.app L)
    (U.mapDerivedCategoryPlusFactorsh.hom.app (R.mapHomotopyCategoryPlus.obj H))
    (DerivedCategory.Plus.Qh.map
      ((NatTrans.mapHomotopyCategoryPlus (baseChangeMap AddCommGrpCat.{v + 1} sq)).app H))
    (F.rightDerivedFunctorPlusUnith.app (P.mapHomotopyCategoryPlus.obj H))
    (F.rightDerivedFunctorPlus.map
      (P.mapDerivedCategoryPlusFactorsh.inv.app H ≫ P.mapDerivedCategoryPlus.map q'.inv))
    (DerivedCategory.Q.map a)
    ((DerivedCategory.quotientCompQhIso _).inv.app
      ((F.mapHomologicalComplex (.up ℤ)).obj D))
    (F.rightDerivedFunctorUnit.app ((HomotopyCategory.quotient _ _).obj D))
    (F.rightDerivedFunctor.map ((DerivedCategory.quotientCompQhIso _).hom.app D))
    (F.rightDerivedFunctor.map
      (P.mapDerivedCategoryFactors.inv.app M.obj ≫ P.mapDerivedCategory.map q.inv))
    (F.rightDerivedFunctorPlusCompatibility.inv.app (P.mapDerivedCategoryPlus.obj K)) hp ht

end AlgebraicGeometry.Etale
