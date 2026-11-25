/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import WeilConjectures.CategoryTheory.CoefficientDerivedSections.DerivedSectionsScalarCoherence
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Limits.Final
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp

/-! # Scalar restriction preserves the computation of derived sections

Source: Stacks Project, Sites Cohomology, Tag 0D6E.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u v w
open CategoryTheory CategoryTheory.Limits
namespace SheafOfModules

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private def smallModulesEquivalence
    {C : Type u} [Category.{v} C] {D : Type*} [Category D]
    (e : C ≌ D) {J : GrothendieckTopology C} (R : Sheaf J RingCat.{w}) :
    SheafOfModules.{w} R ≌ SheafOfModules.{w}
      ((e.sheafCongr J (e.inverse.inducedTopology J) RingCat.{w}).functor.obj R) := by
  let K := e.inverse.inducedTopology J
  let R' := (e.sheafCongr J K RingCat.{w}).functor.obj R
  let φ : R' ⟶ (e.inverse.sheafPushforwardContinuous RingCat.{w} K J).obj R := 𝟙 _
  let ψ : R ⟶ (e.functor.sheafPushforwardContinuous RingCat.{w} J K).obj R' :=
    ((e.sheafCongr J K RingCat.{w}).unitIso.app R).hom
  have : e.symm.functor.IsContinuous K J := inferInstanceAs (e.inverse.IsContinuous K J)
  have : e.symm.inverse.IsContinuous J K := inferInstanceAs (e.functor.IsContinuous J K)
  exact pushforwardPushforwardEquivalence e.symm φ ψ (by
    ext U x
    change R.obj.map (e.unitIso.inv.app U.unop).op x = _
    rfl) (by
    ext U x
    change R.obj.map (e.inverse.map (e.counitIso.inv.app U.unop)).op
      (R.obj.map (e.unitIso.inv.app (e.inverse.obj U.unop)).op x) = x
    change (R.obj.map (e.unitIso.inv.app (e.inverse.obj U.unop)).op ≫
      R.obj.map (e.inverse.map (e.counitIso.inv.app U.unop)).op) x = x
    rw [← Functor.map_comp]
    have hh : (e.unitIso.inv.app (e.inverse.obj U.unop)).op ≫
        (e.inverse.map (e.counitIso.inv.app U.unop)).op = 𝟙 _ := by
      apply Quiver.Hom.unop_inj
      simp
    rw [hh, R.obj.map_id]
    rfl)

private abbrev smallCoefficientRing
    {C : Type u} [Category.{v} C] {D : Type w} [SmallCategory D]
    (e : C ≌ D) {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] (R : Sheaf J CommRingCat.{w}) :=
  (e.sheafCongr J (e.inverse.inducedTopology J) CommRingCat.{w}).functor.obj R

private def smallCoefficientEquivalence
    {C : Type u} [Category.{v} C] {D : Type w} [SmallCategory D]
    (e : C ≌ D) {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] (R : Sheaf J CommRingCat.{w}) :
    SheafOfModules.{w} ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj R) ≌
      SheafOfModules.{w} ((sheafCompose (e.inverse.inducedTopology J)
        (forget₂ CommRingCat.{w} RingCat.{w})).obj (smallCoefficientRing e R)) :=
  smallModulesEquivalence e _

private def smallCoefficientFunctor
    {C : Type u} [Category.{v} C] {D : Type w} [SmallCategory D]
    (e : C ≌ D) {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] (R : Sheaf J CommRingCat.{w}) :=
  (smallCoefficientEquivalence e R).functor

private instance smallCoefficientFunctor_equivalence
    {C : Type u} [Category.{v} C] {D : Type w} [SmallCategory D]
    (e : C ≌ D) {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] (R : Sheaf J CommRingCat.{w}) :
    (smallCoefficientFunctor e R).IsEquivalence := by
  unfold smallCoefficientFunctor
  infer_instance

private instance smallCoefficientFunctor_additive
    {C : Type u} [Category.{v} C] {D : Type w} [SmallCategory D]
    (e : C ≌ D) {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] (R : Sheaf J CommRingCat.{w}) :
    (smallCoefficientFunctor e R).Additive :=
  Functor.additive_of_preserves_binary_products _

private def smallRestrictionComparison
    {C : Type u} [Category.{v} C] {D : Type w} [SmallCategory D]
    (e : C ≌ D) {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
    {R S : Sheaf J CommRingCat.{w}} (f : R ⟶ S) :
    smallCoefficientFunctor e S ⋙
        restrictScalars ((sheafCompose (e.inverse.inducedTopology J)
          (forget₂ CommRingCat.{w} RingCat.{w})).map
            ((e.sheafCongr J (e.inverse.inducedTopology J) CommRingCat.{w}).functor.map f)) ≅
      restrictScalars ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).map f) ⋙
        smallCoefficientFunctor e R :=
  NatIso.ofComponents (fun M ↦ Iso.refl _) (fun g ↦ by rfl)

private def smallUnderlyingComparison
    {C : Type u} [Category.{v} C] {D : Type w} [SmallCategory D]
    (e : C ≌ D) {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] (R : Sheaf J CommRingCat.{w}) :
    smallCoefficientFunctor e R ⋙ toSheaf _ ⋙
        sheafToPresheaf (e.inverse.inducedTopology J) AddCommGrpCat.{w} ≅
      toSheaf ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj R) ⋙
        sheafToPresheaf J AddCommGrpCat.{w} ⋙
          (Functor.whiskeringLeft _ _ AddCommGrpCat.{w}).obj e.inverse.op :=
  Iso.refl _

attribute [irreducible] smallCoefficientFunctor smallCoefficientEquivalence

private theorem quasiIso_map_iso
    {A D : Type*} [Category A] [Category D] [Abelian A] [Abelian D]
    (F G : A ⥤ D) [F.Additive] [G.Additive] (e : F ≅ G)
    {I K : CochainComplex A ℤ} (j : I ⟶ K)
    [QuasiIso ((F.mapHomologicalComplex (.up ℤ)).map j)] :
    QuasiIso ((G.mapHomologicalComplex (.up ℤ)).map j) := by
  let ec := NatIso.mapHomologicalComplex e (.up ℤ)
  have heq : (G.mapHomologicalComplex (.up ℤ)).map j =
      ec.inv.app I ≫ (F.mapHomologicalComplex (.up ℤ)).map j ≫ ec.hom.app K := by
    apply (cancel_epi (ec.hom.app I)).mp
    simp only [Iso.hom_inv_id_app_assoc]
    exact (ec.hom.naturality j).symm
  rw [heq]
  infer_instance

private theorem smallRestrictionSections
    {D : Type w} [SmallCategory D] {T : GrothendieckTopology D}
    [HasSheafify T AddCommGrpCat.{w}] [T.WEqualsLocallyBijective AddCommGrpCat.{w}]
    {R S : Sheaf T CommRingCat.{w}} (f : R ⟶ S)
    (I : CochainComplex (CategoryTheory.CoefficientDerivedSections.coefficientModules S) ℤ)
    (K : CochainComplex (CategoryTheory.CoefficientDerivedSections.coefficientModules R) ℤ)
    (j : ((CategoryTheory.CoefficientDerivedSections.coefficientRestriction f).mapHomologicalComplex
      (.up ℤ)).obj I ⟶ K)
    [I.IsKInjective] [K.IsKInjective] [QuasiIso j] :
    QuasiIso (((toSheaf _ ⋙ sheafToPresheaf T AddCommGrpCat.{w} ⋙ lim).mapHomologicalComplex
      (.up ℤ)).map j) := by
  let : ∀ R : Sheaf T CommRingCat.{w}, HasDerivedCategory.{w + 1}
      (CategoryTheory.CoefficientDerivedSections.coefficientModules R) :=
    fun R ↦ HasDerivedCategory.standard _
  let : HasDerivedCategory.{w + 1} AddCommGrpCat.{w} := HasDerivedCategory.standard _
  obtain ⟨_, H, η, hH, hη, r, ν, σ, hσ, _, _⟩ :=
    CategoryTheory.CoefficientDerivedSections.derivedSectionsScalarCoherence (J := T)
  have hq := ((hσ f).2.2.2 I inferInstance K inferInstance j).1
  let G := CategoryTheory.CoefficientDerivedSections.coefficientSections R
  let F := toSheaf ((sheafCompose T (forget₂ CommRingCat RingCat)).obj R) ⋙
    sheafToPresheaf T AddCommGrpCat.{w} ⋙ lim
  have : F.Additive := Functor.additive_of_preserves_binary_products F
  let e : G ≅ F := Functor.isoWhiskerLeft (toSheaf _) (Sheaf.ΓNatIsoLim T _)
  have hq' : QuasiIso ((G.mapHomologicalComplex (.up ℤ)).map j) := hq
  exact quasiIso_map_iso G F e j

private theorem restrictionSectionsOfEquivalence
    {C : Type u} [Category.{v} C] {D : Type w} [SmallCategory D]
    (e : C ≌ D)
    {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
    [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify J AddCommGrpCat.{w}]
    [HasLimitsOfShape Cᵒᵖ AddCommGrpCat.{w}]
    {R S : Sheaf J CommRingCat.{w}} (f : R ⟶ S)
    (I : CochainComplex (SheafOfModules.{w}
      ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj S)) ℤ)
    (K : CochainComplex (SheafOfModules.{w}
      ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj R)) ℤ)
    (j : ((restrictScalars.{w}
      ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).map f)).mapHomologicalComplex
        (.up ℤ)).obj I ⟶ K)
    [I.IsKInjective] [K.IsKInjective] [QuasiIso j] :
    QuasiIso (((toSheaf _ ⋙ sheafToPresheaf J AddCommGrpCat.{w} ⋙ lim).mapHomologicalComplex
      (.up ℤ)).map j) := by
  let J' := e.inverse.inducedTopology J
  let ec := e.sheafCongr J J' CommRingCat.{w}
  let R' := ec.functor.obj R
  let S' := ec.functor.obj S
  let f' := ec.functor.map f
  let FR := smallCoefficientFunctor e R
  let FS := smallCoefficientFunctor e S
  have : FR.IsEquivalence := inferInstance
  have : FS.IsEquivalence := inferInstance
  have : FR.Additive := Functor.additive_of_preserves_binary_products FR
  have : FS.Additive := Functor.additive_of_preserves_binary_products FS
  let I' := (FS.mapHomologicalComplex (.up ℤ)).obj I
  let K' := (FR.mapHomologicalComplex (.up ℤ)).obj K
  have : CochainComplex.IsKInjective I' := inferInstance
  have : CochainComplex.IsKInjective K' := inferInstance
  let c := smallRestrictionComparison e f
  let j' := (NatIso.mapHomologicalComplex c (.up ℤ)).hom.app I ≫
    (FR.mapHomologicalComplex (.up ℤ)).map j
  have : QuasiIso j' := by
    dsimp only [j']
    infer_instance
  have hq := smallRestrictionSections f' I' K' j'
  let G := toSheaf ((sheafCompose J' (forget₂ CommRingCat.{w} RingCat.{w})).obj R') ⋙
    sheafToPresheaf J' AddCommGrpCat.{w} ⋙ lim
  have : G.Additive := Functor.additive_of_preserves_binary_products G
  have hq' : QuasiIso ((G.mapHomologicalComplex (.up ℤ)).map
      ((FR.mapHomologicalComplex (.up ℤ)).map j)) := by
    rw [show (G.mapHomologicalComplex (.up ℤ)).map j' =
      (G.mapHomologicalComplex (.up ℤ)).map
        ((NatIso.mapHomologicalComplex c (.up ℤ)).hom.app I) ≫
      (G.mapHomologicalComplex (.up ℤ)).map
        ((FR.mapHomologicalComplex (.up ℤ)).map j) from Functor.map_comp _ _ _] at hq
    exact (quasiIso_iff_comp_left _ _).mp hq
  let FG := FR ⋙ G
  have : FG.Additive := inferInstance
  have hq'' : QuasiIso ((FG.mapHomologicalComplex (.up ℤ)).map j) := hq'
  let F := toSheaf
    ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj R) ⋙
      sheafToPresheaf J AddCommGrpCat.{w} ⋙ lim
  have : F.Additive := Functor.additive_of_preserves_binary_products F
  let eΓ : FG ≅ F :=
    Functor.isoWhiskerRight (smallUnderlyingComparison e R) lim ≪≫
      Functor.isoWhiskerLeft (toSheaf _ ⋙ sheafToPresheaf J AddCommGrpCat.{w})
        (Functor.Initial.limIso e.inverse.op)
  exact quasiIso_map_iso FG F eΓ j

/-- A K-injective coefficient complex remains acyclic for the computation of global
sections after scalar restriction. The restricted complex need not be K-injective.
Source: Stacks Project, sites-cohomology.tex, Tag 0D6E,
lemma-derived-pushforward-composition, specialized to scalar restriction and sections
(blueprint: lem-coef-restriction-sections-acyclic).

Proof: replace the site by its small model in the coefficient universe and transport
its topology. Restriction of module sheaves along the site equivalence is an exact
equivalence, commutes with coefficient restriction, and preserves K-injectivity and
quasi-isomorphisms. The underlying presheaf limits are canonically unchanged. On the
small model apply the resolution clause of
lem-coef-derived-sections-scalar-coherence to I, K and j. The canonical composition
comparison of Tag 0D6E identifies the resulting map with sections of j and says it is
a quasi-isomorphism. Transport this conclusion back along the limit comparison.
The argument applies also to the empty site and the zero coefficient ring. -/
theorem coefficientRestrictionSections_quasiIso
    {C : Type u} [Category.{v} C] [EssentiallySmall.{w} C]
    {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
    [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify J AddCommGrpCat.{w}]
    [HasLimitsOfShape Cᵒᵖ AddCommGrpCat.{w}]
    {R S : Sheaf J CommRingCat.{w}} (f : R ⟶ S)
    (I : CochainComplex (SheafOfModules.{w}
      ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj S)) ℤ)
    (K : CochainComplex (SheafOfModules.{w}
      ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj R)) ℤ)
    (j : ((restrictScalars.{w}
      ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).map f)).mapHomologicalComplex
        (.up ℤ)).obj I ⟶ K)
    [I.IsKInjective] [K.IsKInjective] [QuasiIso j] :
    QuasiIso (((toSheaf _ ⋙ sheafToPresheaf J AddCommGrpCat.{w} ⋙ lim).mapHomologicalComplex
      (.up ℤ)).map j) := by
  exact restrictionSectionsOfEquivalence (equivSmallModel.{w} C) f I K j

end SheafOfModules
