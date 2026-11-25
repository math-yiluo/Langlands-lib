/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.Algebra.Homology.KFlat
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import WeilConjectures.CategoryTheory.SiteConstantModuleFunctorGeneral

/-!
# The commutative-coefficient presentation of exact constant realization

Source: Stacks Project, Modules on Sites, Tags 03CY and 093J; Cohomology on Sites,
paragraph preceding 09BD (auxiliary; not a blueprint node).
The ring sheaf here is the constant CommRingCat sheaf with commutativity forgotten.
The old interface uses constant RingCat sheafification instead. Their canonical
constantCommuteCompose isomorphism identifies the two presentations.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u v wR wS
open CategoryTheory CategoryTheory.Limits
namespace CategoryTheory

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)

/-- The usual constant commutative ring sheaf.
Source: Stacks 093J (auxiliary; not a blueprint node). -/
abbrev realizationRing (R : Type (max u v)) [CommRing R] :=
  (constantSheaf J CommRingCat.{max u v}).obj (CommRingCat.of R)

/-- The existing module category over its underlying ring sheaf.
Source: Stacks 03DA (auxiliary; not a blueprint node). -/
abbrev realizationModules (R : Type (max u v)) [CommRing R] :=
  SheafOfModules.{max u v} ((sheafCompose J
    (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj (realizationRing J R))

/-- The coefficient sheafification unit with commutativity forgotten.
Source: Stacks 03CY (auxiliary; not a blueprint node). -/
def realizationRingUnit (R : Type (max u v)) [CommRing R] :
    (Functor.const Cᵒᵖ).obj (RingCat.of R) ⟶
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj (realizationRing J R)).obj :=
  Functor.whiskerRight
    (toSheafify J ((Functor.const Cᵒᵖ).obj (CommRingCat.of R)))
    (forget₂ CommRingCat RingCat)

/-- Forgetting commutativity retains the locally bijective sheafification unit.
Source: Stacks 03CY (auxiliary; not a blueprint node).
Proof: local injectivity and local surjectivity only concern the underlying functions
of sections and covering sieves. Forgetting commutativity changes none of them. -/
theorem realizationRingUnit_locallyBijective (R : Type (max u v)) [CommRing R] :
    Presheaf.IsLocallyInjective J (realizationRingUnit J R) ∧
      Presheaf.IsLocallySurjective J (realizationRingUnit J R) := by
  constructor
  · constructor
    intro X x y h
    exact Presheaf.equalizerSieve_mem J
      (toSheafify J ((Functor.const Cᵒᵖ).obj (CommRingCat.of R))) x y h
  · constructor
    intro U s
    exact Presheaf.imageSieve_mem J
      (toSheafify J ((Functor.const Cᵒᵖ).obj (CommRingCat.of R))) s

/-- The recorded constant module construction with the commutative coefficient
presentation: the same constant module presheaf followed by module sheafification.
Source: Stacks 03CY and 093J (auxiliary; not a blueprint node). -/
def commutativeSiteConstantModuleFunctor (R : Type (max u v)) [CommRing R] :
    ModuleCat.{max u v} R ⥤ realizationModules J R :=
  letI := (realizationRingUnit_locallyBijective J R).1
  letI := (realizationRingUnit_locallyBijective J R).2
  siteConstantModulePresheafGeneral (C := C) R ⋙
    PresheafOfModules.sheafification (realizationRingUnit J R)

/-- The commutative-coefficient presentation is additive and exact.
Source: Stacks 093J and 03CY (auxiliary; not a blueprint node).
Proof: constant presheaves preserve exact sequences sectionwise. Module sheafification
is additive and exact, so their composite preserves finite limits and finite colimits. -/
theorem commutativeSiteConstantModuleFunctor_exact (R : Type (max u v)) [CommRing R] :
    (commutativeSiteConstantModuleFunctor J R).Additive ∧
      PreservesFiniteLimits (commutativeSiteConstantModuleFunctor J R) ∧
      PreservesFiniteColimits (commutativeSiteConstantModuleFunctor J R) := by
  let P := siteConstantModulePresheafGeneral (C := C) R
  have : PreservesFiniteLimits P := by
    constructor
    intro K _ _
    constructor
    intro F
    constructor
    intro c hc
    exact ⟨PresheafOfModules.evaluationJointlyReflectsLimits _ _ (fun X ↦ hc)⟩
  have : PreservesFiniteColimits P := by
    constructor
    intro K _ _
    constructor
    intro F
    constructor
    intro c hc
    exact ⟨PresheafOfModules.evaluationJointlyReflectsColimits _ _ (fun X ↦ hc)⟩
  have := (realizationRingUnit_locallyBijective J R).1
  have := (realizationRingUnit_locallyBijective J R).2
  change (P ⋙ PresheafOfModules.sheafification (realizationRingUnit J R)).Additive ∧
    PreservesFiniteLimits (P ⋙ PresheafOfModules.sheafification (realizationRingUnit J R)) ∧
    PreservesFiniteColimits (P ⋙ PresheafOfModules.sheafification (realizationRingUnit J R))
  have hL : PreservesFiniteLimits (PresheafOfModules.sheafification
      (realizationRingUnit J R)) := inferInstance
  have hC : PreservesFiniteColimits (PresheafOfModules.sheafification
      (realizationRingUnit J R)) := inferInstance
  have : PreservesFiniteLimits
      (P ⋙ PresheafOfModules.sheafification (realizationRingUnit J R)) :=
    comp_preservesFiniteLimits _ _
  have : PreservesFiniteColimits
      (P ⋙ PresheafOfModules.sheafification (realizationRingUnit J R)) :=
    comp_preservesFiniteColimits _ _
  refine ⟨?_, inferInstance, inferInstance⟩
  apply leftExactFunctor_le_additiveFunctor _ _
  rw [leftExactFunctor_iff]
  infer_instance

/-- Additivity supplied by exact constant realization.
Source: Stacks 093J (auxiliary; not a blueprint node). -/
instance commutativeSiteConstantModuleFunctor_additive
    (R : Type (max u v)) [CommRing R] :
    (commutativeSiteConstantModuleFunctor J R).Additive :=
  (commutativeSiteConstantModuleFunctor_exact J R).1

/-- Left exactness supplied by exact constant realization.
Source: Stacks 093J (auxiliary; not a blueprint node). -/
instance commutativeSiteConstantModuleFunctor_limits
    (R : Type (max u v)) [CommRing R] :
    PreservesFiniteLimits (commutativeSiteConstantModuleFunctor J R) :=
  (commutativeSiteConstantModuleFunctor_exact J R).2.1

/-- Right exactness supplied by exact constant realization.
Source: Stacks 093J (auxiliary; not a blueprint node). -/
instance commutativeSiteConstantModuleFunctor_colimits
    (R : Type (max u v)) [CommRing R] :
    PreservesFiniteColimits (commutativeSiteConstantModuleFunctor J R) :=
  (commutativeSiteConstantModuleFunctor_exact J R).2.2

/-- Forgetting commutativity preserves sheafification equivalences.
Source: Stacks 00WJ and 093J (auxiliary; not a blueprint node).
Proof: a morphism of ring presheaves is inverted by sheafification exactly when its
underlying functions are locally injective and locally surjective. The underlying
functions and covering sieves are unchanged by forgetting commutativity. Hence every
CommRingCat sheafification equivalence is a RingCat sheafification equivalence. -/
theorem realization_forget_preservesSheafification :
    J.PreservesSheafification (forget₂ CommRingCat.{max u v} RingCat.{max u v}) := by
  constructor
  intro P Q f hf
  change J.W (Functor.whiskerRight f (forget₂ CommRingCat RingCat))
  have : Presheaf.IsLocallyInjective J f := hf.isLocallyInjective
  have : Presheaf.IsLocallySurjective J f := hf.isLocallySurjective
  apply (J.W_iff_isLocallyBijective _).mpr
  constructor
  · exact ⟨fun x y h ↦ Presheaf.equalizerSieve_mem J f x y h⟩
  · exact ⟨fun x ↦ Presheaf.imageSieve_mem J f x⟩

/-- The coefficient-forgetful sheafification instance.
Source: Stacks 093J (auxiliary; not a blueprint node). -/
instance realization_forget_preservesSheafification_instance :
    J.PreservesSheafification (forget₂ CommRingCat.{max u v} RingCat.{max u v}) :=
  realization_forget_preservesSheafification J

/-- The canonical comparison with the original RingCat coefficient presentation.
Source: Stacks 093J (auxiliary; not a blueprint node). -/
def realizationRingIso (R : Type (max u v)) [CommRing R] :
    (sheafCompose J (forget₂ CommRingCat RingCat)).obj (realizationRing J R) ≅
      (constantSheaf J RingCat).obj (RingCat.of R) :=
  (constantCommuteCompose J (forget₂ CommRingCat RingCat)).app (CommRingCat.of R)

set_option backward.isDefEq.respectTransparency false in
private theorem realizationRingIso_fac (R : Type (max u v)) [CommRing R] :
    realizationRingUnit J R ≫ (realizationRingIso J R).hom.hom =
      toSheafify J ((Functor.const Cᵒᵖ).obj (RingCat.of R)) := by
  dsimp only [realizationRingIso, Iso.app_hom]
  rw [constantCommuteCompose_hom_app_hom]
  unfold realizationRingUnit
  rw [← Category.assoc, sheafComposeIso_inv_fac]
  exact (toSheafify_naturality J
    (Functor.constComp Cᵒᵖ (CommRingCat.of R)
      (forget₂ CommRingCat RingCat)).hom).symm.trans (by rfl)

section Transport

variable [HasSheafify J AddCommGrpCat.{max u v}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]

variable {R₀ : Cᵒᵖ ⥤ RingCat.{max u v}} {A B : Sheaf J RingCat.{max u v}}
  (ηA : R₀ ⟶ A.obj) (ηB : R₀ ⟶ B.obj)
  [Presheaf.IsLocallyInjective J ηA] [Presheaf.IsLocallySurjective J ηA]
  [Presheaf.IsLocallyInjective J ηB] [Presheaf.IsLocallySurjective J ηB]
  (α : A ⟶ B) (hsq : ηA ≫ α.hom = ηB)

set_option backward.isDefEq.respectTransparency false in
private def moduleSheafificationSeed (P : PresheafOfModules.{max u v} R₀) :
    P ⟶ (PresheafOfModules.restrictScalars ηA).obj
      ((SheafOfModules.restrictScalars α).obj
        ((PresheafOfModules.sheafification ηB).obj P)).val := by
  let τ := PresheafOfModules.toSheafify ηB (toSheafify J P.presheaf)
  refine PresheafOfModules.homMk (toSheafify J P.presheaf) ?_
  intro U r x
  refine ((τ.app U).hom.map_smul r x).trans ?_
  change ηB.app U r •
      (show ((PresheafOfModules.sheafification ηB).obj P).val.obj U from τ.app U x) =
    α.hom.app U (ηA.app U r) •
      (show ((PresheafOfModules.sheafification ηB).obj P).val.obj U from τ.app U x)
  have hs := ConcreteCategory.congr_hom (congr_app hsq U) r
  change α.hom.app U (ηA.app U r) = ηB.app U r at hs
  rw [hs]

omit [Presheaf.IsLocallyInjective J ηA] [Presheaf.IsLocallySurjective J ηA] in
private theorem moduleSheafificationSeed_toPresheaf
    (P : PresheafOfModules.{max u v} R₀) :
    (PresheafOfModules.toPresheaf R₀).map
      (moduleSheafificationSeed J ηA ηB α hsq P) = toSheafify J P.presheaf := by
  ext U x
  rfl

attribute [local irreducible] moduleSheafificationSeed

private def moduleSheafificationComparison (P : PresheafOfModules.{max u v} R₀) :
    (PresheafOfModules.sheafification ηA).obj P ⟶
      (SheafOfModules.restrictScalars α).obj
        ((PresheafOfModules.sheafification ηB).obj P) :=
  (PresheafOfModules.sheafificationHomEquiv ηA).symm
    (moduleSheafificationSeed J ηA ηB α hsq P)

set_option backward.isDefEq.respectTransparency false in
private theorem moduleSheafificationComparison_toSheaf
    (P : PresheafOfModules.{max u v} R₀) :
    (SheafOfModules.toSheaf A).map
      (moduleSheafificationComparison J ηA ηB α hsq P) = 𝟙 _ := by
  unfold moduleSheafificationComparison
  rw [PresheafOfModules.toSheaf_map_sheafificationHomEquiv_symm,
    moduleSheafificationSeed_toPresheaf]
  change ((sheafificationAdjunction J AddCommGrpCat.{max u v}).homEquiv
    P.presheaf ((presheafToSheaf J AddCommGrpCat).obj P.presheaf)).symm
      (toSheafify J P.presheaf) = 𝟙 _
  apply ((sheafificationAdjunction J AddCommGrpCat.{max u v}).homEquiv _ _).injective
  rw [Equiv.apply_symm_apply, Adjunction.homEquiv_unit]
  exact (Category.comp_id _).symm

attribute [local irreducible] moduleSheafificationComparison

private theorem moduleSheafificationComparison_isIso
    (P : PresheafOfModules.{max u v} R₀) :
    IsIso (moduleSheafificationComparison J ηA ηB α hsq P) := by
  rw [← isIso_iff_of_reflects_iso _ (SheafOfModules.toSheaf A),
    moduleSheafificationComparison_toSheaf]
  infer_instance

end Transport

/-- The repaired presentation is the recorded constant-module functor after canonical
coefficient transport, rather than a second constant realization.
Source: Stacks 03CY and 093J (auxiliary; not a blueprint node).
Proof: constantCommuteCompose identifies the two ring-sheafification units. Transport
along this identification identifies their module-sheafification adjunctions. The
identity of constant module presheaves therefore extends uniquely to the displayed
natural isomorphism; its inverse is obtained using the inverse ring identification. -/
theorem commutativeSiteConstantModuleFunctor_transport
    (R : Type (max u v)) [CommRing R] :
    Nonempty (commutativeSiteConstantModuleFunctor J R ⋙
        SheafOfModules.restrictScalars (realizationRingIso J R).inv ≅
      siteConstantModuleFunctorGeneral J R) := by
  have := (realizationRingUnit_locallyBijective J R).1
  have := (realizationRingUnit_locallyBijective J R).2
  let η := toSheafify J ((Functor.const Cᵒᵖ).obj (RingCat.of R))
  have hsq : η ≫ (realizationRingIso J R).inv.hom = realizationRingUnit J R := by
    dsimp only [η]
    rw [← realizationRingIso_fac J R, Category.assoc]
    change _ ≫ ((realizationRingIso J R).hom ≫ (realizationRingIso J R).inv).hom = _
    rw [Iso.hom_inv_id]
    exact Category.comp_id _
  let m := fun M ↦ moduleSheafificationComparison J η (realizationRingUnit J R)
    (realizationRingIso J R).inv hsq ((siteConstantModulePresheafGeneral (C := C) R).obj M)
  have hIso (M : ModuleCat.{max u v} R) : IsIso (m M) :=
    moduleSheafificationComparison_isIso J _ _ _ _ _
  refine ⟨(NatIso.ofComponents (fun M ↦ asIso (m M)) ?_).symm⟩
  intro M N f
  apply (SheafOfModules.toSheaf _).map_injective
  simp only [Functor.map_comp, asIso_hom, m, moduleSheafificationComparison_toSheaf]
  rfl

/-- Constant realization by exact-functor localization, at independent localization sizes.
Source: Stacks, paragraph before 09BD
(auxiliary; not a blueprint node). -/
def commutativeSiteDerivedConstantModuleFunctor (R : Type (max u v)) [CommRing R]
    [HasDerivedCategory.{wR} (ModuleCat.{max u v} R)]
    [HasDerivedCategory.{wS} (realizationModules J R)] :
    DerivedCategory (ModuleCat.{max u v} R) ⥤ DerivedCategory (realizationModules J R) :=
  haveI := (commutativeSiteConstantModuleFunctor_exact J R).1
  haveI := (commutativeSiteConstantModuleFunctor_exact J R).2.1
  haveI := (commutativeSiteConstantModuleFunctor_exact J R).2.2
  (commutativeSiteConstantModuleFunctor J R).mapDerivedCategory

end CategoryTheory
