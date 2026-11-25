/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes
public import WeilConjectures.AlgebraicGeometry.LocallyClosedStratification
public import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
public import WeilConjectures.AlgebraicGeometry.ProEtaleSiteComparison
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.CategoryTheory.Functor.ReflectsIso.Balanced

/-!
# Finite coefficients on the small pro-etale site

Source: blueprint, sec-proper-base-change/sk-thm-properbasechange,
node definition-small-pro-etale-site--1 (blueprint: definition-small-pro-etale-site--1).

## Main definitions

* `finiteCoefficientRingSheaf`: sheafified continuous functions on connected components.
* `FiniteCoefficientModules`: left modules over this ring sheaf.
* `FiniteCoefficientDerivedCategory` and `FiniteCoefficientDerivedCategoryPlus`: the
  unbounded localization and its strictly full bounded below subcategory.
* `finiteCoefficientEtaleRingSheaf` and `FiniteCoefficientEtaleDerivedCategory`: etale
  coefficients, using the canonical fixed-ring module-sheaf presentation.
* `finiteCoefficientDerivedComparison`: the exact module inverse image on complexes.
* `isBoundedConstructibleFiniteCoefficient`: the essential image of bounded constructible
  etale complexes, with its full subcategory `FiniteCoefficientBoundedConstructibleDerivedCategory`.
-/

@[expose] public section

universe u vC uC

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.ProEtale

/-- A diagram of left modules is a module presheaf over the constant ring presheaf.
Source: blueprint, `definition-small-pro-etale-site--1`
(blueprint: definition-small-pro-etale-site--1). -/
noncomputable def finiteCoefficientModulePresheaf (C : Type uC) [Category.{vC} C]
    (Λ : Type (u + 1)) [Ring Λ] :
    (Cᵒᵖ ⥤ ModuleCat.{u + 1} Λ) ⥤
      PresheafOfModules.{u + 1} ((Functor.const Cᵒᵖ).obj (RingCat.of Λ)) where
  obj F :=
    { obj U := F.obj U
      map f := ModuleCat.ofHom (F.map f).hom
      map_id U := by ext x; exact ConcreteCategory.congr_hom (F.map_id U) x
      map_comp f g := by ext x; exact ConcreteCategory.congr_hom (F.map_comp f g) x }
  map f :=
    { app U := f.app U
      naturality g := by ext x; exact ConcreteCategory.congr_hom (f.naturality g) x }
  map_id F := by ext U x; rfl
  map_comp f g := by ext U x; rfl

private noncomputable def coefficientModulePresheafFullyFaithful
    (C : Type uC) [Category.{vC} C] (Λ : Type (u + 1)) [Ring Λ] :
    (finiteCoefficientModulePresheaf C Λ).FullyFaithful where
  preimage φ :=
    { app := φ.app
      naturality _ _ f := by ext x; exact ConcreteCategory.congr_hom (φ.naturality f) x }
  map_preimage φ := by ext U x; rfl
  preimage_map φ := by ext U x; rfl

private theorem coefficientRealization_isEquivalence
    {C : Type (u + 1)} [Category.{u} C] (J : GrothendieckTopology C)
    (Λ : Type (u + 1)) [Ring Λ] (R : Sheaf J RingCat.{u + 1})
    (α : (Functor.const Cᵒᵖ).obj (RingCat.of Λ) ⟶ R.obj)
    [Presheaf.IsLocallyInjective J α] [Presheaf.IsLocallySurjective J α]
    [HasSheafify J AddCommGrpCat.{u + 1}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u + 1}] :
    (sheafToPresheaf J (ModuleCat.{u + 1} Λ) ⋙
      finiteCoefficientModulePresheaf C Λ ⋙
      PresheafOfModules.sheafification.{u + 1} α).IsEquivalence := by
  have : (finiteCoefficientModulePresheaf C Λ).Full :=
    (coefficientModulePresheafFullyFaithful C Λ).full
  have : (finiteCoefficientModulePresheaf C Λ).Faithful :=
    (coefficientModulePresheafFullyFaithful C Λ).faithful
  let E := sheafToPresheaf J (ModuleCat.{u + 1} Λ) ⋙
    finiteCoefficientModulePresheaf C Λ
  let S := PresheafOfModules.sheafification.{u + 1} α
  let G := SheafOfModules.forget R ⋙ PresheafOfModules.restrictScalars α
  have hunit (F : Sheaf J (ModuleCat.{u + 1} Λ)) :
      IsIso ((PresheafOfModules.sheafificationAdjunction α).unit.app (E.obj F)) := by
    rw [← isIso_iff_of_reflects_iso _ (PresheafOfModules.toPresheaf _)]
    simp only [PresheafOfModules.toPresheaf_map_sheafificationAdjunction_unit_app]
    apply isIso_toSheafify
    exact ((sheafCompose J
      (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj F).property
  let η : E ⟶ (E ⋙ S) ⋙ G :=
    Functor.whiskerLeft E (PresheafOfModules.sheafificationAdjunction α).unit
  have : IsIso η := by
    rw [NatTrans.isIso_iff_isIso_app]
    exact hunit
  have : (E ⋙ S).Faithful := Functor.Faithful.of_comp_iso (asIso η).symm
  have : (E ⋙ S).Full := Functor.Full.of_comp_faithful_iso (asIso η).symm
  have : (E ⋙ S).EssSurj := by
    refine ⟨fun M ↦ ?_⟩
    let P := (PresheafOfModules.restrictScalars α).obj M.val
    let F : Cᵒᵖ ⥤ ModuleCat.{u + 1} Λ :=
      { obj := P.obj
        map f := P.map f
        map_id U := by ext x; exact ConcreteCategory.congr_hom (P.presheaf.map_id U) x
        map_comp f g := by ext x; exact ConcreteCategory.congr_hom (P.presheaf.map_comp f g) x }
    let F' : Sheaf J (ModuleCat.{u + 1} Λ) :=
      ⟨F, Presheaf.isSheaf_of_isSheaf_comp J F
        (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}) M.isSheaf⟩
    refine ⟨F', ⟨?_⟩⟩
    exact asIso ((PresheafOfModules.sheafificationAdjunction α).counit.app M)
  change (E ⋙ S).IsEquivalence
  exact Functor.IsEquivalence.mk

variable (T : Scheme.{u}) (Λ : Type (u + 1)) [Ring Λ] [Finite Λ]
  [TopologicalSpace Λ] [DiscreteTopology Λ]

/-- Continuous functions on the quotient space of connected components, with pointwise
ring operations and restriction by precomposition. Source: blueprint,
`definition-small-pro-etale-site--1` (blueprint: definition-small-pro-etale-site--1). -/
noncomputable def finiteCoefficientPresheaf (T : Scheme.{u}) (Λ : Type (u + 1))
    [Ring Λ] [Finite Λ] [TopologicalSpace Λ] [DiscreteTopology Λ] :
    T.ProEtᵒᵖ ⥤ RingCat.{u + 1} where
  obj U := RingCat.of C(ConnectedComponents U.unop.left, Λ)
  map f := RingCat.ofHom
    { toFun := fun s ↦ s.comp
        ⟨f.unop.left.continuous.connectedComponentsMap,
          f.unop.left.continuous.connectedComponentsMap_continuous⟩
      map_one' := rfl
      map_mul' := fun _ _ ↦ rfl
      map_zero' := rfl
      map_add' := fun _ _ ↦ rfl }
  map_id U := by
    ext s c
    obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe c
    rfl
  map_comp f g := by
    ext s c
    obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe c
    rfl

/-- The coefficient ring sheaf is the sheafification of continuous functions on connected
components. Source: blueprint, `definition-small-pro-etale-site--1`
(blueprint: definition-small-pro-etale-site--1). -/
noncomputable def finiteCoefficientRingSheaf : Sheaf (Scheme.ProEt.topology T) RingCat.{u + 1} :=
  (presheafToSheaf (Scheme.ProEt.topology T) RingCat.{u + 1}).obj
    (finiteCoefficientPresheaf T Λ)

/-- Constant scalar sections of the continuous-function coefficient presheaf.
Source: blueprint, `definition-small-pro-etale-site--1`
(blueprint: definition-small-pro-etale-site--1). -/
noncomputable def finiteCoefficientConstants :
    (Functor.const T.ProEtᵒᵖ).obj (RingCat.of Λ) ⟶ finiteCoefficientPresheaf T Λ where
  app U := RingCat.ofHom
    { toFun := fun r ↦ ContinuousMap.const _ r
      map_one' := rfl
      map_mul' := fun _ _ ↦ rfl
      map_zero' := rfl
      map_add' := fun _ _ ↦ rfl }
  naturality _ _ f := by ext r; rfl

/-- The canonical scalar map from the constant presheaf to the coefficient ring sheaf.
Source: blueprint, `definition-small-pro-etale-site--1`
(blueprint: definition-small-pro-etale-site--1). -/
noncomputable def finiteCoefficientScalarMap :
    (Functor.const T.ProEtᵒᵖ).obj (RingCat.of Λ) ⟶ (finiteCoefficientRingSheaf T Λ).obj :=
  finiteCoefficientConstants T Λ ≫
    toSheafify (Scheme.ProEt.topology T) (finiteCoefficientPresheaf T Λ)

/-- Constant scalar sections identify the coefficient sheaf with the sheafification of
constant scalars. Source: blueprint, `definition-small-pro-etale-site--1`
(blueprint: definition-small-pro-etale-site--1).

Proof: continuous functions to a discrete ring are locally constant. Their level sets,
pulled back along the quotient map to connected components, are open and give an open
cover of the scheme, hence a pro-etale cover. On each member the function is a constant
scalar. Two constant scalars with equal restrictions are equal locally, including the
empty object, whose empty cover is allowed. Thus the constants-to-functions map is
locally bijective. The sheafification unit is locally bijective and these properties
are closed under composition. This also treats the zero ring and disconnected schemes. -/
theorem finiteCoefficientScalarMap_locallyBijective :
    Presheaf.IsLocallyInjective (Scheme.ProEt.topology T) (finiteCoefficientScalarMap T Λ) ∧
    Presheaf.IsLocallySurjective (Scheme.ProEt.topology T) (finiteCoefficientScalarMap T Λ) := by
  classical
  have hinj : Presheaf.IsLocallyInjective (Scheme.ProEt.topology T)
      (finiteCoefficientConstants T Λ) := by
    refine ⟨?_⟩
    intro U a b hab
    by_cases hU : Nonempty U.unop.left
    · obtain ⟨x⟩ := hU
      have hab' := congrArg (fun s : C(ConnectedComponents U.unop.left, Λ) ↦ s ⟦x⟧) hab
      change a = b at hab'
      subst b
      simpa only [Presheaf.equalizerSieve_self_eq_top] using
        (Scheme.ProEt.topology T).top_mem U.unop
    · have : IsEmpty U.unop.left := not_nonempty_iff.mp hU
      exact (Scheme.ProEt.topology T).superset_covering bot_le
        (Scheme.ProEt.bot_mem_topology U.unop)
  have hsurj : Presheaf.IsLocallySurjective (Scheme.ProEt.topology T)
      (finiteCoefficientConstants T Λ) := by
    refine ⟨?_⟩
    intro U s
    let f : C(U.left, Λ) := s.comp ⟨_, ConnectedComponents.continuous_coe⟩
    let O (x : U.left) : U.left.Opens :=
      ⟨f ⁻¹' {f x}, (isOpen_discrete _).preimage f.continuous⟩
    apply Scheme.ProEt.mem_topology_of_openImmersion _ (fun x ↦ (O x).ι)
    · intro x
      exact ⟨x, ⟨⟨x, rfl⟩, rfl⟩⟩
    · intro x
      refine ⟨f x, ?_⟩
      apply ContinuousMap.ext
      intro c
      obtain ⟨y, rfl⟩ := ConnectedComponents.surjective_coe c
      change f x = f y.val
      exact y.property.symm
  constructor <;> dsimp only [finiteCoefficientScalarMap] <;> infer_instance

/-- Local injectivity needed for the associated module sheaf construction.
Source: blueprint, `definition-small-pro-etale-site--1`
(blueprint: definition-small-pro-etale-site--1). -/
noncomputable instance finiteCoefficientScalarMap_isLocallyInjective :
    Presheaf.IsLocallyInjective (Scheme.ProEt.topology T) (finiteCoefficientScalarMap T Λ) :=
  (finiteCoefficientScalarMap_locallyBijective T Λ).1

/-- Local surjectivity needed for the associated module sheaf construction.
Source: blueprint, `definition-small-pro-etale-site--1`
(blueprint: definition-small-pro-etale-site--1). -/
noncomputable instance finiteCoefficientScalarMap_isLocallySurjective :
    Presheaf.IsLocallySurjective (Scheme.ProEt.topology T) (finiteCoefficientScalarMap T Λ) :=
  (finiteCoefficientScalarMap_locallyBijective T Λ).2

end AlgebraicGeometry.ProEtale
