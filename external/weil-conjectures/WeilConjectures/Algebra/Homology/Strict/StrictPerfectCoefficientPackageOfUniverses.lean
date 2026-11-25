/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.Strict.StrictPerfectPackageOnSiteSupplement
public import WeilConjectures.Algebra.Homology.Scalar.ScalarExtensionBinaryCoherenceSupplement
public import Mathlib.Algebra.Category.Ring.FilteredColimits
import Mathlib.CategoryTheory.Adjunction.Additive

/-!
# Strict-perfect models with independent site and coefficient universes

Source: Stacks Project, Tag 08G5; Weil blueprint, order 1263
(blueprint: def-weil-pbc-strict-perfect-coefficient-package).
The recorded general-site degreewise package is reused. The recorded small-site
local-perfectness and representation interfaces fix coefficients at the site-object
universe; these forms also allow independently larger coefficients.

## Main definitions

- `IsLocallyStrictPerfectComplexOfUniverses`
- `IsPerfectOnRingedSiteOfUniverses`
- `StrictPerfectCoefficientRepresentationOfUniverses`
-/

@[expose] public section
set_option autoImplicit false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe uC vC r w
open CategoryTheory CategoryTheory.Limits
namespace SheafOfModules

variable {C : Type uC} [Category.{vC} C] {J : GrothendieckTopology C}

variable [HasSheafify J AddCommGrpCat.{max uC vC r}]
  [∀ U : C, HasSheafify (J.over U) AddCommGrpCat.{max uC vC r}]
  [∀ U : C, (J.over U).WEqualsLocallyBijective AddCommGrpCat.{max uC vC r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max uC vC r}]

/-- Locally bounded models by finite-free retracts, on covering sieves.
Bounds and ranks may depend on the member of the cover. Source: Stacks Tag 08G5
(blueprint: def-weil-pbc-strict-perfect-coefficient-package). -/
def IsLocallyStrictPerfectComplexOfUniverses (R : Sheaf J CommRingCat.{max uC vC r})
    (K : CochainComplex (SheafOfModules.{max uC vC r}
      ((sheafCompose J
        (forget₂ CommRingCat.{max uC vC r} RingCat.{max uC vC r})).obj R)) ℤ) : Prop :=
  ∀ V : C, ∃ S : Sieve V, S ∈ J V ∧
    ∀ (U : C) (f : U ⟶ V), S f →
      ∃ F : CochainComplex (SheafOfModules.{max uC vC r}
          (((sheafCompose J
        (forget₂ CommRingCat.{max uC vC r} RingCat.{max uC vC r})).obj R).over U)) ℤ,
        (∃ a b : ℤ, ∀ n : ℤ, n < a ∨ b < n → IsZero (F.X n)) ∧
        Nonempty (StrictPerfectCoefficientPackageOnSite.{max uC vC, vC, max uC vC r} _ F) ∧
        ∃ α : F ⟶ ((SheafOfModules.overFunctor _ U).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj K, QuasiIso α

/-- Derived objects represented by locally strictly perfect complexes on a general site.
Source: Stacks Tag 08G5 (blueprint: def-weil-pbc-strict-perfect-coefficient-package). -/
def IsPerfectOnRingedSiteOfUniverses (R : Sheaf J CommRingCat.{max uC vC r})
    [HasDerivedCategory.{w} (SheafOfModules.{max uC vC r}
      ((sheafCompose J
        (forget₂ CommRingCat.{max uC vC r} RingCat.{max uC vC r})).obj R))]
    (K : DerivedCategory (SheafOfModules.{max uC vC r}
      ((sheafCompose J
        (forget₂ CommRingCat.{max uC vC r} RingCat.{max uC vC r})).obj R))) : Prop :=
  ∃ P : CochainComplex (SheafOfModules.{max uC vC r}
      ((sheafCompose J
        (forget₂ CommRingCat.{max uC vC r} RingCat.{max uC vC r})).obj R)) ℤ,
    IsLocallyStrictPerfectComplexOfUniverses.{uC, vC, r} R P ∧
      Nonempty (K ≅ DerivedCategory.Q.obj P)

end SheafOfModules

noncomputable section

universe c v s
open CategoryTheory CategoryTheory.Limits
namespace SheafOfModules

variable {C : Type c} [Category.{v} C] [EssentiallySmall.{s} C]
  (J : GrothendieckTopology C)
  [HasSheafify J CommRingCat.{s}] [HasSheafify J AddCommGrpCat.{s}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{s}]

/-- The constant commutative coefficient ring sheaf.
Source: Stacks 03CY (blueprint: def-weil-pbc-strict-perfect-coefficient-package). -/
abbrev scalarPerfectRing (R : Type s) [CommRing R] :=
  (constantSheaf J CommRingCat.{s}).obj (CommRingCat.of R)

/-- Forget commutativity of the given coefficient sheaf.
Source: Stacks 03DA (blueprint: def-weil-pbc-strict-perfect-coefficient-package). -/
abbrev scalarPerfectRingUnderlying (B : Sheaf J CommRingCat.{s}) :=
  (sheafCompose J (forget₂ CommRingCat.{s} RingCat.{s})).obj B

/-- Constant module presheaves with the given module action and identity restrictions.
Source: Stacks 03CY (blueprint: def-weil-pbc-strict-perfect-coefficient-package). -/
def scalarPerfectConstantPresheaf (R : Type s) [CommRing R] :
    ModuleCat.{s} R ⥤ PresheafOfModules.{s}
      ((Functor.const Cᵒᵖ).obj (RingCat.of R)) where
  obj M := { obj := fun _ ↦ M, map := fun _ ↦ ModuleCat.ofHom LinearMap.id }
  map f := { app := fun _ ↦ f }

/-- The ring sheafification unit, with commutativity forgotten.
Source: Stacks 03CY (blueprint: def-weil-pbc-strict-perfect-coefficient-package). -/
def scalarPerfectRingUnit (R : Type s) [CommRing R] :
    (Functor.const Cᵒᵖ).obj (RingCat.of R) ⟶
      (scalarPerfectRingUnderlying J (scalarPerfectRing J R)).obj :=
  Functor.whiskerRight (toSheafify J ((Functor.const Cᵒᵖ).obj (CommRingCat.of R)))
    (forget₂ CommRingCat RingCat)

set_option linter.unusedSectionVars false in
/-- Forgetting commutativity leaves local bijectivity of the ring unit unchanged.
Source: Stacks 03CY (blueprint: def-weil-pbc-strict-perfect-coefficient-package).
Proof: the sheafification unit is locally injective and locally surjective on sections;
forgetting commutativity preserves those functions and their witnessing covering sieves. -/
theorem scalarPerfectRingUnit_locallyBijective (R : Type s) [CommRing R] :
    Presheaf.IsLocallyInjective J (scalarPerfectRingUnit J R) ∧
      Presheaf.IsLocallySurjective J (scalarPerfectRingUnit J R) := by
  have : J.WEqualsLocallyBijective CommRingCat.{s} :=
    GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall.{v, s, c,
      s + 1, s, s, s} J
  exact ⟨⟨fun x y h ↦ Presheaf.equalizerSieve_mem J
    (toSheafify J ((Functor.const Cᵒᵖ).obj (CommRingCat.of R))) x y h⟩,
    ⟨fun x ↦ Presheaf.imageSieve_mem J
      (toSheafify J ((Functor.const Cᵒᵖ).obj (CommRingCat.of R))) x⟩⟩

/-- Sheafify the constant module presheaf over the sheafified constant ring.
Source: Stacks 03CY (blueprint: def-weil-pbc-strict-perfect-coefficient-package). -/
def scalarPerfectConstantFunctor (R : Type s) [CommRing R] :
    ModuleCat.{s} R ⥤ SheafOfModules.{s}
      (scalarPerfectRingUnderlying J (scalarPerfectRing J R)) :=
  letI := (scalarPerfectRingUnit_locallyBijective J R).1
  letI := (scalarPerfectRingUnit_locallyBijective J R).2
  scalarPerfectConstantPresheaf (C := C) R ⋙
    PresheafOfModules.sheafification (scalarPerfectRingUnit J R)

/-- Ordinary scalar extension, using the recorded sheafified tensor objects and maps.
Source: Stacks 03EK (blueprint: def-weil-pbc-strict-perfect-coefficient-package). -/
def scalarPerfectExtensionFunctor {A B : Sheaf J CommRingCat.{s}} (φ : A ⟶ B) :
    SheafOfModules.{s} (scalarPerfectRingUnderlying J A) ⥤
      SheafOfModules.{s} (scalarPerfectRingUnderlying J B) where
  obj M := changeOfRingsOfUniverses.{v, c, s, s} φ M
  map f := changeOfRingsHomOfUniverses.{v, c, s, s} φ _ f
  map_id M := scalarExtension_map_id φ M
  map_comp f g := scalarExtension_map_comp φ f g

/-- Termwise constant sheafification followed by ordinary scalar extension.
Source: Stacks 03CY and 03EK
(blueprint: def-weil-pbc-strict-perfect-coefficient-package). -/
def scalarPerfectFunctor (R : Type s) [CommRing R]
    {B : Sheaf J CommRingCat.{s}} (φ : scalarPerfectRing J R ⟶ B) :=
  scalarPerfectConstantFunctor J R ⋙ scalarPerfectExtensionFunctor J φ

/-- Additivity of the constant module functor at independent sizes.
Source: Stacks 03CY (blueprint: def-weil-pbc-strict-perfect-coefficient-package).
Proof: sums are pointwise in the constant presheaf, and module sheafification is additive. -/
@[instance] theorem scalarPerfectConstantFunctor_additive (R : Type s) [CommRing R] :
    (scalarPerfectConstantFunctor J R).Additive := by
  let := (scalarPerfectRingUnit_locallyBijective J R).1
  let := (scalarPerfectRingUnit_locallyBijective J R).2
  have : (scalarPerfectConstantPresheaf (C := C) R).Additive := by
    constructor
    intro M N f g
    apply PresheafOfModules.hom_ext
    intro U
    rfl
  have : (PresheafOfModules.sheafification (scalarPerfectRingUnit J R)).Additive :=
    (PresheafOfModules.sheafificationAdjunction _).left_adjoint_additive
  unfold scalarPerfectConstantFunctor
  infer_instance

set_option linter.unusedSectionVars false in
/-- Ordinary scalar extension is additive even for a nonflat coefficient map.
Source: Stacks 03EK (blueprint: def-weil-pbc-strict-perfect-coefficient-package).
Proof: sectionwise tensor maps preserve addition; additive sheafification preserves
this equality. This does not assert preservation of kernels or exact sequences. -/
@[instance] theorem scalarPerfectExtensionFunctor_additive
    {A B : Sheaf J CommRingCat.{s}} (φ : A ⟶ B) :
    (scalarPerfectExtensionFunctor J φ).Additive := by
  have : (PresheafOfModules.sheafification
      (R := scalarPerfectRingUnderlying J B) (𝟙 _)).Additive :=
    (PresheafOfModules.sheafificationAdjunction _).left_adjoint_additive
  constructor
  intro M N f g
  change (PresheafOfModules.sheafification
      (R := scalarPerfectRingUnderlying J B) (𝟙 _)).map _ =
    (PresheafOfModules.sheafification
      (R := scalarPerfectRingUnderlying J B) (𝟙 _)).map _ +
    (PresheafOfModules.sheafification
      (R := scalarPerfectRingUnderlying J B) (𝟙 _)).map _
  rw [← (PresheafOfModules.sheafification
    (R := scalarPerfectRingUnderlying J B) (𝟙 _)).map_add]
  congr 1
  apply PresheafOfModules.hom_ext
  intro U
  have : (ModuleCat.extendScalars (φ.hom.app U).hom).Additive :=
    (ModuleCat.extendRestrictScalarsAdj (φ.hom.app U).hom).left_adjoint_additive
  exact (ModuleCat.extendScalars (φ.hom.app U).hom).map_add
    (f := f.val.app U) (g := g.val.app U)

/-- Constant scalar extension is additive; no flatness is involved.
Source: Stacks 03CY, 03EK and 0GMW
(blueprint: def-weil-pbc-strict-perfect-coefficient-package).
Proof: constant presheaves preserve sums of linear maps componentwise; their module
sheafification is additive. Sectionwise scalar extension is additive on pure tensors,
and target module sheafification preserves this equality. Compose these functors. -/
@[instance] theorem scalarPerfectFunctor_additive (R : Type s) [CommRing R]
    {B : Sheaf J CommRingCat.{s}} (φ : scalarPerfectRing J R ⟶ B) :
    (scalarPerfectFunctor J R φ).Additive := by
  unfold scalarPerfectFunctor
  infer_instance

variable [∀ U : C, EssentiallySmall.{s} (Over U)]
  [∀ U : C, HasSheafify (J.over U) CommRingCat.{s}]
  [∀ U : C, HasSheafify (J.over U) AddCommGrpCat.{s}]
  [∀ U : C, (J.over U).WEqualsLocallyBijective AddCommGrpCat.{s}]

/-- The constant section supplied by the actual module-sheafification unit.
Source: Stacks 03CY (blueprint: def-weil-pbc-strict-perfect-coefficient-package). -/
def scalarPerfectConstantSection (R : Type s) [CommRing R]
    (M : ModuleCat.{s} R) (W : Cᵒᵖ) (m : M) :
    ((scalarPerfectConstantFunctor J R).obj M).val.obj W :=
  letI := (scalarPerfectRingUnit_locallyBijective J R).1
  letI := (scalarPerfectRingUnit_locallyBijective J R).2
  ((PresheafOfModules.sheafificationAdjunction (scalarPerfectRingUnit J R)).unit.app
    ((scalarPerfectConstantPresheaf (C := C) R).obj M)).app W m

end SheafOfModules
