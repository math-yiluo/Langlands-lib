/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.CoefficientRingedTensorHomModel
public import WeilConjectures.CategoryTheory.InternalSectionModuleFlat
public import WeilConjectures.CategoryTheory.InternalSectionTensorComparison
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
import all WeilConjectures.CategoryTheory.InternalSectionTensorComparison
import all Mathlib.Logic.Small.Defs

/-! # Canonical internal-to-sectionwise total-complex comparison

Source: Stacks Project, Tags 08J9, 08JA and 08JB; blueprint module objects and
derived tensor--Hom (auxiliary; not a blueprint node).

## Main definitions

* `totalComparison`: the fixed comparison of the concrete sum-total complexes.

-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false

universe u
open scoped CategoryTheory.Obj
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry AlgebraicGeometry.ProEtale
open CategoryTheory.InternalAbelianSheafModule WeilConjectures

namespace AlgebraicGeometry.ProEtale.ModuleObjectRingedComparison

section GenericComparisonAPI

/-- Named sheaf-composition evidence for the reconstructed section-ring comparison.
Source: the small-model comparison of sites (auxiliary; not a blueprint node).
Proof: replace the essentially small site by its small model. The induced topology
preserves the sheaf condition, so composition with the forgetful ring functor
carries sheaves to sheaves, and the site equivalence transports this fact back. -/
theorem sectionRingHasSheafCompose {C : Type (u + 1)} [Category.{u} C]
    (J : GrothendieckTopology C) :
    J.HasSheafCompose (forget₂ CommRingCat.{u + 1} RingCat.{u + 1}) :=
  (equivSmallModel.{u + 1} C).hasSheafCompose J
    ((equivSmallModel.{u + 1} C).inverse.inducedTopology J)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})

attribute [local instance 1000001] sectionRingHasSheafCompose

attribute [local implicit_reducible] sectionModuleEquivalence
attribute [local irreducible] sectionRingSheaf
  SheafOfModules.monoidalCategory Sheaf.monoidalCategory
  CategoryTheory.Mod.monoidalCategoryStruct CategoryTheory.Mod.monoidalClosed
attribute [local implicit_reducible] CategoryTheory.Mod.monoidalCategory
  CategoryTheory.Monoidal.induced
attribute [local implicit_reducible] GrothendieckTopology.monoidalCategory_sheaf_of_essentiallySmall
  GrothendieckTopology.braidedCategory_sheaf_of_essentiallySmall
  GrothendieckTopology.symmetricCategory_sheaf_of_essentiallySmall
  ProEtale.sheafMonoidalCategory ProEtale.sheafBraidedCategory ProEtale.sheafSymmetricCategory

attribute [local implicit_reducible] Sheaf.symmetricCategory Sheaf.braidedCategory

section TotalData

variable {A B : Type*} [Category A] [Category B] [Preadditive A] [Preadditive B]
  [MonoidalCategory A] [MonoidalCategory B]
  [MonoidalPreadditive A] [MonoidalPreadditive B]
  (F : A ⥤ B) [F.Additive] [F.IsEquivalence]
  (e : ∀ M N : A, F.obj (M ⊗ N) ≅ F.obj M ⊗ F.obj N)
  (P Q : CochainComplex A ℤ) [P.HasMapBifunctor Q (curriedTensor A)]
  [CochainComplex.HasMapBifunctor ((F.mapHomologicalComplex (.up ℤ)).obj P)
    ((F.mapHomologicalComplex (.up ℤ)).obj Q) (curriedTensor B)]

end TotalData

section OrdinaryAtSite

variable {C : Type (u + 1)} [Category.{u} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{u + 1}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u + 1}]

attribute [local instance 30001] Sheaf.monoidalCategory
/-- The canonical braiding used by the section tensor comparison, via its symmetric structure.
Source: Stacks 03EK (auxiliary; not a blueprint node). -/
abbrev sectionComparisonBraiding : BraidedCategory (Sheaf J AddCommGrpCat.{u + 1}) :=
  (Sheaf.symmetricCategory J AddCommGrpCat.{u + 1}).toBraidedCategory

attribute [local instance 30000] sectionComparisonBraiding

variable (R : Sheaf J AddCommGrpCat.{u + 1}) [MonObj R] [hcomm : IsCommMonObj R]

/-- Commutativity for the direct canonical braiding on abelian sheaves.
Source: Stacks 03EK (auxiliary; not a blueprint node).
Proof: its braiding agrees with the parent of the canonical symmetric structure,
so the original commutativity proof has the required type. -/
theorem sectionRingCommDirect :
    @IsCommMonObj (Sheaf J AddCommGrpCat.{u + 1}) _ _
      (Sheaf.braidedCategory J AddCommGrpCat.{u + 1}) R _ := by
  exact hcomm

attribute [local instance] sectionRingCommDirect

/-- The primitive section functor is additive, with evidence named before totalization.
Source: Stacks 00YV (auxiliary; not a blueprint node).
Proof: it is the functor of the section-module equivalence, whose additivity follows
from preservation of binary products in these preadditive categories. -/
theorem sectionFunctorAdditiveForSite :
    (sectionModuleFunctor.{u + 1, u + 1, u} J R).Additive :=
  comparison_EAdditive J R

/-- The primitive section functor is an equivalence.
Source: Stacks 00YV (auxiliary; not a blueprint node).
Proof: the section-module equivalence has this definitionally identical functor. -/
theorem sectionFunctorEquivalenceForSite :
    (sectionModuleFunctor.{u + 1, u + 1, u} J R).IsEquivalence :=
  comparison_EEquiv J R

attribute [local instance] sectionFunctorAdditiveForSite sectionFunctorEquivalenceForSite

attribute [local irreducible] sectionModuleFunctor

end OrdinaryAtSite

end GenericComparisonAPI

section ProEtaleComparisonAPI

variable (Λ : Sheaf (coherentTopology Profinite.{u}) AddCommGrpCat.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ] (X : Scheme.{u})

/-- The canonical symmetric braiding on the pro-etale site.
Source: Stacks 03EK (auxiliary; not a blueprint node). -/
abbrev sectionProEtaleBraiding :
    BraidedCategory (Sheaf (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1}) :=
  sectionComparisonBraiding (Scheme.ProEt.topology X)

/-- The pulled-back coefficient monoid is commutative for this canonical braiding.
Source: Stacks 03CV, 03EK (auxiliary; not a blueprint node).
Proof: the pullback functor preserves the original coefficient commutativity equation.
The symmetric parent's braiding is definitionally the direct canonical braiding. -/
theorem sectionProEtaleRingComm :
    @IsCommMonObj (Sheaf (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1}) _ _
      (sectionProEtaleBraiding X) (condensedRingObj Λ X) _ := by
  have h : IsCommMonObj (condensedRingObj Λ X) := inferInstance
  exact h

attribute [local instance 30000] sectionProEtaleBraiding
attribute [local instance] sectionProEtaleRingComm

end ProEtaleComparisonAPI

variable (Λ : Sheaf (coherentTopology Profinite.{u}) AddCommGrpCat.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ] (X : Scheme.{u})

/-- The original pulled-back coefficient monoid, named before forming module types.
This is precisely the lax pullback monoid constructor already inferred here.
Source: Stacks 03CV (auxiliary; not a blueprint node). -/
@[instance_reducible]
def coefficientMonoid : MonObj (condensedRingObj Λ X) := inferInstance

attribute [instance 1000001] coefficientMonoid

/-- The reconstructed section-ring sheaf of the pulled-back coefficient ring.
Source: Stacks 03CV (auxiliary; not a blueprint node). -/
abbrev ring : Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1} :=
  sectionRingSheaf.{u + 1, u + 1, u} (Scheme.ProEt.topology X) (condensedRingObj Λ X)

/-- Internal module objects, with the relative coequalizer tensor.
Source: blueprint module objects
(auxiliary; not a blueprint node). -/
abbrev Internal := CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1})
  (condensedRingObj Λ X)

/-- Sectionwise module sheaves over the reconstructed ring.
Source: Stacks 03CV (auxiliary; not a blueprint node). -/
abbrev Modules := SheafOfModules.{u + 1}
  ((sheafCompose (Scheme.ProEt.topology X)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (ring Λ X))

/-- The fixed equivalence, unchanged on underlying sheaves and maps.
Source: Stacks 00YV (auxiliary; not a blueprint node). -/
abbrev equivalence : Internal Λ X ≌ Modules Λ X :=
  sectionModuleEquivalence.{u + 1, u + 1, u}
    (Scheme.ProEt.topology X) (condensedRingObj Λ X)

/-- The forward section functor, before constructing its inverse.
Source: Stacks 00YV (auxiliary; not a blueprint node). -/
def sectionForward : Internal Λ X ⥤ Modules Λ X :=
  sectionModuleFunctor.{u + 1, u + 1, u}
    (Scheme.ProEt.topology X) (condensedRingObj Λ X)

/-- The primitive and equivalence presentations have the same forward functor.
Source: Stacks 00YV (auxiliary; not a blueprint node).
Proof: project the forward functor of the section equivalence. -/
theorem sectionForward_eq : sectionForward Λ X = (equivalence Λ X).functor := by
  rfl

/-- The primitive forward functor is additive.
Source: Stacks 00YV (auxiliary; not a blueprint node).
Proof: use the generic section-functor additivity theorem. -/
@[instance] theorem sectionForward_additive : (sectionForward Λ X).Additive := by
  exact sectionFunctorAdditiveForSite (hcomm := isCommMonObj_condensedRingObj Λ X)
    (Scheme.ProEt.topology X) (condensedRingObj Λ X)

/-- The primitive forward functor is an equivalence.
Source: Stacks 00YV (blueprint: def-sfb-internal-section-total-comparison).
Proof: use the generic section-functor equivalence theorem. -/
@[instance] theorem sectionForward_isEquivalence : (sectionForward Λ X).IsEquivalence := by
  exact sectionFunctorEquivalenceForSite (hcomm := isCommMonObj_condensedRingObj Λ X)
    (Scheme.ProEt.topology X) (condensedRingObj Λ X)

/-- Additivity of the recorded section equivalence through its forward-functor API.
Source: Stacks 00YV (auxiliary; not a blueprint node).
Proof: rewrite by sectionForward_eq and use primitive section additivity. -/
@[instance] theorem equivalenceAdditive : (equivalence Λ X).functor.Additive := by
  rw [← sectionForward_eq]
  infer_instance

/-- Grothendieck abelianness supplies the small ordinary derived-category universe.
Source: Stacks 07A5 (blueprint: def-sfb-internal-section-total-comparison).
Proof: apply Grothendieck abelianness of module sheaves on a site small in
the coefficient universe. Restriction of scalars from the commutative ring
sheaf to its underlying ring sheaf does not change this category. -/
@[instance] theorem sectionModulesGrothendieck {C : Type (u + 1)} [Category.{u} C]
    (J : GrothendieckTopology C) (R : Sheaf J CommRingCat.{u + 1}) :
    IsGrothendieckAbelian.{u + 1} (SheafOfModules.{u + 1}
      ((sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R)) := by
  classical
  let S : Sheaf J RingCat.{u + 1} :=
    (sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R
  have : HasFilteredColimitsOfSize.{u + 1, u + 1} (SheafOfModules.{u + 1} S) :=
    ⟨fun _ _ _ ↦ inferInstance⟩
  have : AB5OfSize.{u + 1, u + 1} (SheafOfModules.{u + 1} S) :=
    ⟨fun K _ _ ↦ HasExactColimitsOfShape.domain_of_functor K (SheafOfModules.toSheaf S)⟩
  let T (U : C) := (PresheafOfModules.sheafification.{u + 1} (𝟙 S.obj)).obj
    ((PresheafOfModules.free S.obj).obj (uliftYoneda.{u + 1}.obj U))
  have hs : ObjectProperty.IsSeparating (.ofObj T) := by
    intro M N f g h
    apply (SheafOfModules.forget S ⋙ PresheafOfModules.toPresheaf S.obj).map_injective
    ext ⟨U⟩ x
    let adj := PresheafOfModules.sheafificationAdjunction.{u + 1} (𝟙 S.obj)
    let e (M : SheafOfModules.{u + 1} S) :=
      (adj.homEquiv
        ((PresheafOfModules.free S.obj).obj (uliftYoneda.{u + 1}.obj U)) M).trans
        (PresheafOfModules.freeHomEquiv.trans uliftYonedaEquiv)
    have hn (a : T U ⟶ M) (k : M ⟶ N) :
        (e N) (a ≫ k) = k.val.app (.op U) ((e M) a) := by
      dsimp only [e, Equiv.trans_apply]
      rw [adj.homEquiv_naturality_right]
      let a' := (adj.homEquiv _ _) a
      let k' := (SheafOfModules.forget S ⋙
        PresheafOfModules.restrictScalars (𝟙 S.obj)).map k
      change uliftYonedaEquiv (PresheafOfModules.freeHomEquiv (a' ≫ k')) = _
      have hh := (PresheafOfModules.freeAdjunction S.obj).homEquiv_naturality_right a' k'
      rw [PresheafOfModules.freeAdjunction_homEquiv,
        PresheafOfModules.freeAdjunction_homEquiv] at hh
      erw [hh, uliftYonedaEquiv_comp]
    have hh := congrArg (e N) (h _ (ObjectProperty.ofObj_apply T U) ((e M).symm x))
    rw [hn, hn, Equiv.apply_symm_apply] at hh
    exact hh
  have : HasSeparator (SheafOfModules.{u + 1} S) :=
    ⟨_, hs.isSeparator_coproduct⟩
  exact {}

/-- Fix the dependency's existing totalization instance for this internal category.
Source: Stacks 012Z; lem-pe-internal-section-tensor-comparison
(auxiliary; not a blueprint node). -/
instance internalTotalExists (P Q : CochainComplex (Internal Λ X) ℤ) :
    P.HasMapBifunctor Q (curriedTensor (Internal Λ X)) := by
  exact @comparison_internalTotalExists _ _ (Scheme.ProEt.topology X) _ _ _
    (condensedRingObj Λ X) _ (isCommMonObj_condensedRingObj Λ X) P Q

/-- The native total tensor on internal complexes.
Source: Stacks 06YL (auxiliary; not a blueprint node). -/
instance internalComplexMonoidal : MonoidalCategory (CochainComplex (Internal Λ X) ℤ) := by
  exact @CategoryTheory.Mod.monoidalCategoryCochainComplex _ _ _ _ _ _ _
    (condensedRingObj Λ X) _ (isCommMonObj_condensedRingObj Λ X) _

/-- The native total tensor, with its instance fixed explicitly.
Source: Stacks 06YL (auxiliary; not a blueprint node). -/
def internalTotalTensor (P Q : CochainComplex (Internal Λ X) ℤ) :
    CochainComplex (Internal Λ X) ℤ :=
  (internalComplexMonoidal Λ X).tensorObj P Q

/-- The functorial K-injective sheaf-Hom model, retaining both site universes.
Source: Stacks 08J7 (auxiliary; not a blueprint node). -/
def hom : (DerivedCategory (Modules Λ X))ᵒᵖ × DerivedCategory (Modules Λ X) ⥤
    DerivedCategory (Modules Λ X) :=
  derivedInternalHomOfUniverses.{u + 1, u, u, u + 1}
    (Scheme.ProEt.topology X) (ring Λ X)

/-- The exact equivalence applied termwise to cochain complexes.
Source: Stacks 05RU (auxiliary; not a blueprint node). -/
def complexForward :
    CochainComplex (Internal Λ X) ℤ ⥤ CochainComplex (Modules Λ X) ℤ :=
  (sectionForward Λ X).mapHomologicalComplex (.up ℤ)

attribute [local instance 1000001] sectionRingHasSheafCompose

attribute [local implicit_reducible] sectionModuleEquivalence
attribute [local irreducible] sectionRingSheaf
  SheafOfModules.monoidalCategory Sheaf.monoidalCategory
  CategoryTheory.Mod.monoidalCategoryStruct CategoryTheory.Mod.monoidalClosed
attribute [local implicit_reducible] CategoryTheory.Mod.monoidalCategory
  CategoryTheory.Monoidal.induced
attribute [local implicit_reducible] GrothendieckTopology.monoidalCategory_sheaf_of_essentiallySmall
  GrothendieckTopology.braidedCategory_sheaf_of_essentiallySmall
  GrothendieckTopology.symmetricCategory_sheaf_of_essentiallySmall
  ProEtale.sheafMonoidalCategory ProEtale.sheafBraidedCategory ProEtale.sheafSymmetricCategory

attribute [local implicit_reducible] Sheaf.symmetricCategory Sheaf.braidedCategory

end AlgebraicGeometry.ProEtale.ModuleObjectRingedComparison
