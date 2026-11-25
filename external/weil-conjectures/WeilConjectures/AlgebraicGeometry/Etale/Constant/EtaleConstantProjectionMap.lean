/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.Tensor
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.Monoidal
public import WeilConjectures.CategoryTheory.DerivedCategory.Adjunction
public import WeilConjectures.CategoryTheory.Adjunction.ProjectionMap
public import WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheafOver
public import WeilConjectures.SixFunctors.Etale.Derived.GlobalSections
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat

/-!
# The derived constant-coefficient projection map

Source: Stacks Project, etale-cohomology.tex, Tag 0F12, and sites-cohomology.tex,
Tags 07A4, 07A6 and 0B56 (blueprint: def-kun-constant-projection-morphism).

The constant presheaf tensor constraints have identity components, so their coherence
proofs determine a unique structure. Sheafification and the existing total left derived
tensor comparison give the constant-sheaf comparison. The map is its counit mate under
the existing unbounded derived adjunction. No choice of an arbitrary comparison is made.
-/

@[expose] public section

universe u uA

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

section CachedComparison

variable {C : Type*} [Category.{u + 1} C] [Abelian C]
  [IsGrothendieckAbelian.{u + 1} C]
  [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalClosed C] [BraidedCategory C]
  [Abelian.HasFunctorialFlatResolution C]
  {D : Type*} [Category.{u + 1} D] [Abelian D]
  [IsGrothendieckAbelian.{u + 1} D]
  [MonoidalCategory D] [MonoidalPreadditive D] [MonoidalClosed D] [BraidedCategory D]
  [Abelian.HasFunctorialFlatResolution D]
  (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [F.PreservesFlat] [F.IsLeftAdjoint] [F.Monoidal]

end CachedComparison

namespace AlgebraicGeometry.Etale

/-- The constant presheaf has the unique monoidal core whose unit and tensor constraints
have identity components. Source: the constant inverse image in Stacks Tag 0F12 and the
ordinary tensor comparison underlying Tag 07A4
(blueprint: def-kun-constant-projection-morphism).
Proof: use identity maps in every component for the unit and tensor constraints and their
inverses. Restriction maps of constant presheaves are identities. Naturality therefore
reduces to the same map on both sides. Evaluate the associativity and unit diagrams at
any site object: they reduce to the corresponding diagrams in ModuleCat. These component
identities also determine the isomorphisms uniquely, and proof fields are propositions. -/
theorem exists_etaleConstantPresheafCoreMonoidal (Λ : Type (u + 1)) [CommRing Λ]
    (X : Scheme.{u}) :
    ∃ h : (Functor.const X.Etaleᵒᵖ (C := ModuleCat.{u + 1} Λ)).CoreMonoidal,
      (∀ U : X.Etaleᵒᵖ, h.εIso.hom.app U = 𝟙 _) ∧
      (∀ (M N : ModuleCat.{u + 1} Λ) (U : X.Etaleᵒᵖ),
        (h.μIso M N).hom.app U = 𝟙 _) := by
  refine ⟨{ εIso := NatIso.ofComponents fun _ ↦ Iso.refl _
            μIso _ _ := NatIso.ofComponents fun _ ↦ Iso.refl _ }, ?_, ?_⟩
  · intro U
    rfl
  · intro M N U
    rfl

/-- The constant-presheaf monoidal structure with identity components. Its data are
uniquely fixed by the normalization in the preceding theorem.
Source: Stacks Tag 0F12 (blueprint: def-kun-constant-projection-morphism). -/
noncomputable instance etaleConstantPresheafMonoidal (Λ : Type (u + 1)) [CommRing Λ]
    (X : Scheme.{u}) :
    (Functor.const X.Etaleᵒᵖ (C := ModuleCat.{u + 1} Λ)).Monoidal :=
  (Classical.choose (exists_etaleConstantPresheafCoreMonoidal Λ X)).toMonoidal

/-- The monoidal constant-sheaf functor is the composite of the normalized constant
presheaf functor and monoidal sheafification.
Source: Stacks Tag 07A4 (blueprint: def-kun-constant-projection-morphism). -/
noncomputable instance etaleConstantSheafMonoidal (Λ : Type (u + 1)) [CommRing Λ]
    (X : Scheme.{u}) :
    (constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).Monoidal :=
  inferInstanceAs
    (Functor.const X.Etaleᵒᵖ ⋙ presheafToSheaf X.smallEtaleTopology
      (ModuleCat.{u + 1} Λ)).Monoidal

/-- Constant module sheaves of flat modules are flat for sheaf tensor.
Source: the constant inverse image in Stacks Tag 0F12 and Tag 07A4
(blueprint: def-kun-constant-projection-morphism).
Proof: at every geometric point the stalk of a constant module sheaf is the original
module, and the sheaf tensor has stalk equal to the tensor of the stalks. If the module
is flat, tensoring with it preserves exact sequences of stalks. Geometric stalks form
a conservative family of exact functors on the small etale site, so tensoring with the
constant module sheaf preserves exact sequences of sheaves. This is categorical flatness.
The empty scheme has the zero sheaf category, where the same assertion holds. -/
theorem etaleConstantSheaf_preservesFlat (Λ : Type (u + 1)) [CommRing Λ]
    (X : Scheme.{u}) :
    (constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).PreservesFlat := by
  refine ⟨fun {M} hM ↦ (flat_iff_forall_flat_sheafFiber_obj _).2 ?_⟩
  intro Ω _ _ s
  exact ObjectProperty.prop_of_iso ObjectProperty.flat
    ((Scheme.pointSmallEtale s).ulift.{u + 1}.sheafFiberConstantSheafIso M).symm hM

attribute [instance] etaleConstantSheaf_preservesFlat

-- Use the additive structure supplied by the abelian instance throughout derivation.
attribute [local instance 40000] Preadditive.preadditiveHasZeroMorphisms
attribute [local instance 30000] Abelian.toPreadditive
attribute [local instance 20000] SymmetricCategory.toBraidedCategory
attribute [local instance 21000] sheafBraidedCategory

variable (A : Type uA) [Category.{u + 1} A] [Abelian A]
  [IsGrothendieckAbelian.{u + 1} A] [HasSmallSiteSheafify A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A]

/-- The unbounded adjunction of derived constant sheaves and derived global sections.
Source: Stacks Tag 07A6 (blueprint: def-kun-constant-projection-morphism).
Exactness identifies the left derived functor with termwise constant sheaves. -/
noncomputable def derivedConstantGlobalSectionsAdjunction (X : Scheme.{u}) :
    (constantSheaf X.smallEtaleTopology A).leftDerivedFunctor ⊣
      rightDerivedGlobalSections A X :=
  (constantSheafΓAdj X.smallEtaleTopology A).derivedAdjunction

end AlgebraicGeometry.Etale
