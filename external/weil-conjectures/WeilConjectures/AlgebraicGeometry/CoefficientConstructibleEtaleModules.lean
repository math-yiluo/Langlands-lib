/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.CoefficientProEtaleTorAmplitude
public import WeilConjectures.AlgebraicGeometry.EtaleConstantRingModuleEquivalence
public import WeilConjectures.AlgebraicGeometry.FiniteLocallyClosedStratification
public import WeilConjectures.AlgebraicGeometry.LocallyClosedStratification
public import WeilConjectures.CategoryTheory.ConstantCoefficientScalarExtension

/-! # Constructible etale modules in the coefficient universe

Source: Stacks Project, Tags 03RW(3) and 09AL
(auxiliary; not a blueprint node).
These are the recorded affine-local definitions on the equivalent coefficient-sized model.
The constant scalar action and every locally closed stratum are retained.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u v w
open CategoryTheory CategoryTheory.Limits Opposite

-- The universe-polymorphic `hasSheafify_of_essentiallySmall` gets stuck on the universe of
-- `ModuleCat.{max v (u + 1)}`; Mathlib's concrete-category instance applies instead.
attribute [-instance] GrothendieckTopology.hasSheafify_of_essentiallySmall

namespace CategoryTheory

/-- Restrict a constant-ring sheaf module to constant scalars, keeping its additive sheaf.
Source: Stacks Tag 03CY (auxiliary; not a blueprint node). -/
def coefficientModelFixedScalars {C : Type w} [SmallCategory C]
    (T : GrothendieckTopology C) (A : Type w) [CommRing A] :
    ConstantCompletion.Mod (ConstantCompletion.constant T A) ⥤ Sheaf T (ModuleCat.{w} A) where
  obj M :=
    { obj :=
        { obj := fun U ↦ ((PresheafOfModules.restrictScalars
            (SheafOfModules.constantCoefficientUnit T A)).obj M.val).obj U
          map := fun f ↦ ((PresheafOfModules.restrictScalars
            (SheafOfModules.constantCoefficientUnit T A)).obj M.val).map f
          map_id := fun _ ↦ by ext x; simp; rfl
          map_comp := fun _ _ ↦ by ext x; simp; rfl }
      property := Presheaf.isSheaf_of_isSheaf_comp _ _
        (forget₂ (ModuleCat.{w} A) AddCommGrpCat.{w}) M.isSheaf }
  map f := ObjectProperty.homMk
    { app := fun U ↦ (ModuleCat.restrictScalars
        ((SheafOfModules.constantCoefficientUnit T A).app U).hom).map (f.val.app U)
      naturality := fun {_ _} g ↦ by ext x; exact PresheafOfModules.naturality_apply f.val g x }

/-- The usual locally constant finite-module condition on any small site.
The value may vary between covering members, and finiteness means module generation.
Source: Stacks Tag 03RW(3) (auxiliary; not a blueprint node). -/
def IsCoefficientModelLocallyConstantFinite {C : Type w} [SmallCategory C]
    (T : GrothendieckTopology C) (A : Type w) [CommRing A]
    (F : Sheaf T (ModuleCat.{w} A)) : Prop :=
  ∀ V : C, ∃ S : Sieve V, S ∈ T V ∧
    ∀ (U : C) (f : U ⟶ V), S f →
      ∃ M : ModuleCat.{w} A, Module.Finite A M ∧
        Nonempty (F.over U ≅ (constantSheaf (T.over U) (ModuleCat.{w} A)).obj M)

end CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- Base change on the equivalent small etale models.
Source: Stacks Tags 03D2 and 00VC (auxiliary; not a blueprint node). -/
abbrev coefficientEtaleBaseChange {X Y : Scheme.{u}} (f : X ⟶ Y) :
    smallModelComparisonEtaleSite.{u, v} Y ⥤ smallModelComparisonEtaleSite.{u, v} X :=
  AsSmall.down ⋙ MorphismProperty.Over.pullback @Etale ⊤ f ⋙ AsSmall.up

/-- Continuity is transported from etale base change along the site equivalences.
Source: Stacks Tags 03D2 and 00VC (auxiliary; not a blueprint node).
Proof: AsSmall.down and AsSmall.up preserve covering sieves under the induced topologies;
base change preserves etale covers and is the original continuous etale-site functor.
Compose these three continuous functors. -/
@[instance] theorem coefficientEtaleBaseChange_isContinuous {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (coefficientEtaleBaseChange.{u, v} f).IsContinuous
      (smallModelComparisonEtaleTopology.{u, v} Y)
      (smallModelComparisonEtaleTopology.{u, v} X) := by
  let : (AsSmall.up : X.Etale ⥤ smallModelComparisonEtaleSite.{u, v} X).IsContinuous
      X.smallEtaleTopology (smallModelComparisonEtaleTopology.{u, v} X) :=
    inferInstanceAs
      ((AsSmall.equiv.{u, u + 1, max v (u + 1)} (C := X.Etale)).functor.IsContinuous
        X.smallEtaleTopology
        ((AsSmall.equiv.{u, u + 1, max v (u + 1)} (C := X.Etale)).inverse.inducedTopology
          X.smallEtaleTopology))
  let : (MorphismProperty.Over.pullback @Etale ⊤ f).IsContinuous
      Y.smallEtaleTopology X.smallEtaleTopology :=
    Scheme.isContinuous_overPullback @Etale @Etale le_rfl f
  have := Functor.isContinuous_comp (MorphismProperty.Over.pullback @Etale ⊤ f)
    (AsSmall.up : X.Etale ⥤ smallModelComparisonEtaleSite.{u, v} X)
    Y.smallEtaleTopology X.smallEtaleTopology (smallModelComparisonEtaleTopology.{u, v} X)
  exact Functor.isContinuous_comp AsSmall.down
    (MorphismProperty.Over.pullback @Etale ⊤ f ⋙ AsSmall.up)
    (smallModelComparisonEtaleTopology.{u, v} Y) Y.smallEtaleTopology
    (smallModelComparisonEtaleTopology.{u, v} X)

/-- The same inverse image, constructed by Kan extension and sheafification.
Source: Stacks Tag 03D2 (auxiliary; not a blueprint node). -/
def coefficientEtaleFixedPullback {X Y : Scheme.{u}} (f : X ⟶ Y)
    (A : Type (max v (u + 1))) [CommRing A] :=
  Functor.sheafPullbackConstruction.sheafPullback (coefficientEtaleBaseChange.{u, v} f)
    (ModuleCat.{max v (u + 1)} A)
    (smallModelComparisonEtaleTopology.{u, v} Y) (smallModelComparisonEtaleTopology.{u, v} X)

/-- Affine-local constructibility with finite locally closed strata and finitely generated
constant module models. Inverse image and trivializations are on the equivalent small sites.
Source: Stacks Tag 03RW(3) (auxiliary; not a blueprint node). -/
def IsCoefficientConstructibleEtaleModule (X : Scheme.{u})
    (A : Type (max v (u + 1))) [CommRing A] [IsNoetherianRing A]
    (F : CategoryTheory.ConstantCompletion.Mod
      (CategoryTheory.ConstantCompletion.constant (smallModelComparisonEtaleTopology.{u, v} X)
        A)) : Prop :=
  ∀ U : X.Opens, IsAffineOpen U →
    ∃ S : FiniteLocallyClosedStratification U.toScheme,
      (∀ i : Fin S.n, Topology.IsConstructible (S.stratum i)) ∧
      ∀ i : Fin S.n, IsCoefficientModelLocallyConstantFinite
        (smallModelComparisonEtaleTopology.{u, v} (S.domain i)) A
        ((coefficientEtaleFixedPullback.{u, v} (S.immersion i ≫ U.ι) A).obj
          ((coefficientModelFixedScalars _ A).obj F))

/-- Bounded constructible cohomology, using the standard derived category.
Source: Stacks Tag 09AL (auxiliary; not a blueprint node). -/
def IsCoefficientBoundedConstructibleEtale (X : Scheme.{u})
    (A : Type (max v (u + 1))) [CommRing A] [IsNoetherianRing A]
    (K : CategoryTheory.ConstantCompletion.D
      (CategoryTheory.ConstantCompletion.constant (smallModelComparisonEtaleTopology.{u, v} X)
        A)) : Prop :=
  (∀ q : ℤ, IsCoefficientConstructibleEtaleModule X A
    ((coefficientModelCohomology _ q).obj K)) ∧
  ∃ a b : ℤ, a ≤ b ∧ ∀ q : ℤ, q < a ∨ b < q →
    IsZero ((coefficientModelCohomology _ q).obj K)

/-- All ambient module morphisms between constructible objects are retained.
Source: Stacks Tag 03RW(3) (auxiliary; not a blueprint node). -/
abbrev CoefficientConstructibleEtaleModuleCategory (X : Scheme.{u})
    (A : Type (max v (u + 1))) [CommRing A] [IsNoetherianRing A] :=
  ObjectProperty.FullSubcategory (IsCoefficientConstructibleEtaleModule X A)

/-- All ambient derived morphisms between bounded constructible objects are retained.
Source: Stacks Tag 09AL (auxiliary; not a blueprint node). -/
abbrev CoefficientBoundedConstructibleEtaleCategory (X : Scheme.{u})
    (A : Type (max v (u + 1))) [CommRing A] [IsNoetherianRing A] :=
  ObjectProperty.FullSubcategory (IsCoefficientBoundedConstructibleEtale X A)

end AlgebraicGeometry.Scheme
