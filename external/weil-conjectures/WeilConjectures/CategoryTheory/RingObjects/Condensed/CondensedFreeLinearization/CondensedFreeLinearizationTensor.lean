/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.RingObjects.Condensed.CondensedAction.InternalBar.CondensedInternalBarData
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.CategoryTheory.Monoidal.Internal.FunctorCategory
public import WeilConjectures.CategoryTheory.RingObjects.Ab
public import WeilConjectures.CategoryTheory.Sites.MonObj
public import WeilConjectures.CategoryTheory.ModuleObjects.MapMod
public import Mathlib.CategoryTheory.Sites.Monoidal
public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import Mathlib.CategoryTheory.Monoidal.Preadditive
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Preadditive
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Sites.Localization
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.Monoidal.Braided.Reflection
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify
public import WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.CategoryTheory.ModuleObjects.Symmetric
public import WeilConjectures.CategoryTheory.ModuleObjects.Abelian
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
public import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
public import WeilConjectures.FromJoel.Algebra.Homology.TotalComplexMap
public import WeilConjectures.CategoryTheory.ModuleObjects.GrothendieckAbelian
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.CategoryTheory.Adjunction.Mates
public import Mathlib.CategoryTheory.Limits.Preserves.Finite
public import WeilConjectures.CategoryTheory.Grothendieck.GrothendieckTopos
public import Mathlib.Algebra.Category.Grp.Limits
public import Mathlib.CategoryTheory.Sites.Whiskering
public import Mathlib.CategoryTheory.Types.Basic
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.CategoryTheory.Sites.CartesianMonoidal
import WeilConjectures.Algebra.Category.ModuleCat.Presheaf.SheafificationTensor
public import Mathlib.CategoryTheory.Sites.LocalSite
public import Mathlib.Combinatorics.Quiver.ReflQuiver

/-! # Free linearization of condensed sets and tensor products

Source: blueprint direct-image stability, paragraph (3), internal bar input;
Stacks Project, Modules on Sites, Tags 04BL, 03CY and 0GMW
(blueprint: lem-sfb-condensed-free-linearization-tensor).
-/

@[expose] public section

noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped TensorProduct
open CategoryTheory.InternalAbelianSheafModule
open Profinite.CondensedAction Profinite.CondensedAction.InternalBar

namespace Profinite.CondensedFreeLinearization

variable (R : Profinite.CondensedRing.{u}) [IsCommMonObj R.X]

/-- The existing reconstructed coefficient ring sheaf.
Source: Stacks 04BL (blueprint: lem-sfb-condensed-free-linearization-tensor). -/
abbrev coefficients := sectionRingSheaf (coherentTopology Profinite.{u}) R.X

/-- The fixed equivalence, retaining the underlying abelian sheaves.
Source: Stacks 03CY (blueprint: lem-sfb-condensed-free-linearization-tensor). -/
abbrev sections := (sectionModuleEquivalence (coherentTopology Profinite.{u}) R.X).functor

/-- The actual sectionwise free presheaf, with semilinear restriction maps.
Source: Stacks 04BL (blueprint: lem-sfb-condensed-free-linearization-tensor). -/
abbrev presheafFree (X : Sheaf (coherentTopology Profinite.{u}) (Type (u + 1))) :=
  PresheafOfModules.freeObj (R := (SheafFreeModule.ring (coefficients R)).obj) X.obj

/-- The existing module sheafification of the sectionwise free presheaf.
Source: Stacks 04BL and 03CY (blueprint: lem-sfb-condensed-free-linearization-tensor). -/
abbrev sheafFree := SheafFreeModule.free (coefficients R)

/-- Generalized generators from the unit of the fixed internal free adjunction.
Source: Stacks 04BL (blueprint: lem-sfb-condensed-free-linearization-tensor). -/
def generator (X : Sheaf (coherentTopology Profinite.{u}) (Type (u + 1)))
    (S : Profinite.{u}) (x : X.obj.obj (op S)) : sectionModule R ((free R).obj X) S :=
  (((freeAdjunction R).unit.app X).hom.app (op S)) x

/-- The existing module sheafification functor, with identity coefficient map.
Source: Stacks 03CY (blueprint: lem-sfb-condensed-free-linearization-tensor). -/
abbrev sheafify := PresheafOfModules.sheafification.{u + 1}
  (R := SheafFreeModule.ring (coefficients R)) (𝟙 _)

/-- Restriction to the fixed generators, as a morphism of condensed sets.
Source: Stacks 04BL (blueprint: lem-sfb-condensed-free-linearization-tensor). -/
def restrictGenerators (X : Sheaf (coherentTopology Profinite.{u}) (Type (u + 1)))
    (M : Modules R) (f : (free R).obj X ⟶ M) :=
  (freeAdjunction R).unit.app X ≫
    (Mod.forget R.X ⋙ sheafCompose (coherentTopology Profinite.{u})
      (forget AddCommGrpCat.{u + 1})).map f

/-- All normalized comparisons for the fixed free internal adjunction. The presheaf
comparison is fixed sectionwise, and the tensor comparison is its sheafification through
the specified internal-to-section and module-sheafification tensor comparisons.
Source: blueprint direct-image stability, paragraph (3), extracted free linearization;
Stacks 04BL, 03CY and 0GMW (blueprint: lem-sfb-condensed-free-linearization-tensor). -/
structure Comparison where
  /-- The natural identification with sheafification of the sectionwise free presheaf. -/
  linearization : free R ⋙ sections R ≅ sheafFree R
  /-- The identification preserves the generators of the fixed adjunction. -/
  linearization_generator :
    ∀ (X : Sheaf (coherentTopology Profinite.{u}) (Type (u + 1)))
      (S : Profinite.{u}) (x : X.obj.obj (op S)),
    ((linearization.hom.app X).val.app (op S)) (generator R X S x) =
      ((SheafFreeModule.generatorRaw (coefficients R) X).hom.app (op S)) x
  /-- Maps out of the actual free object are precisely natural generator assignments. -/
  universalProperty :
    ∀ (X : Sheaf (coherentTopology Profinite.{u}) (Type (u + 1))) (M : Modules R),
    Function.Bijective (restrictGenerators R X M)
  /-- The linear extension is the finite coefficient sum before sheafification. -/
  finite_sum :
    ∀ (X : Sheaf (coherentTopology Profinite.{u}) (Type (u + 1))) (M : Modules R)
      (f : (free R).obj X ⟶ M) (S : Profinite.{u})
      (v : X.obj.obj (op S) →₀ (coefficients R).obj.obj (op S)),
    ((sections R).map f).val.app (op S)
        (((linearization.inv.app X).val.app (op S))
          ((SheafFreeModule.freeModuleUnit (coefficients R) X).app (op S) v)) =
      v.sum (fun x a ↦ a • @id (((sections R).obj M).val.obj (op S))
        (((restrictGenerators R X M f).hom.app (op S)) x))
  /-- The functorial free map takes [x] to [u(x)]. -/
  map_generator :
    ∀ (X Y : Sheaf (coherentTopology Profinite.{u}) (Type (u + 1))) (f : X ⟶ Y)
      (S : Profinite.{u}) (x : X.obj.obj (op S)),
    onSections R ((free R).map f) S (generator R X S x) =
      generator R Y S (f.hom.app (op S) x)
  /-- Equality is tested on generalized generators, not on globally free sections. -/
  generator_ext :
    ∀ (X : Sheaf (coherentTopology Profinite.{u}) (Type (u + 1))) (M : Modules R)
      (f g : (free R).obj X ⟶ M),
    (∀ (S : Profinite.{u}) (x : X.obj.obj (op S)),
      onSections R f S (generator R X S x) = onSections R g S (generator R X S x)) →
      f = g
  /-- Inverse presheaf maps, automatically compatible with all restrictions. -/
  presheafTensor :
    ∀ X Y : Sheaf (coherentTopology Profinite.{u}) (Type (u + 1)),
    presheafFree R X ⊗ presheafFree R Y ≅ presheafFree R (X ⊗ Y)
  /-- The forward section map is the ordinary free-module tensor map. -/
  presheafTensor_hom :
    ∀ (X Y : Sheaf (coherentTopology Profinite.{u}) (Type (u + 1))) (S : Profinite.{u}),
    (presheafTensor X Y).hom.app (op S) =
      (ModuleCat.FreeMonoidal.μIso ((coefficients R).obj.obj (op S))
        (X.obj.obj (op S)) (Y.obj.obj (op S))).hom
  /-- The inverse sends [(x,y)] to [x] tensor [y], with linear extension. -/
  presheafTensor_inv :
    ∀ (X Y : Sheaf (coherentTopology Profinite.{u}) (Type (u + 1))) (S : Profinite.{u}),
    (presheafTensor X Y).inv.app (op S) =
      (ModuleCat.FreeMonoidal.μIso ((coefficients R).obj.obj (op S))
        (X.obj.obj (op S)) (Y.obj.obj (op S))).inv
  /-- The fixed internal-to-section relative tensor comparison. -/
  sectionTensor : ∀ M N : Modules R,
    (sections R).obj (M ⊗ N) ≅ (sections R).obj M ⊗ (sections R).obj N
  /-- Its local pure tensor normalization determines this comparison. -/
  sectionTensor_tmul : ∀ (M N : Modules R) (S : Profinite.{u})
      (x : sectionModule R M S) (y : sectionModule R N S),
    (sectionTensor M N).hom.val.app (op S) (pureTensor R M N S x y) =
      comparison_sectionTmul (coherentTopology Profinite.{u}) R.X
        ((sections R).obj M) ((sections R).obj N) (op S) x y
  /-- Module sheafification commutes with the presheaf tensor product. -/
  sheafTensor : ∀ X Y : Sheaf (coherentTopology Profinite.{u}) (Type (u + 1)),
    (sheafFree R).obj X ⊗ (sheafFree R).obj Y ≅
      (sheafify R).obj (presheafFree R X ⊗ presheafFree R Y)
  /-- The sheafification comparison is the one induced by the two unit maps. -/
  sheafTensor_tmul :
    ∀ (X Y : Sheaf (coherentTopology Profinite.{u}) (Type (u + 1))) (S : Profinite.{u})
      (v : (presheafFree R X).obj (op S)) (w : (presheafFree R Y).obj (op S)),
    (sheafTensor X Y).inv.val.app (op S)
        ((toSheafify (coherentTopology Profinite.{u})
          (presheafFree R X ⊗ presheafFree R Y).presheaf).app (op S)
            (v ⊗ₜ[(coefficients R).obj.obj (op S)] w)) =
      comparison_sectionTmul (coherentTopology Profinite.{u}) R.X
        ((sheafFree R).obj X) ((sheafFree R).obj Y) (op S)
        ((SheafFreeModule.freeModuleUnit (coefficients R) X).app (op S) v)
        ((SheafFreeModule.freeModuleUnit (coefficients R) Y).app (op S) w)
  /-- The two inverse internal tensor maps. -/
  tensor : ∀ X Y : Sheaf (coherentTopology Profinite.{u}) (Type (u + 1)),
    (free R).obj X ⊗ (free R).obj Y ≅ (free R).obj (X ⊗ Y)
  /-- The internal tensor map is exactly the sheafification of the sectionwise map. -/
  tensor_sheafification :
    ∀ X Y : Sheaf (coherentTopology Profinite.{u}) (Type (u + 1)),
    (sections R).map (tensor X Y).hom ≫ linearization.hom.app (X ⊗ Y) =
      (sectionTensor ((free R).obj X) ((free R).obj Y)).hom ≫
        (linearization.hom.app X ⊗ₘ linearization.hom.app Y) ≫
          (sheafTensor X Y).hom ≫ (sheafify R).map (presheafTensor X Y).hom
  /-- Forward generator formula. -/
  tensor_generator :
    ∀ (X Y : Sheaf (coherentTopology Profinite.{u}) (Type (u + 1)))
      (S : Profinite.{u}) (x : X.obj.obj (op S)) (y : Y.obj.obj (op S)),
    onSections R (tensor X Y).hom S
        (pureTensor R _ _ S (generator R X S x) (generator R Y S y)) =
      generator R (X ⊗ Y) S (x, y)
  /-- Inverse generator formula. -/
  tensor_inv_generator :
    ∀ (X Y : Sheaf (coherentTopology Profinite.{u}) (Type (u + 1)))
      (S : Profinite.{u}) (x : X.obj.obj (op S)) (y : Y.obj.obj (op S)),
    onSections R (tensor X Y).inv S (generator R (X ⊗ Y) S (x, y)) =
      pureTensor R _ _ S (generator R X S x) (generator R Y S y)
  /-- Naturality for maps of both condensed sets. -/
  tensor_naturality :
    ∀ (X X' Y Y' : Sheaf (coherentTopology Profinite.{u}) (Type (u + 1)))
      (f : X ⟶ X') (g : Y ⟶ Y'),
    ((free R).map f ⊗ₘ (free R).map g) ≫ (tensor X' Y').hom =
      (tensor X Y).hom ≫ (free R).map (f ⊗ₘ g)
  /-- The terminal condensed set linearizes to the regular module. -/
  unit : (free R).obj (𝟙_ (Sheaf (coherentTopology Profinite.{u}) (Type (u + 1)))) ≅
    Mod.regular R.X
  /-- The single generator maps to the unit section, including over the zero ring. -/
  unit_generator : ∀ (S : Profinite.{u})
      (x : (𝟙_ (Sheaf (coherentTopology Profinite.{u}) (Type (u + 1)))).obj.obj (op S)),
    onSections R unit.hom S (generator R _ S x) = regularOne R S
  /-- Associator compatibility with the canonical cartesian product associator. -/
  associativity :
    ∀ X Y Z : Sheaf (coherentTopology Profinite.{u}) (Type (u + 1)),
    (tensor X Y).hom ▷ (free R).obj Z ≫ (tensor (X ⊗ Y) Z).hom ≫
        (free R).map (α_ X Y Z).hom =
      (α_ _ _ _).hom ≫ (free R).obj X ◁ (tensor Y Z).hom ≫
        (tensor X (Y ⊗ Z)).hom
  /-- Symmetry compatibility. -/
  symmetry : ∀ X Y : Sheaf (coherentTopology Profinite.{u}) (Type (u + 1)),
    (tensor X Y).hom ≫ (free R).map
        (CartesianMonoidalCategory.lift (CartesianMonoidalCategory.snd X Y)
          (CartesianMonoidalCategory.fst X Y)) =
      (β_ ((free R).obj X) ((free R).obj Y)).hom ≫ (tensor Y X).hom
  /-- Left unitor compatibility. -/
  left_unit : ∀ X : Sheaf (coherentTopology Profinite.{u}) (Type (u + 1)),
    (tensor (𝟙_ _) X).hom ≫ (free R).map (λ_ X).hom =
      unit.hom ▷ (free R).obj X ≫ (λ_ ((free R).obj X)).hom
  /-- Right unitor compatibility. -/
  right_unit : ∀ X : Sheaf (coherentTopology Profinite.{u}) (Type (u + 1)),
    (tensor X (𝟙_ _)).hom ≫ (free R).map (ρ_ X).hom =
      (free R).obj X ◁ unit.hom ≫ (ρ_ ((free R).obj X)).hom

end Profinite.CondensedFreeLinearization
