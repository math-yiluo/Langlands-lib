/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.RingObjects.Condensed.CondensedAction.CondensedActionModule
public import WeilConjectures.CategoryTheory.InternalAbelianSheafModuleEquivalence
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.CategoryTheory.Monoidal.Internal.FunctorCategory
public import WeilConjectures.CategoryTheory.RingObjects.Ab
public import WeilConjectures.CategoryTheory.Sites.MonObj
public import WeilConjectures.CategoryTheory.ModuleObjects.MapMod
public import WeilConjectures.CategoryTheory.SheafTensorStructure
public import Mathlib.CategoryTheory.Sites.Monoidal
public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import Mathlib.CategoryTheory.Monoidal.Preadditive
public import WeilConjectures.CategoryTheory.PresheafTensorInternalHom
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Preadditive
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Sites.Localization
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Sites.Sheafification
public import WeilConjectures.CategoryTheory.ModuleObjects.Monoidal
public import Mathlib.CategoryTheory.Sites.Canonical
public import Mathlib.CategoryTheory.Sites.Adjunction
public import Mathlib.Algebra.Category.Grp.Adjunctions
public import Mathlib.Algebra.Homology.ShortComplex.Exact
public import Mathlib.CategoryTheory.Sites.Coherent.CoherentSheaves
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import WeilConjectures.CategoryTheory.CondensedInternalBarData
public import WeilConjectures.AlgebraicGeometry.FreeParameterScalarMaps

/-! # The augmented internal homogeneous bar resolution

Source: blueprint, direct-image stability, paragraph (3), formal internal bar input
(blueprint: lem-sfb-condensed-internal-bar-resolution).

Free objects are the actual composite of free abelian sheaf and free internal module.
The resolution specification retains all generator formulas, including the equivariant
induced presentation. No object is selected from the postponed existence theorem.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open Profinite.CondensedAction
open scoped TensorProduct

namespace Profinite.CondensedAction.InternalBar

variable (R : Profinite.CondensedRing.{u}) [IsCommMonObj R.X]

variable (G : Type u) [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
  [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]

/-- The profinite space of tuples, including the one-point space in arity zero.
Source: the objects in the homogeneous bar construction
(blueprint: lem-sfb-condensed-internal-bar-resolution). -/
abbrev tuples (n : ℕ) : Profinite.{u} := Profinite.of (Fin n → G)

/-- The free internal module on the condensed profinite space G^n.
Source: step 1, A[X] constructed by the free adjunction
(blueprint: lem-sfb-condensed-internal-bar-resolution). -/
def freePower (n : ℕ) : Modules R :=
  (free R).obj (((coherentTopology Profinite.{u}).uliftYoneda.{u + 1}).obj (tuples G n))

/-- The canonical local generator from the unit of the free adjunction.
Source: step 1, the generator [g_1,...,g_n]
(blueprint: lem-sfb-condensed-internal-bar-resolution). -/
def generator (n : ℕ) (S : Profinite.{u}) (x : Fin n → C(S, G)) :
    sectionModule R (freePower R G n) S :=
  (((freeAdjunction R).unit.app
    (((coherentTopology Profinite.{u}).uliftYoneda.{u + 1}).obj (tuples G n))).hom.app
      (op S)) (ULift.up (CompHausLike.ofHom _
        ⟨fun s i ↦ x i s, continuous_pi fun i ↦ (x i).continuous⟩))

/-- Evaluate an internal module map on a section, without changing its encoding.
Source: step 1, maps of the original underlying abelian sheaves
(blueprint: lem-sfb-condensed-internal-bar-resolution). -/
abbrev onSections {M N : Modules R} (f : M ⟶ N) (S : Profinite.{u})
    (x : sectionModule R M S) : sectionModule R N S :=
  (f.hom.hom.app (op S)).hom x

/-- Generators in an explicitly identified copy of the canonical free object.
Source: step 1, the unique-up-to-isomorphism free-module universal property
(blueprint: lem-sfb-condensed-internal-bar-resolution). -/
def basis (n : ℕ) (M : ActionModule R G) (e : M.module ≅ freePower R G n)
    (S : Profinite.{u}) (x : Fin n → C(S, G)) : sectionModule R M.module S :=
  onSections R e.inv S (generator R G n S x)

/-- The canonical relative pure tensor of internal modules.
Source: step 2, the lax sheaf-inclusion tensor map followed by the relative coequalizer
(blueprint: lem-sfb-condensed-internal-bar-resolution). -/
def pureTensor (M N : Modules R) (S : Profinite.{u})
    (x : sectionModule R M S) (y : sectionModule R N S) :
    sectionModule R (M ⊗ N) S :=
  ((Mod.tensorObjπ M N).hom.app (op S))
    (((Functor.LaxMonoidal.μ
      (sheafToPresheaf (coherentTopology Profinite.{u}) AddCommGrpCat.{u + 1})
      M.X N.X).app (op S)) (x ⊗ₜ[ℤ] y))

/-- The unit section of the regular internal module, in the reconstructed section ring.
Source: step 3, the augmentation [g] ↦ 1
(blueprint: lem-sfb-condensed-internal-bar-resolution). -/
def regularOne (S : Profinite.{u}) : sectionModule R (Mod.regular R.X) S :=
  (1 : (InternalAbelianSheafModule.sectionRings
    (coherentTopology Profinite.{u}) R.X).obj (op S))

end Profinite.CondensedAction.InternalBar
