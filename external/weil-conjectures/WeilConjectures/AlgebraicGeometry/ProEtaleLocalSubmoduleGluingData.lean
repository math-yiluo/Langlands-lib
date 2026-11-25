/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.CategoryTheory.ModuleObjects.MapMod
public import WeilConjectures.CategoryTheory.RingObjects.Ab
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Monoidal

/-! # A module equipped with its local identifications

Source: Stacks Project, Sites, Tag 04TR.
(auxiliary; not a blueprint node).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale

/-- The output of gluing local submodules, retaining the injections and local
identifications as named fields rather than a nested dependent existential.

Source: Stacks Project, Sites, Tag 04TR.
(auxiliary; not a blueprint node). -/
structure LocalSubmoduleGluingData
    (X : Scheme.{u}) (R : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) [MonObj R]
    (Q : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R)
    (U : Scheme.Cover.{u} Scheme.proetalePrecoverage X)
    (L : ∀ i, Mod (Sheaf (Scheme.ProEt.topology (U.X i)) Ab.{u + 1})
      ((upperStar Ab.{u + 1} (U.f i)).obj R))
    (q : ∀ i, L i ⟶ ((upperStar Ab.{u + 1} (U.f i)).mapMod R).obj Q) where
  globalModule : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R
  hom : globalModule ⟶ Q
  localIso : ∀ i, ((upperStar Ab.{u + 1} (U.f i)).mapMod R).obj globalModule ≅ L i
  hom_eq : ∀ i, ((upperStar Ab.{u + 1} (U.f i)).mapMod R).map hom =
    (localIso i).hom ≫ q i

end AlgebraicGeometry.ProEtale
