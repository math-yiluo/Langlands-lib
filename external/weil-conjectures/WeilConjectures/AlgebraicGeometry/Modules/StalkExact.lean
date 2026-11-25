/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import Mathlib.Algebra.Homology.Additive
public import WeilConjectures.AlgebraicGeometry.Cohomology.Exact
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import Mathlib.Topology.Sheaves.Abelian
public import WeilConjectures.AlgebraicGeometry.Modules.FlatPullbackStalk
public import WeilConjectures.AlgebraicGeometry.Modules.Ext

/-!
# Exactness of complexes of `𝒪_X`-modules can be checked on stalks

The stalk at a point `x` of the underlying abelian sheaf of an `𝒪_X`-module defines an exact
functor `AlgebraicGeometry.Scheme.Modules.stalkFunctor x : X.Modules ⥤ Ab`, and a short complex
(or a homological complex) of `𝒪_X`-modules is exact if and only if all its stalks are.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

/-- The stalk at `x` of the underlying abelian sheaf of an `𝒪_X`-module. -/
noncomputable def stalkFunctor (x : X) : X.Modules ⥤ Ab.{u} :=
  toAb X ⋙ TopCat.Sheaf.forget Ab.{u} X ⋙
    TopCat.Presheaf.stalkFunctor Ab.{u} x

lemma stalkFunctor_obj (x : X) (M : X.Modules) :
    (stalkFunctor x).obj M = M.presheaf.stalk x :=
  rfl

instance : (toAb X).Faithful :=
  inferInstanceAs (SheafOfModules.toSheaf.{u} X.ringCatSheaf).Faithful

instance (x : X) : (stalkFunctor x).Additive := by
  have : (TopCat.Sheaf.forget Ab.{u} X).Additive := inferInstance
  have : (TopCat.Presheaf.stalkFunctor Ab.{u} x).Additive := inferInstance
  dsimp only [stalkFunctor]
  infer_instance

instance (x : X) : PreservesFiniteLimits (stalkFunctor x) := by
  have : PreservesFiniteLimits (TopCat.Sheaf.forget Ab.{u} X ⋙
      TopCat.Presheaf.stalkFunctor Ab.{u} x) := inferInstance
  exact comp_preservesFiniteLimits (toAb X) _

instance (x : X) : PreservesFiniteColimits (stalkFunctor x) := by
  dsimp only [stalkFunctor]
  have : PreservesFiniteColimits (TopCat.Sheaf.forget Ab.{u} X ⋙
      TopCat.Presheaf.stalkFunctor Ab.{u} x) :=
    PreservesColimitsOfSize.preservesFiniteColimits.{u, u} _
  exact comp_preservesFiniteColimits _ _

/-- **Exactness is stalk-local.** A short complex of `𝒪_X`-modules is exact if and only if its
stalks at all points are exact. -/
theorem exact_iff_stalkFunctor (S : ShortComplex X.Modules) :
    S.Exact ↔ ∀ x : X, (S.map (stalkFunctor x)).Exact := by
  rw [← ShortComplex.exact_map_iff_of_faithful S (toAb X),
    TopCat.Sheaf.exact_iff_stalkFunctor_map_exact]
  rfl

/-- A homological complex of `𝒪_X`-modules is exact in degree `i` if and only if its stalks at
all points are. -/
theorem exactAt_iff_stalkFunctor {ι : Type*} {c : ComplexShape ι}
    (K : HomologicalComplex X.Modules c) (i : ι) :
    K.ExactAt i ↔ ∀ x : X, (((stalkFunctor x).mapHomologicalComplex c).obj K).ExactAt i := by
  simp only [HomologicalComplex.exactAt_iff]
  exact exact_iff_stalkFunctor (K.sc i)

/-- A homological complex of `𝒪_X`-modules is acyclic if and only if its stalks at all points
are. -/
theorem acyclic_iff_stalkFunctor {ι : Type*} {c : ComplexShape ι}
    (K : HomologicalComplex X.Modules c) :
    K.Acyclic ↔ ∀ x : X, (((stalkFunctor x).mapHomologicalComplex c).obj K).Acyclic := by
  simp only [HomologicalComplex.Acyclic, exactAt_iff_stalkFunctor K]
  exact forall_comm

end AlgebraicGeometry.Scheme.Modules
