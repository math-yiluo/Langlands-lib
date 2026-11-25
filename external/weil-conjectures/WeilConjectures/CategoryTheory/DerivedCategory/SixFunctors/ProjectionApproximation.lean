/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.Algebra.Category.ModuleCat.Abelian
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.TStructure

/-! # Detection of a projection isomorphism by bounded approximations -/

@[expose] public section

universe u v w

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

namespace DerivedCategory

/-- A natural transformation between triangulated functors with a common upper amplitude
bound is invertible at an object admitting arbitrarily accurate approximations where it is
invertible. Source: Stacks Project, Tag 0944, degreewise comparison in the proof.
(blueprint: lem-sf-projection-approximation-comparison).

Proof: in degree r choose an approximation with cone bound r-d-2. After either functor,
the cone vanishes in degrees r-1 and r. The long exact sequences make both approximation
maps invertible in degree r. Naturality and the isomorphism at the approximation make
the desired map invertible in degree r. Cohomological detection finishes the proof. -/
theorem isIso_app_of_approximations
    {R : Type u} [CommRing R] [HasDerivedCategory.{w} (ModuleCat.{u} R)]
    {B : Type v} [Category B] [Abelian B] [HasDerivedCategory B]
    (F G : DerivedCategory (ModuleCat.{u} R) ⥤ DerivedCategory B)
    [F.CommShift ℤ] [G.CommShift ℤ] [F.IsTriangulated] [G.IsTriangulated]
    (τ : F ⟶ G) (M : DerivedCategory (ModuleCat.{u} R)) (d : ℤ)
    (hF : ∀ (E : DerivedCategory (ModuleCat.{u} R)) (c : ℤ), E.IsLE c →
      (F.obj E).IsLE (c + d))
    (hG : ∀ (E : DerivedCategory (ModuleCat.{u} R)) (c : ℤ), E.IsLE c →
      (G.obj E).IsLE (c + d))
    (happrox : ∀ c : ℤ, ∃ T : Triangle (DerivedCategory (ModuleCat.{u} R)),
      T ∈ distTriang _ ∧ T.obj₂ = M ∧ T.obj₃.IsLE c ∧ IsIso (τ.app T.obj₁)) :
    IsIso (τ.app M) := by
  apply (DerivedCategory.isIso_iff B _).2
  intro r
  obtain ⟨T, hT, heq, hC, hP⟩ := happrox (r - d - 2)
  have hFC := hF T.obj₃ (r - d - 2) hC
  have hGC := hG T.obj₃ (r - d - 2) hC
  have hmapF : IsIso ((homologyFunctor B r).map (F.map T.mor₁)) :=
    isIso_homologyMap_mor₁ (F.mapTriangle.obj T) (F.map_distinguished T hT)
      (r - 1) r (by omega)
      ((F.obj T.obj₃).isZero_of_isLE (r - d - 2 + d) _ (by omega))
      ((F.obj T.obj₃).isZero_of_isLE (r - d - 2 + d) _ (by omega))
  have hmapG : IsIso ((homologyFunctor B r).map (G.map T.mor₁)) :=
    isIso_homologyMap_mor₁ (G.mapTriangle.obj T) (G.map_distinguished T hT)
      (r - 1) r (by omega)
      ((G.obj T.obj₃).isZero_of_isLE (r - d - 2 + d) _ (by omega))
      ((G.obj T.obj₃).isZero_of_isLE (r - d - 2 + d) _ (by omega))
  have hnat := congrArg ((homologyFunctor B r).map) (τ.naturality T.mor₁)
  simp only [Functor.map_comp] at hnat
  have hcomp : IsIso ((homologyFunctor B r).map (F.map T.mor₁) ≫
      (homologyFunctor B r).map (τ.app T.obj₂)) := by
    rw [hnat]
    infer_instance
  rw [← heq]
  exact IsIso.of_isIso_comp_left ((homologyFunctor B r).map (F.map T.mor₁)) _

end DerivedCategory
