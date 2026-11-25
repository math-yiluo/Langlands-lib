/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators
import WeilConjectures.AlgebraicGeometry.EpiOverFunctor

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits
set_option linter.style.haveILetI false


/-- Epimorphic images of finite type sheaves are finite type.
Source: Stacks Project, Modules, Lemma 01B7 (blueprint: lem-weil-pbc-sheaf-finite-type-epi-image).
The proof is the local-generator argument from Lemma 01B7. On each open neighbourhood
where finitely many sections generate `A`, their images generate `B`: for a section of
`B`, use the epimorphism to lift it locally to `A`, then express each lift locally as a
linear combination of the chosen generators. Refining the two coverings gives a finite
generating family for `B` around every point, which is exactly `B.IsFiniteType`. The
same argument applies on the restricted open sites used for relation kernels. -/
theorem sheaf_finiteType_of_epi
    {C : Type v} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}
    [∀ U, HasSheafify (J.over U) AddCommGrpCat.{u}]
    [∀ U, (J.over U).WEqualsLocallyBijective
      AddCommGrpCat.{u}]
    {A B : SheafOfModules.{u} R} (e : A ⟶ B) [Epi e] :
    A.IsFiniteType → B.IsFiniteType := by
  intro hA
  obtain ⟨σ, hσ⟩ := hA.exists_localGeneratorsData
  let τ : B.LocalGeneratorsData := {
    I := σ.I
    X := σ.X
    coversTop := σ.coversTop
    generators := fun i => by
      letI := epi_overFunctor_map e (σ.X i)
      exact (σ.generators i).ofEpi ((SheafOfModules.overFunctor R (σ.X i)).map e)
  }
  refine ⟨⟨τ, ?_⟩⟩
  refine ⟨fun i => ?_⟩
  dsimp [τ]
  haveI : (σ.generators i).IsFiniteType := hσ.isFiniteType i
  letI := epi_overFunctor_map e (σ.X i)
  infer_instance

end
