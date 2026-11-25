/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Properties
public import WeilConjectures.AlgebraicGeometry.FiniteLocallyClosedStratification
import WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme
import WeilConjectures.AlgebraicGeometry.FiniteEtaleNoetherianClopenAssemblyCore
import WeilConjectures.AlgebraicGeometry.FiniteEtaleNoetherianClopenAssemblyReduction

/-! Noetherian assembly of generic properties on reduced scheme strata. -/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory
namespace AlgebraicGeometry.Scheme

/-- Noetherian assembly of a generic affine-integral property.
Source: Stacks Project, Tags 01OZ and 01J3
(blueprint: lem-a1-finite-etale-noetherian-clopen-assembly).

The reduced case is supplied by the core induction lemma. The vanishing ideal of the
whole space gives a reduced closed subscheme with surjective underlying map, and the
reduction transport lemma carries the resulting strata back to the original scheme.
-/
theorem exists_reduced_stratification_of_integral_affine_generic
    (Y : Scheme.{u}) [IsLocallyNoetherian Y] [CompactSpace Y]
    (P : (B : Scheme.{u}) → (B ⟶ Y) → Prop)
    (hgeneric : ∀ (B : Scheme.{u}) [IsIntegral B] [IsNoetherian B] [IsAffine B]
      (t : B ⟶ Y), IsImmersion t →
      ∃ U : B.Opens, Nonempty U ∧ P U.toScheme (U.ι ≫ t)) :
    ∃ T : FiniteLocallyClosedStratification Y,
      (∀ a : Fin T.n, IsReduced (T.domain a)) ∧
      ∀ a : Fin T.n, P (T.domain a) (T.immersion a) := by
  classical
  let I := IdealSheafData.vanishingIdeal (⊤ : TopologicalSpace.Closeds Y)
  let X := I.subscheme
  let r : X ⟶ Y := I.subschemeι
  let _ : IsReduced X :=
    (IdealSheafData.reduced_induced_closed_subscheme Y ⊤).2.2.2.1
  let _ : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian r
  let _ : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace r
  have hrange : Set.range r = (Set.univ : Set Y) := by
    change Set.range I.subschemeι = (Set.univ : Set Y)
    rw [IdealSheafData.range_subschemeι, IdealSheafData.coe_support_vanishingIdeal]
    rfl
  let Q : (B : Scheme.{u}) → (B ⟶ X) → Prop := fun B t => P B (t ≫ r)
  obtain ⟨T, hT, hP⟩ :=
    exists_reduced_stratification_of_integral_affine_generic_reduced X Q
      (fun B _ _ _ t ht => hgeneric B (t ≫ r) inferInstance)
  exact transport_reduced_stratification_along_surjective_closed_immersion
    r hrange P T hT hP

end AlgebraicGeometry.Scheme
