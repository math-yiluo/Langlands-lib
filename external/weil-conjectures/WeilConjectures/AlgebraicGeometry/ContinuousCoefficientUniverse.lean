/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Topology.Category.Profinite.EffectiveEpi
public import WeilConjectures.CategoryTheory.RingObjects.ContinuousMap

import Mathlib.Condensed.TopComparison

/-!
# Continuous coefficient rings in the scheme universe

Source: Hemo--Richarz--Scholbach, Example 3.1
(auxiliary; not a blueprint node).
The upstream coefficient API fixes the coefficient carrier in Type 0. This interface
uses the same sectionwise construction for any coefficient ring in the scheme universe.
The other internal-module and derived constructions use the existing library framework.
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory MonObj Limits Opposite

namespace Profinite

variable (T : Type u) [TopologicalSpace T] [Ring T] [IsTopologicalRing T]

/-- Continuous functions with pointwise ring operations and precomposition.
Source: Hemo--Richarz--Scholbach, Example 3.1
(auxiliary; not a blueprint node). -/
noncomputable def continuousCoefficientRingPresheaf : Profinite.{u}ᵒᵖ ⥤ RingCat.{u + 1} where
  obj S := RingCat.of (ULift.{u + 1} C(S.unop, T))
  map f := RingCat.ofHom
    (ULift.ringEquiv.symm.toRingHom.comp
      (((ContinuousMap.compRightAlgHom ℤ T f.unop.hom.hom).toRingHom).comp
        ULift.ringEquiv.toRingHom))
  map_id _ := rfl
  map_comp _ _ := rfl

private noncomputable def continuousCoefficientRingPresheafForgetIso :
    continuousCoefficientRingPresheaf T ⋙ forget RingCat.{u + 1} ≅
      ContinuousMap.yonedaPresheaf Profinite.toTopCat.{u} T ⋙ uliftFunctor.{u + 1} :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (fun _ ↦ rfl)

/-- Continuous functions descend along coherent profinite covers.
Source: Hemo--Richarz--Scholbach, Example 3.1
(auxiliary; not a blueprint node).
Proof: a surjective map of profinite spaces is a quotient map; compatible functions
therefore descend uniquely and continuously. Finite coproducts give the other sheaf axiom. -/
theorem isSheaf_continuousCoefficientRingPresheaf :
    Presheaf.IsSheaf (coherentTopology Profinite.{u})
      (continuousCoefficientRingPresheaf T) := by
  rw [Presheaf.isSheaf_iff_isSheaf_forget _ _ (forget RingCat.{u + 1}),
    Presheaf.isSheaf_of_iso_iff (continuousCoefficientRingPresheafForgetIso T),
    isSheaf_iff_isSheaf_of_type, Presieve.isSheaf_comp_uliftFunctor_iff,
    ← isSheaf_iff_isSheaf_of_type]
  rw [Presheaf.isSheaf_iff_preservesFiniteProducts_and_equalizerCondition]
  refine ⟨inferInstance, ?_⟩
  apply +allowSynthFailures equalizerCondition_yonedaPresheaf Profinite.toTopCat.{u} T
  intro Z B π hπ
  exact .of_surjective_continuous (((Profinite.effectiveEpi_tfae π).out 1 3).mp hπ)
    π.hom.hom.continuous

/-- The condensed ring with sections C(S,T), with no Type 0 restriction.
Source: Hemo--Richarz--Scholbach, Example 3.1
(auxiliary; not a blueprint node). -/
noncomputable def continuousCoefficientRingSheaf :
    Sheaf (coherentTopology Profinite.{u}) RingCat.{u + 1} :=
  ⟨continuousCoefficientRingPresheaf T, isSheaf_continuousCoefficientRingPresheaf T⟩

/-- The underlying internal ring of the continuous condensed coefficient sheaf.
Source: Hemo--Richarz--Scholbach, Example 3.1
(auxiliary; not a blueprint node). -/
noncomputable abbrev continuousCoefficientRingObj :
    Sheaf (coherentTopology Profinite.{u}) AddCommGrpCat.{u + 1} :=
  (sheafCompose (coherentTopology Profinite.{u})
    (forget₂ RingCat.{u + 1} AddCommGrpCat.{u + 1})).obj
      (continuousCoefficientRingSheaf T)

end Profinite

namespace AlgebraicGeometry.ProEtale

variable (X : Scheme.{u}) (T : Type u)
  [TopologicalSpace T] [Ring T] [IsTopologicalRing T]

/-- Continuous functions on pro-etale objects, with their Zariski topology.
Source: Hemo--Richarz--Scholbach, Example 3.1
(auxiliary; not a blueprint node). -/
noncomputable def continuousCoefficientRingPresheaf : X.ProEtᵒᵖ ⥤ RingCat.{u + 1} where
  obj U := RingCat.of (ULift.{u + 1} C(U.unop.left, T))
  map f := RingCat.ofHom
    (ULift.ringEquiv.symm.toRingHom.comp
      (((ContinuousMap.compRightAlgHom ℤ T f.unop.left.base.hom).toRingHom).comp
        ULift.ringEquiv.toRingHom))
  map_id _ := rfl
  map_comp _ _ := rfl

private noncomputable def continuousCoefficientRingPresheafForgetIso :
    continuousCoefficientRingPresheaf X T ⋙ forget RingCat.{u + 1} ≅
      (Scheme.ProEt.forget X ⋙ Over.forget X).op ⋙ continuousMapPresheaf T ⋙
        uliftFunctor.{u + 1} :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (fun _ ↦ rfl)

/-- Continuous functions are a pro-etale sheaf.
Source: Hemo--Richarz--Scholbach, Example 3.1
(auxiliary; not a blueprint node).
Proof: compatible functions glue uniquely along fpqc covers, since these detect openness
and their fibre products enforce equality of values in each fibre; restrict to pro-etale covers. -/
theorem isSheaf_continuousCoefficientRingPresheaf :
    Presheaf.IsSheaf (Scheme.ProEt.topology X)
      (continuousCoefficientRingPresheaf X T) := by
  rw [Presheaf.isSheaf_iff_isSheaf_forget _ _ (forget RingCat.{u + 1}),
    Presheaf.isSheaf_of_iso_iff (continuousCoefficientRingPresheafForgetIso X T)]
  refine Functor.op_comp_isSheaf_of_isSheaf (F := Scheme.ProEt.forget X ⋙ Over.forget X)
    (J := Scheme.ProEt.topology X) (K := Scheme.proetaleTopology) _ ?_
  rw [isSheaf_iff_isSheaf_of_type, Presieve.isSheaf_comp_uliftFunctor_iff,
    ← isSheaf_iff_isSheaf_of_type]
  exact (isSheaf_fpqcTopology_continuousMapPresheaf T).of_le Scheme.proetaleTopology_le_fpqcTopology

/-- The ring sheaf V ↦ C(|V|,T) in the scheme universe.
Source: Hemo--Richarz--Scholbach, Example 3.1
(auxiliary; not a blueprint node). -/
noncomputable def continuousCoefficientRingSheaf :
    Sheaf (Scheme.ProEt.topology X) RingCat.{u + 1} :=
  ⟨continuousCoefficientRingPresheaf X T, isSheaf_continuousCoefficientRingPresheaf X T⟩

end AlgebraicGeometry.ProEtale
