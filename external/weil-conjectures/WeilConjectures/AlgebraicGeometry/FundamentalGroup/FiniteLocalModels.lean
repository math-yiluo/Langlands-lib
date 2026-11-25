/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.ConstantSheafOfTypes
public import WeilConjectures.ConstructibleSheaf.KernelCokernel

/-!
# Finite constant local models of finite locally constant sheaves of sets

Let `E` be a sheaf of sets on the small étale site of a scheme `T` which is constant on the
members of some étale cover and whose geometric stalks are finite. Then on every nonempty member
`U` of the cover, `E|_U` is the constant sheaf at a set `S`, and `S` is finite: distinct
elements of `S` give distinct elements of the stalk of `E` at a geometric point of `U`
(`AlgebraicGeometry.Scheme.Etale.finite_of_iso_continuousMapSheafOfTypes`). Discarding the empty
members gives an étale cover on whose members `E` is constant with finite values.

## Main results

- `AlgebraicGeometry.Scheme.finiteLocallyConstant_exists_local_models`
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme

variable {T : Scheme.{u}}

/-- **Finite locally constant sheaves of sets admit finite constant local models**: if a sheaf
of sets `E` on the small étale site of `T` is constant on the members of an étale cover and all
its geometric stalks are finite, there is an étale cover of `T` on every member `U` of which
`E|_U` is isomorphic to the constant sheaf at a finite set `S`. The sets `S` may depend on `U`.
(blueprint: `lem-weil-pbc-finite-locally-constant-sets-local-models`) -/
theorem finiteLocallyConstant_exists_local_models
    (E : Sheaf T.smallEtaleTopology (Type (u + 1))) (𝒰 : Cover.{u} etalePrecoverage T)
    (h𝒰 : ∀ i, (E.over (𝒰.etalePrecoverageToEtale i)).IsConstant
      (T.smallEtaleTopology.over (𝒰.etalePrecoverageToEtale i)))
    (hE : IsFiniteSheaf E) :
    ∃ 𝒱 : Cover.{u} etalePrecoverage T, ∀ i, ∃ S : Type (u + 1), Finite S ∧
      Nonempty (E.over (𝒱.etalePrecoverageToEtale i) ≅
        (constantSheaf (T.smallEtaleTopology.over (𝒱.etalePrecoverageToEtale i))
          (Type (u + 1))).obj S) := by
  refine ⟨𝒰.nonemptyMembers, fun i ↦ ?_⟩
  let U := 𝒰.etalePrecoverageToEtale i.1
  have := h𝒰 i.1
  obtain ⟨S, ⟨e⟩⟩ := (E.over U).mem_essImage_of_isConstant
  let _ : TopologicalSpace S := ⊥
  have : DiscreteTopology S := ⟨rfl⟩
  let j : E.over U ≅ (Etale.continuousMapSheafOfTypes T S).over U :=
    e.symm ≪≫
      ((T.smallEtaleTopology.overPullbackConstantSheafIso (Type (u + 1)) U).app S).symm ≪≫
      (T.smallEtaleTopology.overPullback (Type (u + 1)) U).mapIso
        (Etale.constantSheafIsoContinuousMapSheafOfTypes T S)
  obtain ⟨t⟩ := i.2
  exact ⟨S, Etale.finite_of_iso_continuousMapSheafOfTypes E hE U t
    ((sheafToPresheaf _ _).mapIso j), ⟨e.symm⟩⟩

end AlgebraicGeometry.Scheme
