/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.CohomologyFractionPresentation
public import WeilConjectures.AlgebraicGeometry.OpenSectionFractionPresentation
public import WeilConjectures.AlgebraicGeometry.OpenCohomologyZeroSections

/-! # Comparing degree-zero cohomology fractions with section fractions

Source: Stacks Project, Tag 09MR, degree-zero fraction presentation.
(blueprint: lem-sc-open-cohomology-fraction-zero-comparison).
-/

@[expose] public section

universe u
open CategoryTheory MonoidalCategory DirectSum
namespace AlgebraicGeometry.Scheme.Modules

/-- The canonical degree-zero comparison descends to fraction presentations on any open.
Source: Stacks Project, Tag 09MR, degree-zero case.
(blueprint: lem-sc-open-cohomology-fraction-zero-comparison).

Proof: Take the direct sum of the canonical additive equivalences on numerator groups.
Naturality in the coefficient module takes every fraction relation to its section
relation. Conversely every section numerator is the image of a cohomology numerator,
so the sets of relation generators correspond exactly. An additive equivalence takes
the additive closure of a set to the closure of its image. Hence it descends to an
additive equivalence of quotients, with the asserted formula on each generator. -/
theorem openCohomologyFraction_zero_comparison (X : Scheme.{u})
    (L F : X.Modules) (s : Γ(L, ⊤)) (U : X.Opens) :
    ∃ q : CohomologyFractionPresentation L F s 0 U ≃+
        OpenSectionFractionPresentation L F s U,
      ∀ (n : ℕ) (ξ : (RingedSpace.openModuleCohomology X.toRingedSpace 0 U).obj
          (F ⊗ L.tensorPow n : X.Modules)),
        q (cohomologyFraction L F s 0 U n ξ) =
          openSectionFraction L F s U n
            ((RingedSpace.openCohomologyZeroSectionsIso X.toRingedSpace U).hom.app
              (F ⊗ L.tensorPow n : X.Modules) ξ) := by
  classical
  let A (n : ℕ) : Type u :=
    (RingedSpace.openModuleCohomology X.toRingedSpace 0 U).obj
      (F ⊗ L.tensorPow n : X.Modules)
  let B (n : ℕ) : Type u := Γ(F ⊗ L.tensorPow n, U)
  let a (n : ℕ) : A n ≃+ B n :=
    ((RingedSpace.openCohomologyZeroSectionsIso X.toRingedSpace U).app
      (F ⊗ L.tensorPow n : X.Modules)).addCommGroupIsoToAddEquiv
  let d : (⨁ n : ℕ, A n) ≃+ (⨁ n : ℕ, B n) :=
    AddEquiv.ofBijective (DirectSum.map (fun n ↦ (a n).toAddMonoidHom))
      ⟨(DirectSum.map_injective _).mpr (fun n ↦ (a n).injective),
        (DirectSum.map_surjective _).mpr (fun n ↦ (a n).surjective)⟩
  have hd (n : ℕ) (ξ : A n) : d (DirectSum.of A n ξ) = DirectSum.of B n (a n ξ) := by
    exact DirectSum.map_of _ n ξ
  have ha (n b : ℕ) (ξ : A n) :
      a (n + b) ((RingedSpace.openModuleCohomology X.toRingedSpace 0 U).map
          (mulTensorPowSection (homOfGlobalSection L s) F n b) ξ) =
        (mulTensorPowSection (homOfGlobalSection L s) F n b).app U (a n ξ) := by
    exact congrArg (fun f ↦ f ξ)
      (RingedSpace.openCohomologyZeroSectionsIso_naturality X.toRingedSpace U
        (mulTensorPowSection (homOfGlobalSection L s) F n b))
  have hrel : (cohomologyFractionRelations L F s 0 U).map d.toAddMonoidHom =
      openSectionFractionRelations L F s U := by
    unfold cohomologyFractionRelations openSectionFractionRelations
    rw [AddMonoidHom.map_closure]
    congr 1
    ext z
    constructor
    · rintro ⟨w, ⟨n, b, ξ, rfl⟩, rfl⟩
      refine ⟨n, b, a n ξ, ?_⟩
      change d (_ - _) = _
      rw [map_sub, hd, hd, ha]
    · rintro ⟨n, b, t, rfl⟩
      refine ⟨_, ⟨n, b, (a n).symm t, rfl⟩, ?_⟩
      change d (_ - _) = _
      rw [map_sub, hd, hd, ha, AddEquiv.apply_symm_apply]
  refine ⟨QuotientAddGroup.congr _ _ d hrel, ?_⟩
  intro n ξ
  exact congrArg QuotientAddGroup.mk (hd n ξ)

end AlgebraicGeometry.Scheme.Modules
