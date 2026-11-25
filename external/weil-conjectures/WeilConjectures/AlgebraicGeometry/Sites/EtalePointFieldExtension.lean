/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Sites.StrictHenselizationFunctoriality
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Point.Category
public import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.CospecializationSections

/-!
# Geometric points under an extension of separably closed fields

Let `c : Spec κ ⟶ Y` be a geometric point, `κ` separably closed, and let
`ρ : Spec K ⟶ Spec κ` be a morphism from the spectrum of another separably closed field. Then
the geometric points `c` and `ρ ≫ c` of the small étale site of `Y` are isomorphic: for an étale
`Y`-scheme `V`, every lift `Spec K ⟶ V` of `ρ ≫ c` factors uniquely as `ρ` followed by a lift
`Spec κ ⟶ V` of `c`, because `κ` is a strictly henselian local ring
(`AlgebraicGeometry.existsUnique_lift_of_etale`). In particular the stalks of an étale sheaf at
`c` and at `ρ ≫ c` agree.

## Main definitions

- `AlgebraicGeometry.Scheme.pointSmallEtaleFiberExtendIso`: the isomorphism of fibre functors.
- `AlgebraicGeometry.Scheme.pointSmallEtaleExtendIso`: the isomorphism of points
  `ρ ≫ c ≅ c`.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.Scheme

variable {Y : Scheme.{u}} {κ K : Type u} [Field κ] [IsSepClosed κ] [Field K] [IsSepClosed K]
  (c : Spec (.of κ) ⟶ Y) (ρ : Spec (.of K) ⟶ Spec (.of κ))

omit [IsSepClosed K] in
/-- A lift `Spec K ⟶ V` of `ρ ≫ c` along an étale `V ⟶ Y` factors uniquely through a lift of
`c`. -/
lemma existsUnique_lift_of_isSepClosed (V : Y.Etale) (v : Spec (.of K) ⟶ V.left)
    (hv : v ≫ V.hom = ρ ≫ c) :
    ∃! w : Spec (.of κ) ⟶ V.left, w ≫ V.hom = c ∧ ρ ≫ w = v := by
  have : Etale V.hom := V.prop
  have : IsStrictlyHenselianLocalRing (CommRingCat.of κ) :=
    inferInstanceAs (IsStrictlyHenselianLocalRing κ)
  have he : RingHom.ker (Spec.preimage ρ).hom = IsLocalRing.maximalIdeal (CommRingCat.of κ) := by
    rw [(RingHom.injective_iff_ker_eq_bot _).1 (Spec.preimage ρ).hom.injective,
      IsLocalRing.maximalIdeal_eq_bot]
  obtain ⟨w, ⟨hw₁, hw₂⟩, hw⟩ :=
    existsUnique_lift_of_etale (Spec.preimage ρ) he V.hom c v (by rw [hv, Spec.map_preimage])
  rw [Spec.map_preimage] at hw₂
  exact ⟨w, ⟨hw₁, hw₂⟩, fun w' ⟨h₁, h₂⟩ ↦ hw w' ⟨h₁, by rwa [Spec.map_preimage]⟩⟩

/-- The morphism `ρ` as a morphism of geometric points over `Y`. -/
noncomputable def overHomOfExtend :
    CategoryTheory.Over.mk (ρ ≫ c) ⟶ CategoryTheory.Over.mk c :=
  CategoryTheory.Over.homMk ρ

/-- The bijection between lifts of `c` and lifts of `ρ ≫ c` to an étale `Y`-scheme `V`, given
by precomposition with `ρ`. -/
noncomputable def pointSmallEtaleFiberExtendEquiv (V : Y.Etale) :
    (pointSmallEtale c).fiber.obj V ≃ (pointSmallEtale (ρ ≫ c)).fiber.obj V :=
  Equiv.ofBijective
    (fun w ↦ overHomOfExtend c ρ ≫ w) (by
    constructor
    · intro w₁ w₂ hw
      have h := congrArg CommaMorphism.left hw
      dsimp at h
      have hw₁ := CategoryTheory.Over.w w₁
      have hw₂ := CategoryTheory.Over.w w₂
      dsimp at hw₁ hw₂
      obtain ⟨w, -, hu⟩ := existsUnique_lift_of_isSepClosed c ρ V (ρ ≫ w₁.left)
        (by rw [Category.assoc, hw₁])
      exact CategoryTheory.Over.OverMorphism.ext
        ((hu _ ⟨hw₁, rfl⟩).trans (hu _ ⟨hw₂, h.symm⟩).symm)
    · intro v
      have hv := CategoryTheory.Over.w v
      dsimp at hv
      obtain ⟨w, ⟨hw₁, hw₂⟩, -⟩ := existsUnique_lift_of_isSepClosed c ρ V v.left hv
      exact ⟨CategoryTheory.Over.homMk w hw₁, CategoryTheory.Over.OverMorphism.ext hw₂⟩)

/-- The fibre functors of the geometric points `c` and `ρ ≫ c` are isomorphic. -/
noncomputable def pointSmallEtaleFiberExtendIso :
    (pointSmallEtale c).fiber ≅ (pointSmallEtale (ρ ≫ c)).fiber :=
  NatIso.ofComponents (fun V ↦ (pointSmallEtaleFiberExtendEquiv c ρ V).toIso)
    (fun f ↦ by
      ext w
      change overHomOfExtend c ρ ≫ (w ≫ _) = (overHomOfExtend c ρ ≫ w) ≫ _
      exact (Category.assoc _ _ _).symm)

/-- **Extending a geometric point by a separably closed field**: the geometric points
`ρ ≫ c` and `c` of the small étale site of `Y` are isomorphic. -/
noncomputable def pointSmallEtaleExtendIso : pointSmallEtale (ρ ≫ c) ≅ pointSmallEtale c :=
  GrothendieckTopology.Point.isoMk (pointSmallEtaleFiberExtendIso c ρ).symm

end AlgebraicGeometry.Scheme
