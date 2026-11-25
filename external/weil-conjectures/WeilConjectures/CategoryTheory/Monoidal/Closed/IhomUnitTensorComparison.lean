/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.DualizableCriterion
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Rigid.Comparison
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenImmersionIhom

/-!
# Dualizability through a monoidal functor commuting with internal homs

For a monoidal functor `G : C ⥤ D` between monoidal closed categories, the comparison map
`[X, 𝟙] ⊗ Z ⟶ [X, Z]` (`CategoryTheory.MonoidalClosed.ihomUnitTensorToIhom`) is carried by `G` to
the comparison map of `G X` and `G Z`, up to the tensorator, the unit and the comparison maps
`G [X, -] ⟶ [G X, G -]` (`CategoryTheory.Functor.Monoidal.map_ihomUnitTensorToIhom_comp`). So
when the comparison maps at `𝟙` and `Z` are isomorphisms, `G` preserves and reflects the
invertibility of the comparison map. Since in a braided monoidal closed category `X` is
dualizable if and only if `[X, 𝟙] ⊗ X ⟶ [X, X]` is an isomorphism
(`CategoryTheory.MonoidalClosed.isDualizable_iff_isIso_ihomUnitTensorToIhom`), this applies to
dualizability.

We specialise to the pullback `Lj^*` along an open immersion `j` on bounded constructible
`ℚ̄_ℓ`-complexes, which commutes with internal homs
(`ProEtale.CondensedRing.isIso_ihomComparison_boundedConstructibleUpperStar_of_isOpenImmersion`).

## Main statements

- `CategoryTheory.Functor.Monoidal.isIso_map_ihomUnitTensorToIhom_iff`: `G` of the comparison
  map of `X` and `Z` is an isomorphism if and only if the comparison map of `G X` and `G Z` is.
- `AlgebraicGeometry.ProEtale.CondensedRing.isIso_map_ihomUnitTensorToIhom_of_isDualizable`:
  if `Lj^* L` is dualizable, then `Lj^*` of `[L, 𝟙] ⊗ L ⟶ [L, L]` is an isomorphism.
- `AlgebraicGeometry.ProEtale.CondensedRing.isDualizable_of_isIso_ihomUnitTensorToIhom`: a
  bounded constructible complex `L` with `[L, 𝟙] ⊗ L ⟶ [L, L]` an isomorphism is dualizable.
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory MonoidalClosed

open scoped CategoryTheory.Obj

namespace CategoryTheory.Functor.Monoidal

open LaxMonoidal

variable {C D : Type*} [Category* C] [Category* D] [MonoidalCategory C] [MonoidalCategory D]
  [MonoidalClosed C] [MonoidalClosed D] (G : C ⥤ D) [G.Monoidal]

/-- If the comparison maps `G [X, 𝟙] ⟶ [G X, G 𝟙]` and `G [X, Z] ⟶ [G X, G Z]` are isomorphisms,
then `G` of the comparison map `[X, 𝟙] ⊗ Z ⟶ [X, Z]` is an isomorphism if and only if the
comparison map `[G X, 𝟙] ⊗ G Z ⟶ [G X, G Z]` is. -/
theorem isIso_map_ihomUnitTensorToIhom_iff (X Z : C)
    [IsIso ((ihomComparison G X).app (𝟙_ C))]
    [IsIso ((ihomComparison G X).app Z)] :
    IsIso (G.map (ihomUnitTensorToIhom X Z)) ↔
      IsIso (ihomUnitTensorToIhom (G.obj X) (G.obj Z)) := by
  rw [← isIso_comp_right_iff _ ((ihomComparison G X).app Z),
    map_ihomUnitTensorToIhom_comp, isIso_comp_left_iff, isIso_comp_left_iff]

end CategoryTheory.Functor.Monoidal

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

attribute [local instance] boundedConstructibleBraiding

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)] {U X : Over (Spec (.of k))} [LocallyOfFiniteType U.hom]
  [QuasiCompact U.hom] [IsSeparated U.hom] [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
  [IsSeparated X.hom]

/-- For an open immersion `j : U ⟶ X` and a bounded constructible `ℚ̄_ℓ`-complex `L` on `X` whose
restriction `Lj^* L` is dualizable, `Lj^*` carries the comparison map `[L, 𝟙] ⊗ L ⟶ [L, L]` to
an isomorphism: `Lj^*` commutes with internal homs, and the comparison map of `Lj^* L` is an
isomorphism. -/
theorem isIso_map_ihomUnitTensorToIhom_of_isDualizable (j : U ⟶ X) [IsOpenImmersion j.left]
    (L : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    (hL : IsDualizable ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ j).obj
      L)) :
    IsIso ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ j).map
      (ihomUnitTensorToIhom L L)) := by
  have := isIso_ihomComparison_boundedConstructibleUpperStar_of_isOpenImmersion ℓ j L
  rw [Functor.Monoidal.isIso_map_ihomUnitTensorToIhom_iff,
    ← isDualizable_iff_isIso_ihomUnitTensorToIhom]
  exact hL

/-- Conversely, for an open immersion `j : U ⟶ X` and a bounded constructible `ℚ̄_ℓ`-complex `L`
on `X`, if `Lj^*` carries the comparison map `[L, 𝟙] ⊗ L ⟶ [L, L]` to an isomorphism, then the
restriction `Lj^* L` is dualizable. -/
theorem isDualizable_obj_of_isIso_map_ihomUnitTensorToIhom (j : U ⟶ X) [IsOpenImmersion j.left]
    (L : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    (hL : IsIso ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ j).map
      (ihomUnitTensorToIhom L L))) :
    IsDualizable ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ j).obj L) := by
  have := isIso_ihomComparison_boundedConstructibleUpperStar_of_isOpenImmersion ℓ j L
  rw [isDualizable_iff_isIso_ihomUnitTensorToIhom,
    ← Functor.Monoidal.isIso_map_ihomUnitTensorToIhom_iff]
  exact hL


/-- A bounded constructible `ℚ̄_ℓ`-complex `L` whose comparison map `[L, 𝟙] ⊗ L ⟶ [L, L]` is an
isomorphism is dualizable: `[L, 𝟙]` is a left dual of `L`
(`CategoryTheory.MonoidalClosed.exactPairingOfIsIso`), hence a right dual by the braiding. -/
theorem isDualizable_of_isIso_ihomUnitTensorToIhom
    (L : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) (hL : IsIso (ihomUnitTensorToIhom L L)) :
    IsDualizable L :=
  (isDualizable_iff_isIso_ihomUnitTensorToIhom L).2 hL

end AlgebraicGeometry.ProEtale.CondensedRing
