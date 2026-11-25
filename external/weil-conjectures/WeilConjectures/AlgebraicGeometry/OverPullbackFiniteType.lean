/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.CategoryTheory.Comma.Over.Pullback

/-!

# Fibre products of separated `k`-schemes of finite type

For morphisms `f : X ⟶ Y` and `g : Z ⟶ Y` of separated `k`-schemes of finite type, viewed as
objects of `Over (Spec k)`, the fibre product `pullback f g` (in `Over (Spec k)`) is again a
separated `k`-scheme of finite type, and its projections are base changes of `f` and `g`: they
inherit smoothness and being an open or closed immersion.

-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

variable {k : Type u} [Field k] {X Y Z : Over (Spec (.of k))} (f : X ⟶ Y) (g : Z ⟶ Y)

/-- The underlying square of schemes of the fibre product in `Over (Spec k)` is cartesian. -/
lemma isPullback_pullback_left :
    IsPullback (pullback.fst f g).left (pullback.snd f g).left f.left g.left := by
  have h := (IsPullback.of_hasPullback f g).map (Over.forget _)
  simpa only [Over.forget_map] using h

/-- The structure morphism of the fibre product is the second projection followed by that
of `Z`. -/
lemma pullback_hom_eq_snd_left_comp : (pullback f g).hom = (pullback.snd f g).left ≫ Z.hom := by
  rw [← Over.w (pullback.snd f g)]

variable [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
  [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [IsSeparated Z.hom]

/-- A morphism of `k`-schemes of finite type is locally of finite type. -/
instance locallyOfFiniteType_left_of_over : LocallyOfFiniteType f.left := by
  have : LocallyOfFiniteType (f.left ≫ Y.hom) := by rw [Over.w f]; infer_instance
  exact locallyOfFiniteType_of_comp f.left Y.hom

/-- A morphism of `k`-schemes of finite type is quasi-compact. -/
instance quasiCompact_left_of_over : QuasiCompact f.left := by
  have : QuasiCompact (f.left ≫ Y.hom) := by rw [Over.w f]; infer_instance
  exact QuasiCompact.of_comp f.left Y.hom

/-- A morphism of separated `k`-schemes is separated. -/
instance isSeparated_left_of_over : IsSeparated f.left := by
  have : IsSeparated (f.left ≫ Y.hom) := by rw [Over.w f]; infer_instance
  exact IsSeparated.of_comp f.left Y.hom

/-- The fibre product of `k`-schemes of finite type is of finite type. -/
instance locallyOfFiniteType_over_pullback_hom : LocallyOfFiniteType (pullback f g).hom := by
  have : LocallyOfFiniteType (pullback.snd f g).left :=
    MorphismProperty.of_isPullback (isPullback_pullback_left f g) inferInstance
  rw [pullback_hom_eq_snd_left_comp]
  infer_instance

/-- The fibre product of `k`-schemes of finite type is quasi-compact. -/
instance quasiCompact_over_pullback_hom : QuasiCompact (pullback f g).hom := by
  have : QuasiCompact (pullback.snd f g).left :=
    MorphismProperty.of_isPullback (isPullback_pullback_left f g) inferInstance
  rw [pullback_hom_eq_snd_left_comp]
  infer_instance

/-- The fibre product of separated `k`-schemes is separated. -/
instance isSeparated_over_pullback_hom : IsSeparated (pullback f g).hom := by
  have : IsSeparated (pullback.snd f g).left :=
    MorphismProperty.of_isPullback (isPullback_pullback_left f g) inferInstance
  rw [pullback_hom_eq_snd_left_comp]
  infer_instance

omit [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
  [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [IsSeparated Z.hom] in
/-- The base change of a smooth morphism is smooth. -/
instance smooth_over_pullback_snd_left [Smooth f.left] :
    Smooth (pullback.snd f g).left :=
  MorphismProperty.of_isPullback (isPullback_pullback_left f g) inferInstance

omit [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
  [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [IsSeparated Z.hom] in
/-- The base change of a closed immersion is a closed immersion. -/
instance isClosedImmersion_over_pullback_fst_left [IsClosedImmersion g.left] :
    IsClosedImmersion (pullback.fst f g).left :=
  MorphismProperty.of_isPullback (isPullback_pullback_left f g).flip inferInstance

omit [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
  [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [IsSeparated Z.hom] in
/-- The base change of an open immersion is an open immersion. -/
instance isOpenImmersion_over_pullback_fst_left [IsOpenImmersion g.left] :
    IsOpenImmersion (pullback.fst f g).left :=
  MorphismProperty.of_isPullback (isPullback_pullback_left f g).flip inferInstance

end AlgebraicGeometry
