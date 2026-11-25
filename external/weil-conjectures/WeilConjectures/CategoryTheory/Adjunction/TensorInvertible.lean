/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Adjunction.Unique
public import Mathlib.CategoryTheory.Monoidal.Functor
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Rigid.Basic

/-!
# Right adjoints commute with tensoring by an invertible object

Let `adj : F ⊣ G` be an adjunction between monoidal categories, with `F : C ⥤ D`, and let
`P : D ⥤ C` be a monoidal functor. If `L` is a `⊗`-invertible object of `D`, with inverse `M`,
and `F` satisfies the projection formula `F (-) ⊗ M ≅ F (- ⊗ P M)` at `M`, then
`G (- ⊗ L) ≅ G (-) ⊗ P L`. Both sides are right adjoints, of `F (-) ⊗ M` and of `F (- ⊗ P M)`
respectively, since tensoring with an invertible object is an equivalence.

This is the formal part of the co-projection formula `Ri^! (K ⊗ L) ≅ Ri^! K ⊗ Li^* L` of the
purity chapter (blueprint `lem-pur-coprojection`), with `F = Ri_!`, `G = Ri^!` and `P = Li^*`.

## Main definitions

- `CategoryTheory.Adjunction.tensorRightCompIsoOfTensorIso`: the isomorphism
  `G (- ⊗ L) ≅ G (-) ⊗ P L` of functors.
-/

@[expose] public section

namespace CategoryTheory

open MonoidalCategory

namespace Adjunction

variable {C D : Type*} [Category* C] [Category* D] [MonoidalCategory C] [MonoidalCategory D]
  {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G) (P : D ⥤ C) [P.Monoidal] {L M : D}

/-- **Right adjoints commute with tensoring by an invertible object.** Let `adj : F ⊣ G`, let
`P` be a monoidal functor in the opposite direction, let `L` have the two-sided tensor inverse
`M` (`e : M ⊗ L ≅ 𝟙_ D`, `e' : L ⊗ M ≅ 𝟙_ D`), and let `pf : F (-) ⊗ M ≅ F (- ⊗ P M)` be a
projection formula at `M`. Then `G (- ⊗ L) ≅ G (-) ⊗ P L`.

The functor `G (- ⊗ L)` is right adjoint to `F (-) ⊗ M`, and `G (-) ⊗ P L` is right adjoint to
`F (- ⊗ P M)`, because `- ⊗ M ⊣ - ⊗ L` and `- ⊗ P M ⊣ - ⊗ P L` (the object `P M` being a tensor
inverse of `P L` as `P` is monoidal). The isomorphism is the one induced by `pf` on right
adjoints. -/
noncomputable def tensorRightCompIsoOfTensorIso (e : M ⊗ L ≅ 𝟙_ D) (e' : L ⊗ M ≅ 𝟙_ D)
    (pf : F ⋙ tensorRight M ≅ tensorRight (P.obj M) ⋙ F) :
    tensorRight L ⋙ G ≅ G ⋙ tensorRight (P.obj L) :=
  rightAdjointUniq
    ((adj.comp (tensorRightEquivalenceOfTensorIso e e').toAdjunction).ofNatIsoLeft pf)
    ((tensorRightEquivalenceOfTensorIso
      (Functor.Monoidal.μIso P M L ≪≫ P.mapIso e ≪≫ (Functor.Monoidal.εIso P).symm)
      (Functor.Monoidal.μIso P L M ≪≫ P.mapIso e' ≪≫
        (Functor.Monoidal.εIso P).symm)).toAdjunction.comp adj)

end Adjunction

end CategoryTheory
