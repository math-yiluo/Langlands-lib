/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.CategoryTheory.Limits.ExactFunctor

/-!
# Flat sheaves of modules

Source: Stacks Project, Modules on Sites, Definition 03ER, item (3)
(blueprint: def-pc-flat-sheaf-modules).

The tensor product is the one of `def-pur-sheaf-tensor-product`, the source's
`SheafOfModules.monoidalCategory R` (the sheafification of the sectionwise tensor product,
`SheafOfModules.tensorObjIsoSheafification`), on a site `C : Type u`, `Category.{u} C` in the
universe of the rings and modules, as for the K-flat complexes (`CochainComplex.IsKFlatTensor`).
The source's `CategoryTheory.ObjectProperty.flat` asks both `tensorLeft` and `tensorRight` to
be exact; the node asks it of `G ↦ G ⊗ F` only. By the symmetry of the tensor product the two
notions agree (`SheafOfModules.isFlat_iff_flat`).
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory

namespace SheafOfModules

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasWeakSheafify J AddCommGrpCat.{u}]
  {R : Sheaf J CommRingCat.{u}}

/-- A sheaf of modules `F` over a sheaf of commutative rings `R` is *flat* when the functor
`G ↦ G ⊗_R F` on sheaves of `R`-modules (the tensor product `SheafOfModules.monoidalCategory R`)
is exact: it preserves finite limits and finite colimits. The two instance arguments on the
site provide the sheafification of presheaves of modules, hence the abelian category `Mod(R)`.
Source: Stacks Project, Tag 03ER, item (3) (blueprint: def-pc-flat-sheaf-modules). -/
def IsFlat
    (F : SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) :
    Prop :=
  letI := SheafOfModules.monoidalCategory R
  exactFunctor _ _ (tensorRight F)

end SheafOfModules
