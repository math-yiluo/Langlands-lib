/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.ConstructibleSheaf.Monoidal

/-!
# The tensor product of finite sheaves of modules is finite

Let `Λ` be a commutative ring. For sheaves `F` and `G` of `Λ`-modules on the small étale site
of a scheme `X` whose geometric stalks are finitely generated (`IsFiniteSheaf`), the tensor
product `F ⊗ G` again has finitely generated geometric stalks: the stalk functor is strong
monoidal (`AlgebraicGeometry.Etale.sheafFiberTensorIso`), and the tensor product of two
finitely generated modules is finitely generated.

## Main results

- `AlgebraicGeometry.Scheme.IsFiniteSheaf.tensorObj`
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory

namespace AlgebraicGeometry.Scheme

variable {X : Scheme.{u}} {Λ : Type (u + 1)} [CommRing Λ]
  {F G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)}

/-- **The tensor product of finite sheaves of modules is finite**: for sheaves `F` and `G` of
`Λ`-modules on the small étale site with finitely generated geometric stalks, the geometric
stalks of `F ⊗ G` are `F_s ⊗ G_s`, finitely generated.
(blueprint: `lem-weil-pbc-flc-tensor-finite-part`) -/
theorem IsFiniteSheaf.tensorObj (hF : IsFiniteSheaf F) (hG : IsFiniteSheaf G) :
    IsFiniteSheaf (F ⊗ G) where
  isFinitelyGenerated_sheafFiber Ω _ _ s := by
    let Φ := (pointSmallEtale s).ulift.{u + 1}
    let e := (pointSmallEtale s).uliftSheafFiberIso.{u + 1} (ModuleCat.{u + 1} Λ)
    have hF' : Module.Finite Λ ((Φ.sheafFiber (A := ModuleCat.{u + 1} Λ)).obj F) :=
      (ModuleCat.isFinitelyGenerated_iff _).1
        ((hF.isFinitelyGenerated_sheafFiber Ω s).of_iso (e.app F).symm)
    have hG' : Module.Finite Λ ((Φ.sheafFiber (A := ModuleCat.{u + 1} Λ)).obj G) :=
      (ModuleCat.isFinitelyGenerated_iff _).1
        ((hG.isFinitelyGenerated_sheafFiber Ω s).of_iso (e.app G).symm)
    have : Module.Finite Λ
        (((Φ.sheafFiber (A := ModuleCat.{u + 1} Λ)).obj F ⊗
          (Φ.sheafFiber (A := ModuleCat.{u + 1} Λ)).obj G : ModuleCat.{u + 1} Λ)) :=
      inferInstanceAs (Module.Finite Λ (TensorProduct Λ
        ((Φ.sheafFiber (A := ModuleCat.{u + 1} Λ)).obj F)
        ((Φ.sheafFiber (A := ModuleCat.{u + 1} Λ)).obj G)))
    exact (((ModuleCat.isFinitelyGenerated_iff _).2 this).of_iso
      (Etale.sheafFiberTensorIso s F G).symm).of_iso (e.app (F ⊗ G))

end AlgebraicGeometry.Scheme
