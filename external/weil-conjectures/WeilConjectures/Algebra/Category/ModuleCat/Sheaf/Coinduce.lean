/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Sites.Adjunction
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Whiskering

/-!
# Coinduction for sheaves of modules over a constant ring

Let `R` be a ring and `J` a Grothendieck topology. Forgetting the `R`-module structure of a sheaf
of `R`-modules is left adjoint to coinduction `A ↦ Hom_ℤ(R, A)`, computed objectwise
(`CategoryTheory.Sheaf.forget₂CoinduceAdj`). Consequently a morphism from the underlying
abelian sheaf of a sheaf of `R`-modules `F` to an abelian sheaf `A` which is a monomorphism
corresponds to a monomorphism from `F` to the coinduced sheaf of `A`
(`CategoryTheory.Sheaf.mono_forget₂CoinduceAdj_homEquiv`).
-/

@[expose] public section

universe w v u

open CategoryTheory Limits

namespace CategoryTheory.Sheaf

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C) (R : Type w) [Ring R]
  [J.HasSheafCompose (forget₂ (ModuleCat.{w} R) AddCommGrpCat.{w})]

/-- On sheaves, forgetting the `R`-module structure is left adjoint to coinduction
`A ↦ Hom_ℤ(R, A)`, both computed objectwise: this is the adjunction induced by
`ModuleCat.forget₂CoinduceAdj` on coefficients. -/
noncomputable def forget₂CoinduceAdj :
    sheafCompose J (forget₂ (ModuleCat.{w} R) AddCommGrpCat.{w}) ⊣
      sheafCompose J (ModuleCat.coinduce R) :=
  sheafComposeAdjunction J (ModuleCat.forget₂CoinduceAdj R)

/-- A monomorphism from the underlying abelian sheaf of a sheaf of `R`-modules `F` to an
abelian sheaf `A` corresponds to a monomorphism from `F` to the coinduced sheaf of `A`. -/
lemma mono_forget₂CoinduceAdj_homEquiv {F : Sheaf J (ModuleCat.{w} R)}
    {A : Sheaf J AddCommGrpCat.{w}}
    (f : (sheafCompose J (forget₂ (ModuleCat.{w} R) AddCommGrpCat.{w})).obj F ⟶ A) [Mono f] :
    Mono ((forget₂CoinduceAdj J R).homEquiv _ _ f) where
  right_cancellation g h hgh := by
    apply (sheafCompose J (forget₂ (ModuleCat.{w} R) AddCommGrpCat.{w})).map_injective
    rw [← cancel_mono f]
    simpa [Adjunction.homEquiv_naturality_left_symm] using
      congrArg ((forget₂CoinduceAdj J R).homEquiv _ _).symm hgh

end CategoryTheory.Sheaf
