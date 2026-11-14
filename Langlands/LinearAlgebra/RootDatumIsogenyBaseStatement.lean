import Langlands.LinearAlgebra.RootDatumIsogeny
import Mathlib.LinearAlgebra.RootSystem.Base

/-! # Statement: isogenies of root data carry bases to bases -/

universe u₁ u₂ u₃ u₄ u₅ u₆

namespace Langlands.LinearAlgebra

/-- **Isogenies of root data carry bases to bases** (Conrad, *Reductive group schemes* (2014),
Lemma 6.1.12). Let `f : P → Q` be an isogeny of finite reduced root data in characteristic
exponent `p` (a `p`-morphism `Q → P` in Conrad's direction: `f.weightMap` is Conrad's `h`,
`f.indexEquiv` is the inverse of Conrad's root bijection `d`). For every base `b'` of `Q`
there is a base `b` of `P` whose simple roots are the roots of `P` corresponding to the simple
roots of `b'`, and whose positive roots are the roots of `P` corresponding to the positive
roots of `b'`. -/
def RootDatumIsogenyBaseStatement : Prop :=
  ∀ (p : ℕ) {ι : Type u₁} {X : Type u₂} {Y : Type u₃} {ι₂ : Type u₄} {X₂ : Type u₅}
    {Y₂ : Type u₆}
    [AddCommGroup X] [AddCommGroup Y] [AddCommGroup X₂] [AddCommGroup Y₂]
    [Finite ι] [Finite ι₂]
    [Module.Finite ℤ X] [Module.Finite ℤ Y] [Module.Finite ℤ X₂] [Module.Finite ℤ Y₂]
    (P : RootDatum ι X Y) (Q : RootDatum ι₂ X₂ Y₂) [P.IsReduced] [Q.IsReduced]
    (f : RootDatumIsogeny p P Q) (b' : Q.Base),
    ∃ b : P.Base,
      (∀ i : ι, i ∈ b.support ↔ f.indexEquiv i ∈ b'.support) ∧
      ∀ i : ι, b.IsPos i ↔ b'.IsPos (f.indexEquiv i)

end Langlands.LinearAlgebra
