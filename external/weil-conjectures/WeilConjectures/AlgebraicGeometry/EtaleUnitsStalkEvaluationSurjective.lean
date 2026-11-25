/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Sites.Gm
public import WeilConjectures.FieldTheory.GaloisUnitsCohomology
public import Mathlib.AlgebraicGeometry.Sites.EtalePoint
import WeilConjectures.AlgebraicGeometry.EtaleUnitsStalkEvaluationOverfieldBijective

@[expose] public section

universe u

open CategoryTheory Opposite

namespace AlgebraicGeometry.Scheme

/-- Surjectivity part of geometric stalk evaluation.

Source: Stacks Project, Tags 03QU and Example 03QV (2).
(blueprint: lem-sc-etale-units-stalk-evaluation-surjective).

Proof: Let a be a unit of the separable closure, with its multiplicative group
written additively. The subfield L = K(a) inside the separable closure is finite
and separable over K and contains both a and its inverse. Spec L is therefore
etale over Spec K, and the composite embedding of L into the algebraic closure
gives a geometric lift x. Via the global-sections isomorphism for Spec L, a and
its inverse define a unit section z on this neighbourhood. Let t be the germ
of z at x. The evaluation formula for f says that the underlying value of f(t)
embedded in the algebraic closure is the embedded value of a. Injectivity of the
separable-closure embedding, followed by extensionality of units and transport
through the additive wrapper, gives f(t) = a. Thus every target element has a
preimage. This construction uses only separable extensions, even for imperfect K. -/
theorem etale_units_stalk_evaluation_surjective (K : Type u) [Field K] :
    let Ω := AlgebraicClosure K
    let S := Spec (.of K)
    let p := pointSmallEtale (Spec.map (CommRingCat.ofHom (algebraMap K Ω)))
    ∀ f : (p.sheafFiber (A := AddCommGrpCat.{u + 1})).obj S.gmSheaf →+
        Field.galoisUnitsTopRep K,
      (∀ (X : S.Etale) (x : p.fiber.obj X) (z : S.gmSheaf.obj.obj (op X)),
        algebraMap (SeparableClosure K) Ω
            (Additive.toMul (f (p.toPresheafFiber X x S.gmSheaf.obj z)) :
              (SeparableClosure K)ˣ) =
          (ΓSpecIso (.of Ω)).hom
            (x.left.appTop ((Additive.toMul z.down : Γ(X.left, ⊤)ˣ) : Γ(X.left, ⊤)))) →
      Function.Surjective f := by
  dsimp only
  intro f hev
  exact (etaleUnits_stalk_evaluation_overfield_bijective K (AlgebraicClosure K) f hev).2

end AlgebraicGeometry.Scheme
