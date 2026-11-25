/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Sites.Gm
public import WeilConjectures.FieldTheory.GaloisUnitsCohomology
public import Mathlib.AlgebraicGeometry.Sites.EtalePoint

import WeilConjectures.AlgebraicGeometry.EtaleUnitsStalkEvaluationSurjective
import WeilConjectures.AlgebraicGeometry.EtaleUnitsStalkEvaluationInjective

/-!
# Bijectivity of evaluation on the geometric stalk of units

Source: Stacks Project, Tags 03QU and Example 03QV (2).
(blueprint: lem-sc-etale-units-stalk-evaluation-bijective).
-/

@[expose] public section

universe u

open CategoryTheory Opposite

namespace AlgebraicGeometry.Scheme

/-- A stalk homomorphism satisfying the evaluation formula is bijective.

Source: Stacks Project, Tags 03QU and Example 03QV (2).
(blueprint: lem-sc-etale-units-stalk-evaluation-bijective).

Proof: For surjectivity, a separable-closure unit and its inverse belong to a finite
separable extension of the base field. Its spectrum is an etale neighbourhood,
and its embedding in the algebraic closure supplies the lift. The corresponding
unit germ has the prescribed value by the evaluation formula and injectivity of
the separable-closure embedding. For injectivity, represent both stalk elements
by germs and refine each to the spectrum of a finite separable field extension.
The two embeddings into the algebraic closure identify their images with finite
separable subextensions. Their compositum is a common pointed etale refinement.
Equality of evaluated values says the two pulled-back units are equal in this
compositum, so their germs agree in the colimit. This works for imperfect base
fields because every extension used here is separable. No Galois equivariance is
assumed or concluded. -/
theorem etale_units_stalk_evaluation_bijective (K : Type u) [Field K] :
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
      Function.Bijective f := by
  dsimp
  intro f hf
  exact ⟨etale_units_stalk_evaluation_injective K f hf,
    etale_units_stalk_evaluation_surjective K f hf⟩

end AlgebraicGeometry.Scheme
