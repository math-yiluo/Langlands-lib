/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import WeilConjectures.AlgebraicGeometry.EtaleSheaves
public import Mathlib.AlgebraicGeometry.Sites.EtalePoint
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint
/-! # NonzeroGermWitness

Source: blueprint `lem-weil-pbc-lisse-generic-kernel`, first proof step.
(blueprint: lem-weil-pbc-nonzero-germ-witness) -/

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme
/-- The first, stalkwise part of the locally constant nonzero-germ argument.
Source: blueprint `lem-weil-pbc-locally-constant-nonzero-germs`, proof step 1.
The geometric stalks are jointly faithful, so a nonzero map has a nonzero value
on some pointed etale neighbourhood.
(blueprint: lem-weil-pbc-nonzero-germ-witness)

Proof:
1. Suppose every image of every section has zero germ. For the algebraic closure
   point at each point of X, precompose the stalk map with all germ maps.
2. Naturality identifies these composites with the germs of the image sections,
   which vanish by assumption. The germ maps jointly detect equality of maps
   out of the stalk, so the stalk map equals zero.
3. Apply the existing joint faithfulness theorem
   `sheafHom_ext_of_sheafFiber_map_algClosurePoint` to conclude that the original
   morphism is zero, a contradiction. A lift from Spec of a field supplies an
   underlying point of its neighbourhood, proving nonemptiness. -/
theorem exists_section_nonzero_at_some_germ (X : Scheme.{u})
    (N F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (ψ : N ⟶ F) (hψ : ψ ≠ 0) :
    ∃ (U : X.Etale) (_ : Nonempty U.left) (s : N.obj.obj (op U)),
      ∃ (Ω : Type u), ∃ (_ : Field Ω) (_ : IsAlgClosed Ω)
        (t : Spec (.of Ω) ⟶ X) (v : (pointSmallEtale t).fiber.obj U),
        (pointSmallEtale t).toPresheafFiber U v F.obj
          (ψ.hom.app (op U) s) ≠ 0 := by
  classical
  by_contra h
  apply hψ
  apply sheafHom_ext_of_sheafFiber_map_algClosurePoint
  intro x
  apply (pointSmallEtale (X.algClosurePoint x)).presheafFiber_hom_ext
  intro U v
  ext s
  have hn : Nonempty U.left := ⟨v.left (IsLocalRing.closedPoint _)⟩
  have hz : (pointSmallEtale (X.algClosurePoint x)).toPresheafFiber U v F.obj
      (ψ.hom.app (op U) s) = 0 := by
    by_contra hs
    exact h ⟨U, hn, s, AlgebraicClosure (X.residueField x), inferInstance,
      inferInstance, X.algClosurePoint x, v, hs⟩
  change ((pointSmallEtale (X.algClosurePoint x)).presheafFiber.map ψ.hom)
    ((pointSmallEtale (X.algClosurePoint x)).toPresheafFiber U v N.obj s) = _
  rw [GrothendieckTopology.Point.toPresheafFiber_naturality_apply]
  simpa using hz
end AlgebraicGeometry.Scheme
