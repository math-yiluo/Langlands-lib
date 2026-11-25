/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.RingTheory.AdicCompletion.Basic
import WeilConjectures.AlgebraicGeometry.EtaleInfinitesimalNeighbourhoods
import WeilConjectures.AlgebraicGeometry.QuotientBaseChangeIdeal

/-!
# Étale neighborhoods from quotient restrictions

Source: Stacks Project, Tag 0GS2, using Tag 0A43(2).
(blueprint: lem-weil-pbc-etale-infinitesimal-restrictions-proper-neighborhood).
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

/-- Étaleness on all infinitesimal restrictions yields an étale open neighborhood of
 the closed fiber. This packages the closed-immersion and ideal-sheaf identifications
 in the proof of Stacks Project, Tag 0GS2.

Proof:
1. Let j be the projection Y ×_A Spec(A/I) → Y. The quotient-base-change ideal
   theorem makes j a closed immersion and identifies its kernel with the extended
   ideal I O_Y. For the projection j_n from Y ×_A Spec(A/I^(n+1)), the same theorem
   and the extended-ideal power formula give j.ker^(n+1) = j_n.ker.
2. A closed immersion j_n is isomorphic to its scheme-theoretic image, whose
   inclusion is j_n.ker.subschemeι. Base change this isomorphism along g. The
   second-projection identity identifies the composite with the given étale
   restriction followed by j_n.toImage. Étaleness is preserved under composition
   with isomorphisms and reflected by precomposition with an isomorphism, so the
   restriction to (j.ker^(n+1)).subschemeι is étale.
3. Apply etale_on_open_of_etale_infinitesimal_neighbourhoods with j and j.ker.
   Its conclusion is exactly the desired open neighborhood and étaleness.
   The argument also covers an empty closed fiber, I = 0, and I = A.
(blueprint: lem-weil-pbc-etale-infinitesimal-restrictions-proper-neighborhood)
-/
theorem etale_open_of_infinitesimal_restrictions
    {A : Type u} [CommRing A] (I : Ideal A) [IsAdicComplete I A]
    {X Y : Scheme.{u}} (f : Y ⟶ Spec (.of A)) (g : X ⟶ Y)
    [IsLocallyNoetherian Y] [LocallyOfFiniteType g] [QuasiCompact g]
    (h_etale : ∀ n : ℕ, Etale (pullback.snd g (pullback.fst f
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1)))))))) :
    ∃ W : X.Opens,
      (g : X → Y) ⁻¹' Set.range
        (pullback.fst f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) : _ → _) ⊆
          (W : Set X) ∧ Etale (W.ι ≫ g) := by
  let j := pullback.fst f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))
  have hj := quotientBaseChange_closedImmersion_ideal f I
  have : IsClosedImmersion j := hj.1
  apply etale_on_open_of_etale_infinitesimal_neighbourhoods g j j.ker rfl
  intro n
  let jn := pullback.fst f
    (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1)))))
  have hjn := quotientBaseChange_closedImmersion_ideal f (I ^ (n + 1))
  have : IsClosedImmersion jn := hjn.1
  have hpow : j.ker ^ (n + 1) = jn.ker := by
    rw [hj.2.1, (quotientBaseChange_extendedIdeal_mul_pow f).2 I (n + 1)
      (Nat.le_add_left 1 n)]
    exact hjn.2.1.symm
  rw [hpow]
  have : Etale (pullback.snd g jn) := h_etale n
  let e := pullback.map g jn g jn.imageι (𝟙 X) jn.toImage (𝟙 Y)
    (by simp) (by simp)
  have : IsIso e := by dsimp [e]; infer_instance
  rw [← MorphismProperty.cancel_left_of_respectsIso (P := @Etale) e]
  simpa [e] using (inferInstance : Etale (pullback.snd g jn ≫ jn.toImage))

end AlgebraicGeometry
