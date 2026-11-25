/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.RingTheory.AdicCompletion.Basic
import WeilConjectures.AlgebraicGeometry.EtaleOpenOfInfinitesimalRestrictions
import WeilConjectures.AlgebraicGeometry.ProperEtaleOpen

/-!
# Étaleness detected by infinitesimal restrictions with proper source

Source: Stacks Project, Fundamental Groups, Tag 0GS2, complete Noetherian
essential-surjectivity paragraph, the last two sentences before the conclusion
(blueprint: lem-weil-pbc-etale-infinitesimal-restrictions-proper).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry


/-- A finite type morphism to a locally Noetherian scheme is étale if all its
infinitesimal restrictions are étale and its source is proper over the complete base.
Source: Stacks Project, Tag 0GS2, complete Noetherian essential-surjectivity
paragraph, using More on Morphisms, Tag 0A43(2), and Algebra, Tag 05GI(4).
(blueprint: lem-weil-pbc-etale-infinitesimal-restrictions-proper).

Proof:
1. Let j : Y_0 → Y be the projection from Y ×_A Spec(A/I), and J its ideal
   sheaf. This is a closed immersion. On every affine open Spec R of Y,
   J is IR, and the (n+1)st power is I^(n+1)R. Thus the closed subscheme
   cut out by J^(n+1) is canonically Y ×_A Spec(A/I^(n+1)). Under these
   identifications the base changes of g in the hypothesis are exactly
   the infinitesimal neighbourhood restrictions.
2. Apply etale_on_open_of_etale_infinitesimal_neighbourhoods to obtain
   an open W of X containing g^(-1)(Y_0), with g restricted to W étale.
3. Completeness gives I ≤ jacobson(0). For x in X, the image of the
   nonempty closed set closure({x}) under the proper map g ≫ f is closed
   and nonempty. Any nonempty closed subset of Spec A contains a maximal
   ideal m, and every such m contains I. Hence there is t in closure({x})
   mapping to V(I). The image of Y_0 → Y is f^(-1)(V(I)), as follows
   from the affine description Spec(R/IR) above. Thus t lies in W.
4. Since W is open and t is a specialization of x, x also lies in W.
   Therefore W is all of X, and the étaleness of its restriction proves
   Etale g. If X is empty this argument is vacuous and still valid. -/
theorem etale_of_infinitesimal_restrictions_of_proper
    {A : Type u} [CommRing A] (I : Ideal A) [IsAdicComplete I A]
    {X Y : Scheme.{u}} (f : Y ⟶ Spec (.of A)) (g : X ⟶ Y)
    [IsLocallyNoetherian Y] [LocallyOfFiniteType g] [QuasiCompact g]
    [IsProper (g ≫ f)]
    (h_etale : ∀ n : ℕ, Etale (pullback.snd g (pullback.fst f
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1)))))))) :
    Etale g := by
  obtain ⟨W, hW, hEt⟩ :=
    etale_open_of_infinitesimal_restrictions I f g h_etale
  have htop : W = ⊤ := proper_closed_fiber_open_eq_top I f g W hW
  subst W
  let : Etale ((⊤ : X.Opens).ι ≫ g) := hEt
  have : Etale (X.topIso.inv ≫ ((⊤ : X.Opens).ι ≫ g)) := inferInstance
  simpa only [← Category.assoc, Scheme.toIso_inv_ι, Category.id_comp] using this

end AlgebraicGeometry
