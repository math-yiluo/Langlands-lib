/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.CategoryTheory.MorphismProperty.Comma
public import Mathlib.RingTheory.Henselian
import WeilConjectures.AlgebraicGeometry.FiniteEtaleLiftingLimitDescent
import WeilConjectures.AlgebraicGeometry.FiniteEtaleLiftingApproximation

/-!
# Essential surjectivity of finite étale lifting over a henselian pair

Source: Stacks Project, Fundamental Groups, Lemma 0GS2, essential-surjectivity paragraphs
(blueprint: lem-weil-pbc-finite-etale-lifting-essential-surjectivity).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- Every finite étale cover of the closed fibre of a proper scheme over a henselian pair
lifts to a finite étale cover of the scheme, with an isomorphism over the closed fibre.
Source: Stacks Project, Fundamental Groups, Lemma 0GS2
(blueprint: lem-weil-pbc-finite-etale-lifting-essential-surjectivity).

Proof:
1. If `A` is Noetherian and `I`-adically complete, lift the cover uniquely to the nilpotent
   thickenings by formal étaleness. These lifts remain finite. Grothendieck algebraization
   gives a finite cover of `Y`; its étale locus contains the closed fibre. Properness and
   the Jacobson-radical condition on `I` imply that every point specializes into that fibre,
   so the cover is étale everywhere (lem-weil-pbc-finite-etale-lifting-complete).
2. For a Noetherian henselian G-ring, apply the complete case after completion. Descend
   the cover's finite presentation data, overlap maps and cocycle equations to a finite
   type algebra. Henselian G-ring approximation gives an algebra map back to `A` agreeing
   modulo `I`, and hence the desired lift (lem-weil-pbc-finite-etale-lifting-approximation).
3. In general, descend the proper scheme and its closed-fibre cover to finite type
   Noetherian models. Henselize the corresponding pairs; their rings are Noetherian
   G-rings and their filtered colimit is `A`. Apply the preceding case and base change
   back (lem-weil-pbc-finite-etale-lifting-limit-descent and
   lem-weil-pbc-finite-etale-lifting-approximation).
4. The constructed lift has the prescribed closed-fibre isomorphism. By the definition
   of the finite étale category (def-weil-pbc-finite-etale-category), this is exactly
   essential surjectivity. The closed fibre is `pullback f (Spec.map (Quotient.mk I))` with
   closed immersion `pullback.fst`, and the isomorphism is one of `Y₀`-schemes. -/
theorem Scheme.essSurj_pullback_finiteEtale_of_henselianRing
    {A : Type u} [CommRing A] (I : Ideal A) [HenselianRing A I]
    {Y : Scheme.{u}} (f : Y ⟶ Spec (.of A)) [IsProper f]
    (V : (@IsFinite ⊓ @Etale : MorphismProperty Scheme.{u}).Over ⊤
      (pullback f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))))) :
    ∃ U : (@IsFinite ⊓ @Etale : MorphismProperty Scheme.{u}).Over ⊤ Y,
      Nonempty
        (Over.mk (pullback.snd U.hom
          (pullback.fst f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))))) ≅
          Over.mk V.hom) := by
  apply Scheme.exists_finiteEtale_lift_of_henselianPair_of_gRing_lifting
    (fun B _ hB J _ Z g _ W ↦
      Scheme.exists_finiteEtale_lift_of_henselianPair_of_isGRing hB J g W) I f V

end AlgebraicGeometry
