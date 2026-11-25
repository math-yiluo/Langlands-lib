/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.CoherentFormalModule
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Mathlib.RingTheory.AdicCompletion.Basic
public import WeilConjectures.Mathlib.AlgebraicGeometry.Noetherian
import WeilConjectures.AlgebraicGeometry.GrothendieckExistenceMaximalFailure
import WeilConjectures.AlgebraicGeometry.GrothendieckExistenceProperComparison
import WeilConjectures.AlgebraicGeometry.GrothendieckExistenceDevissage

/-! # Grothendieck existence for proper schemes

Source: Stacks Project, Cohomology of Schemes, Proposition 088C; EGA III_1, Theorem 5.1.4
(blueprint: prop-weil-pbc-grothendieck-existence-proper).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- Completion of coherent modules on a proper scheme over an I-adically complete
Noetherian ring is an equivalence. The kernel ideal of Spec(A/I) → Spec(A) is the ideal
sheaf associated to I; its `comap f` is I O_X. The Noetherian structure on X is supplied
by `isNoetherian_of_locallyOfFiniteType f`, rather than an additional hypothesis.
Source: Stacks Project, Proposition 088C; EGA III_1, Theorem 5.1.4
(blueprint: prop-weil-pbc-grothendieck-existence-proper).

Proof:
1. Properness and the Noetherian base make X Noetherian
   (lem-weil-pbc-finite-type-over-noetherian). Completion is fully faithful by
   lem-weil-pbc-formal-completion-fully-faithful-proper.
2. If essential surjectivity fails, Noetherian ACC gives a maximal quasi-coherent ideal
   for which algebraization fails. Replace X by its closed subscheme; it is nonempty,
   and every strictly larger ideal algebraizes (lem-weil-pbc-noetherian-acc-quasi-coherent,
   lem-weil-pbc-closed-immersion-coherent-equivalence).
3. Every nonzero ideal on this replacement cuts out a subscheme on which completion is
   an equivalence: maximality gives essential surjectivity and properness gives full
   faithfulness. Equal-ideal closed immersions identify the corresponding subschemes
   (lem-weil-pbc-closed-immersions-equal-ideal-isomorphic).
4. Chow's lemma gives a proper surjective projective modification, an isomorphism over
   a dense open (theorem-chow-s-lemma-projective-form). The immersion into projective space is
   closed by properness (lem-weil-pbc-proper-over-separated,
   lem-weil-pbc-immersion-closed-image-closed-immersion).
5. Pull back the formal system and algebraize it on that projective scheme
   (lem-weil-pbc-formal-systems-pullback, lem-weil-pbc-grothendieck-existence-projective).
6. Push forward the resulting coherent module. The push-pull comparison has kernel
   and cokernel killed by a power of the ideal of the reduced closed complement
   (lem-weil-pbc-formal-systems-push-pull).
7. Every positive power of this complement ideal is nonzero: on the nonempty dense
   open it is the unit ideal. Thus step 3 applies to all its thickenings.
8. Devissage algebraizes the original system, contradicting maximality
   (lem-weil-pbc-grothendieck-existence-devissage). Essential surjectivity and step 1
   give the claimed equivalence. -/
theorem grothendieck_existence_proper (A : Type u) [CommRing A] [IsNoetherianRing A]
    (I : Ideal A) [IsAdicComplete I A] (X : Scheme.{u})
    (f : X ⟶ Spec (CommRingCat.of A)) [IsProper f] :
    (@completion X (isNoetherian_of_locallyOfFiniteType f)
      ((Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))).ker.comap f)).IsEquivalence := by
  classical
  by_contra hbad
  obtain ⟨Z, j, hj, hp, hZ, hn, M, hM, hquot⟩ :=
    proper_existence_maximal_failure A I X f hbad
  let := hj
  let := hp
  let := hZ
  let := hn
  let J := (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))).ker.comap (j ≫ f)
  obtain ⟨K, hK, H, α, htorsion⟩ := proper_existence_comparison A I (j ≫ f) M
  have hthick : ∀ e : ℕ, 1 ≤ e → ∀ hW : IsNoetherian (K ^ e).subscheme,
      (@completion (K ^ e).subscheme hW (J.comap (K ^ e).subschemeι)).IsEquivalence := by
    intro e he hW
    exact hquot (K ^ e) (hK e he) hW
  exact hM (grothendieck_existence_devissage J K M hthick H α htorsion)

end AlgebraicGeometry
