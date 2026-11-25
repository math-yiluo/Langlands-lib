/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.CoherentFormalModule
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import WeilConjectures.Mathlib.AlgebraicGeometry.Noetherian
import WeilConjectures.AlgebraicGeometry.ClosedImmersionCoherentEquivalence
import WeilConjectures.AlgebraicGeometry.ClosedSubsetProperOverBaseUnionPreimage
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial

/-! # Presentation of a formal module on its closed quotient

Source: Stacks Project, Theorem 088E, first reduction to a closed subscheme.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- Descend a system killed by K to V(K), retaining its first support and the
termwise pushforward identification. The lack of a proper closed support implies
that V(K) is nonempty.

Source: Stacks Project, Theorem 088E, paragraphs 2--4, and Tag 087T.
(blueprint: lem-weil-pbc-closed-quotient-formal-presentation).

Proof: K.subschemeι is a closed immersion with kernel K. The closed-immersion
coherent-formal equivalence is essentially surjective onto systems killed by K;
apply it to M. Its comparison with termwise pushforward gives the displayed
isomorphism. At points in V(K), closed pushforward has the same stalk as the
original module, and outside V(K) its stalk is zero. Thus the first supports,
with reduced closed subscheme structures, are identified and properness descends.
If V(K) were empty, its closed immersion into X would be proper over any base
(the empty morphism is proper), and its kernel K already kills M. This contradicts
the hypothesis forbidding a proper closed support. No comparison map or enlarged
annihilator is obtained at this step. -/
theorem exists_closedQuotientFormalPresentation
    {X S : Scheme.{u}} [IsNoetherian X] (f : X ⟶ S)
    [LocallyOfFiniteType f]
    (Q K : X.IdealSheafData) (M : CoherentFormalModule X Q)
    (hK : AnnihilatedBy Q K M)
    (hR : Scheme.Modules.HasSupportProperOver f (M.obj.obj (op 0)))
    (hP : ¬ ∃ (Z : Scheme.{u}) (j : Z ⟶ X) (_ : IsClosedImmersion j),
      IsProper (j ≫ f) ∧ AnnihilatedBy Q j.ker M) :
    ∃ G : @CoherentFormalModule K.subscheme
        (isNoetherian_of_locallyOfFiniteType K.subschemeι) (Q.comap K.subschemeι),
      Nonempty (M.obj ≅ G.obj ⋙ Scheme.Modules.pushforward K.subschemeι) ∧
      Scheme.Modules.HasSupportProperOver (K.subschemeι ≫ f) (G.obj.obj (op 0)) ∧
      Nonempty K.subscheme := by
  classical
  let j := K.subschemeι
  let : IsNoetherian K.subscheme := isNoetherian_of_locallyOfFiniteType j
  have hM : SupportedOn Q M j := by
    simpa only [SupportedOn, j, Scheme.IdealSheafData.ker_subschemeι] using hK
  obtain ⟨⟨E, ⟨β⟩⟩, _⟩ := closedImmersion_coherentFormal_equivalence j Q
  let G := E.inverse.obj ⟨M, hM⟩
  let e : M.obj ≅ G.obj ⋙ Scheme.Modules.pushforward j :=
    ((ObjectProperty.ι (fun M : CoherentFormalModule X Q ↦ SupportedOn Q M j) ⋙
      ObjectProperty.ι (IsCoherentFormalModule Q)).mapIso
        (E.counitIso.app ⟨M, hM⟩)).symm ≪≫ β.app G
  have hsupport : {x : X | ¬ Subsingleton ((M.obj.obj (op 0)).presheaf.stalk x)} =
      j '' {z : K.subscheme | ¬ Subsingleton ((G.obj.obj (op 0)).presheaf.stalk z)} := by
    rw [← closedImmersion_coherent_support j ⟨G.obj.obj (op 0), G.property.1 0⟩]
    ext x
    let T := SheafOfModules.forget X.ringCatSheaf ⋙
      PresheafOfModules.toPresheaf X.ringCatSheaf.obj ⋙
        TopCat.Presheaf.stalkFunctor Ab.{u} x
    have eb := ConcreteCategory.bijective_of_isIso (T.map (e.app (op 0)).hom)
    apply not_congr
    constructor
    · intro h
      exact ⟨fun a b ↦ by
        obtain ⟨a', rfl⟩ := eb.2 a
        obtain ⟨b', rfl⟩ := eb.2 b
        exact congrArg (ConcreteCategory.hom (T.map (e.app (op 0)).hom)) (h.elim a' b')⟩
    · intro h
      exact ⟨fun a b ↦ eb.1 (h.elim _ _)⟩
  obtain ⟨R, hR, hp⟩ := hR
  have hpre : (R.preimage (f := j.base) j.continuous : Set K.subscheme) =
      {z : K.subscheme | ¬ Subsingleton ((G.obj.obj (op 0)).presheaf.stalk z)} := by
    ext z
    change j z ∈ (R : Set X) ↔ _
    rw [hR, hsupport]
    exact j.isClosedEmbedding.injective.mem_set_image
  have hpG := (Scheme.isClosedSubsetProperOver_union_preimage (j ≫ f)).2
    j f rfl R hp
  have hZ : Nonempty K.subscheme := by
    by_contra hn
    let : IsEmpty K.subscheme := not_nonempty_iff.mp hn
    exact hP ⟨K.subscheme, j, inferInstance, inferInstance, hM⟩
  exact ⟨G, ⟨e⟩, ⟨R.preimage (f := j.base) j.continuous, hpre, hpG⟩, hZ⟩

end AlgebraicGeometry
