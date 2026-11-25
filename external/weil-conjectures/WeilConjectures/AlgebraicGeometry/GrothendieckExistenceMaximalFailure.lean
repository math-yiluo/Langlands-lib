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
import WeilConjectures.AlgebraicGeometry.NoetherianQuasicoherentSubmodules
import WeilConjectures.AlgebraicGeometry.FormalCompletionFullyFaithfulProper
import WeilConjectures.AlgebraicGeometry.GrothendieckExistenceProjective
import WeilConjectures.AlgebraicGeometry.ClosedImmersionCoherentEquivalence
import WeilConjectures.AlgebraicGeometry.ModulePullbackIdealQuotient

/-! # A maximal closed counterexample to proper algebraization

Source: Stacks Project, Proposition 088C, first two paragraphs of the proof.
(blueprint: lem-weil-pbc-proper-existence-maximal-failure).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- Failure of proper existence reduces to a nonempty closed subscheme on which
algebraization fails, but completion on every nonzero closed quotient is an equivalence.
Source: Stacks Project, Proposition 088C, first two paragraphs of the proof.
(blueprint: lem-weil-pbc-proper-existence-maximal-failure).

Proof:
1. Identify the kernel ideal of Spec(A/I) with the ideal sheaf of I, using the
Gamma-Spec naturality square and ker(A -> A/I) = I. Proper full faithfulness then
turns failure of equivalence into an object outside the essential image.
2. Consider the set of kernels of closed immersions j:Z -> X for which completion
on Z is not an equivalence. The identity immersion shows that this set is nonempty.
Apply Noetherian ACC to choose a maximal kernel L, retaining an immersion j with
kernel L and failing completion. Properness supplies Noetherianity on X and Z.
3. Z cannot be empty: an empty scheme embeds into projective space of dimension zero.
Its structural map is j followed by f, by uniqueness of maps from the empty scheme.
Projective existence would make its completion an equivalence, a contradiction.
Proper full faithfulness supplies a formal module M outside the essential image on Z.
4. For a nonzero ideal K on Z, the composite V(K) -> Z -> X has kernel containing L.
Equality would make V(K) -> Z an isomorphism by the closed-immersion ideal correspondence,
forcing K = 0. Thus the kernel strictly contains L. If its completion failed, this
kernel would belong to the failing set, contradicting maximality. Ideal comap composition
identifies its completion ideal with the one in the conclusion. Noetherian witnesses
are propositions, so this argument holds for every such witness on V(K). -/
theorem proper_existence_maximal_failure
    (A : Type u) [CommRing A] [IsNoetherianRing A]
    (I : Ideal A) [IsAdicComplete I A] (X : Scheme.{u})
    (f : X ⟶ Spec (CommRingCat.of A)) [IsProper f]
    (hbad : ¬ (@completion X (isNoetherian_of_locallyOfFiniteType f)
      ((Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))).ker.comap f)).IsEquivalence) :
    ∃ (Z : Scheme.{u}) (j : Z ⟶ X) (_ : IsClosedImmersion j)
      (_ : IsProper (j ≫ f)) (hZ : IsNoetherian Z) (_ : Nonempty Z),
      let J := (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))).ker.comap (j ≫ f)
      ∃ M : @CoherentFormalModule Z hZ J,
        (¬ ∃ F : CoherentModules Z, Nonempty ((@completion Z hZ J).obj F ≅ M)) ∧
        ∀ (K : Z.IdealSheafData), K ≠ ⊥ → ∀ (hW : IsNoetherian K.subscheme),
          (@completion K.subscheme hW (J.comap K.subschemeι)).IsEquivalence := by
  classical
  let hX := isNoetherian_of_locallyOfFiniteType f
  let B := Spec (CommRingCat.of A)
  let Q := (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))).ker
  have hQ : Q = Scheme.IdealSheafData.ofIdealTop
      (I.map (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom) := by
    dsimp only [Q]
    rw [Scheme.ker_of_isAffine]
    congr 1
    rw [← RingHom.ker_equiv_comp _
      (Scheme.ΓSpecIso (CommRingCat.of (A ⧸ I))).commRingCatIsoToRingEquiv]
    change RingHom.ker ((Spec.map (CommRingCat.ofHom
      (Ideal.Quotient.mk I))).appTop ≫
      (Scheme.ΓSpecIso (CommRingCat.of (A ⧸ I))).hom).hom = _
    rw [Scheme.ΓSpecIso_naturality, CommRingCat.hom_comp, ← RingHom.comap_ker]
    change (RingHom.ker (Ideal.Quotient.mk I)).comap _ = _
    rw [Ideal.mk_ker]
    exact (Ideal.map_comap_of_equiv
      (Scheme.ΓSpecIso (CommRingCat.of A)).symm.commRingCatIsoToRingEquiv).symm
  have failure (Z : Scheme.{u}) (g : Z ⟶ B) (hg : IsProper g)
      (hb : ¬ (@completion Z (isNoetherian_of_locallyOfFiniteType g)
        (Q.comap g)).IsEquivalence) :
      ∃ M : @CoherentFormalModule Z (isNoetherian_of_locallyOfFiniteType g) (Q.comap g),
        ¬ ∃ F : CoherentModules Z,
          Nonempty ((@completion Z (isNoetherian_of_locallyOfFiniteType g)
            (Q.comap g)).obj F ≅ M) := by
    let C := @completion Z (isNoetherian_of_locallyOfFiniteType g) (Q.comap g)
    have hbij (G F : CoherentModules Z) : Function.Bijective (C.map (X := G) (Y := F)) := by
      dsimp only [C]
      rw [hQ]
      exact formalCompletion_map_bijective_of_proper I g G F
    obtain ⟨hff⟩ := (Functor.FullyFaithful.nonempty_iff_map_bijective C).mpr hbij
    by_contra he
    push Not at he
    exact hb { faithful := hff.faithful, full := hff.full, essSurj := ⟨he⟩ }
  obtain ⟨M₀, _⟩ := failure X f inferInstance hbad
  let S : Set X.IdealSheafData := {L | ∃ (Z : Scheme.{u}) (j : Z ⟶ X)
    (hj : IsClosedImmersion j) (hp : IsProper (j ≫ f)),
    j.ker = L ∧ ¬ (@completion Z (isNoetherian_of_locallyOfFiniteType (j ≫ f))
      (Q.comap (j ≫ f))).IsEquivalence}
  have hS : S.Nonempty := by
    refine ⟨Scheme.Hom.ker (𝟙 X), X, 𝟙 X, inferInstance, inferInstance, rfl, ?_⟩
    change ¬ (@completion X hX (Q.comap (𝟙 X ≫ f))).IsEquivalence
    rw [Category.id_comp]
    exact hbad
  obtain ⟨L, hL, hmax⟩ :=
    (noetherian_quasicoherent_submodules X (M₀.obj.obj (Opposite.op 0))
      (M₀.property.1 0)).2.2 S hS
  obtain ⟨Z, j, hj, hp, hker, hb⟩ := hL
  let hZ := isNoetherian_of_locallyOfFiniteType (j ≫ f)
  have hn : Nonempty Z := by
    by_contra he
    have : IsEmpty Z := not_nonempty_iff.mp he
    let P := ProjectiveSpace (ULift.{u} (Fin (0 + 1))) B
    let i : Z ⟶ P := (isInitialOfIsEmpty (X := Z)).to P
    have hi : IsClosedImmersion i := inferInstance
    have hcomp : i ≫ (P ↘ B) = j ≫ f := (isInitialOfIsEmpty (X := Z)).hom_ext _ _
    have heq := completion_isEquivalence_of_projective_embedding A I Z 0 i
    change (@completion Z hZ (Q.comap (i ≫ (P ↘ B)))).IsEquivalence at heq
    rw [hcomp] at heq
    exact hb heq
  obtain ⟨M, hM⟩ := failure Z (j ≫ f) hp hb
  refine ⟨Z, j, hj, hp, hZ, hn, M, hM, ?_⟩
  intro K hK hW
  have hproper : IsProper ((K.subschemeι ≫ j) ≫ f) := inferInstance
  have hstrict : j.ker < (K.subschemeι ≫ j).ker := by
    refine lt_of_le_of_ne (K.subschemeι.le_ker_comp j) ?_
    intro heq
    have : IsIso K.subschemeι := IsClosedImmersion.isIso_of_ker_eq
      (K.subschemeι ≫ j) j K.subschemeι rfl heq.symm
    exact hK (K.ker_subschemeι.symm.trans K.subschemeι.ker_eq_bot_of_isIso)
  by_contra hnq
  have hmem : (K.subschemeι ≫ j).ker ∈ S := by
    refine ⟨K.subscheme, K.subschemeι ≫ j, inferInstance, hproper, rfl, ?_⟩
    change ¬ (@completion K.subscheme hW
      (Q.comap ((K.subschemeι ≫ j) ≫ f))).IsEquivalence
    rw [Category.assoc, Scheme.IdealSheafData.comap_comp]
    exact hnq
  have heq := hmax (K.subschemeι ≫ j).ker hmem (hker ▸ hstrict.le)
  exact (ne_of_gt hstrict) (heq.trans hker.symm)

end AlgebraicGeometry
