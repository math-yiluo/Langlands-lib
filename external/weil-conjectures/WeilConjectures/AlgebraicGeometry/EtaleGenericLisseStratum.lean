/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.EtaleSheaves
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
import WeilConjectures.AlgebraicGeometry.EtaleSetInverseImageCompositionUnits
import WeilConjectures.AlgebraicGeometry.FundamentalGroup.FiniteStalksComparison

/-!
# A generic lisse stratum in an irreducible closed subset

Source: finite pushforward constructibility blueprint, step 3.
(blueprint: lem-weil-pbc-etale-generic-lisse-stratum).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

private lemma lisse_of_iso {Y : Scheme.{u}}
    {G H : Sheaf Y.smallEtaleTopology (Type (u + 1))} (e : G ≅ H)
    (hG : IsLisseEtaleSheafOfSets G) : IsLisseEtaleSheafOfSets H := by
  obtain ⟨⟨𝒰, h𝒰⟩, hfin⟩ := hG
  refine ⟨⟨𝒰, fun i ↦ ?_⟩, ?_⟩
  · have := h𝒰 i
    exact Sheaf.isConstant_congr _
      ((Y.smallEtaleTopology.overPullback (Type (u + 1))
        (𝒰.etalePrecoverageToEtale i)).mapIso e)
  · refine isFiniteSheaf_of_finite_algClosed_stalks _ fun Ω _ _ s ↦ ?_
    have := (ConcreteCategory.isFinitelyGenerated_iff_finite _).mp
      (hfin.isFinitelyGenerated_sheafFiber Ω s)
    exact Finite.of_equiv _
      (((pointSmallEtale s).sheafFiber (A := Type (u + 1))).mapIso e).toEquiv

/-- Generic lissity on integral affine immersions supplies one lisse locally closed
stratum in every irreducible closed subset, leaving a proper closed complement.
No partition of that complement is asserted here.

Source: blueprint `lemma-detection-proper-direct-image--1`, step 3;
Stacks Project, Tags 01J3 and 01J4 for the reduced induced scheme.
(blueprint: lem-weil-pbc-etale-generic-lisse-stratum).

Proof: Give T its reduced induced closed scheme structure. Its underlying space is
homeomorphic to T; since T is irreducible and nonempty, this reduced scheme is integral.
It is Noetherian as a closed subscheme of X. Choose an affine open containing one point;
it is nonempty, integral and Noetherian. Compose its open immersion with the closed
immersion into X and apply the generic-lissity hypothesis. The resulting dense open W
is nonempty and is also open in the reduced induced scheme. Its image is relatively
open and dense in T. Let Z be its complement in T. Then Z is closed in X and proper
in T. The composite immersion W into X has image T minus Z. The inverse-image
composition isomorphism identifies its pullback of F with the iterated pullback supplied
by the hypothesis. Local constancy and finite geometric stalks are invariant under
isomorphism of sheaves, so that composite pullback is lisse. -/
theorem exists_etaleGenericLisseStratum
    {X : Scheme.{u}} [IsNoetherian X]
    (F : Sheaf X.smallEtaleTopology (Type (u + 1)))
    (hF : ∀ (S : Scheme.{u}) [IsIntegral S] [IsNoetherian S] [IsAffine S]
      (g : S ⟶ X) [IsImmersion g],
      ∃ W : S.Opens, Dense (W : Set S) ∧
        IsLisseEtaleSheafOfSets
          ((etaleSetPullback W.ι).obj ((etaleSetPullback g).obj F)))
    (T : TopologicalSpace.Closeds X) (hT : IsIrreducible (T : Set X)) :
    ∃ (Z : TopologicalSpace.Closeds X), Z < T ∧
      ∃ (S : Scheme.{u}) (g : S ⟶ X), IsImmersion g ∧
        Set.range g = (T : Set X) \ (Z : Set X) ∧
        IsLisseEtaleSheafOfSets ((etaleSetPullback g).obj F) := by
  classical
  let I := IdealSheafData.vanishingIdeal T
  let Y := I.subscheme
  let j : Y ⟶ X := I.subschemeι
  have hj : Set.range j = (T : Set X) := by
    exact I.range_subschemeι
  have : IrreducibleSpace Y := by
    change IrreducibleSpace (T : Set X)
    exact Subtype.irreducibleSpace hT
  have : IsIntegral Y := isIntegral_of_irreducibleSpace_of_isReduced Y
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian j
  obtain ⟨y⟩ := (inferInstance : Nonempty Y)
  obtain ⟨U, hU, hyU, _⟩ := exists_isAffineOpen_mem_and_subset (x := y) (U := ⊤) trivial
  have : IsAffine U := hU
  have : Nonempty U := ⟨⟨y, hyU⟩⟩
  have : IsIntegral U := isIntegral_of_isOpenImmersion U.ι
  have : IsLocallyNoetherian U := isLocallyNoetherian_of_isOpenImmersion U.ι
  have : IsNoetherian U := ⟨⟩
  obtain ⟨W, hW, hlisse⟩ := hF U (U.ι ≫ j)
  let V : Set Y := U.ι '' (W : Set U)
  have hV : IsOpen V := U.ι.isOpenEmbedding.isOpenMap _ W.isOpen
  let Z : TopologicalSpace.Closeds X :=
    ⟨j '' Vᶜ, j.isClosedEmbedding.isClosedMap _ hV.isClosed_compl⟩
  have hZT : Z < T := by
    refine lt_of_le_of_ne ?_ ?_
    · intro x hx
      obtain ⟨z, _, rfl⟩ := hx
      change j z ∈ (T : Set X)
      rw [← hj]
      exact ⟨z, rfl⟩
    · intro heq
      obtain ⟨w, hw⟩ := hW.nonempty
      have hx : j (U.ι w) ∈ (T : Set X) := by rw [← hj]; exact ⟨_, rfl⟩
      rw [← heq] at hx
      obtain ⟨z, hz, he⟩ := hx
      have he' := j.isClosedEmbedding.injective he
      exact hz (he' ▸ ⟨w, hw, rfl⟩)
  refine ⟨Z, hZT, W, W.ι ≫ U.ι ≫ j, inferInstance, ?_, ?_⟩
  · ext x
    constructor
    · rintro ⟨w, rfl⟩
      refine ⟨?_, ?_⟩
      · rw [← hj]; exact ⟨_, rfl⟩
      · rintro ⟨z, hz, he⟩
        have he' := j.isClosedEmbedding.injective he
        exact hz (he' ▸ ⟨(W.ι w), w.property, rfl⟩)
    · rintro ⟨hx, hxZ⟩
      rw [← hj] at hx
      obtain ⟨z, rfl⟩ := hx
      have hz : z ∈ V := by
        by_contra hz
        exact hxZ ⟨z, hz, rfl⟩
      obtain ⟨w, hw, rfl⟩ := hz
      exact ⟨⟨w, hw⟩, rfl⟩
  · obtain ⟨c, _⟩ := etaleSetInverseImageCompositionUnits.2.2
    exact lisse_of_iso ((c X U W (U.ι ≫ j) W.ι).app F) hlisse

end AlgebraicGeometry.Scheme
