/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.EtaleSheaves
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
import WeilConjectures.AlgebraicGeometry.EtaleLissePartitionReducible
import WeilConjectures.AlgebraicGeometry.EtaleGenericLisseStratum

/-!
# Constructibility from generic lissity on integral affine subschemes

Source: finite pushforward constructibility blueprint, steps 2 and 3;
Stacks Project, Tags 095E and 005L.
(blueprint: lem-weil-pbc-constructible-etale-noetherian-criterion).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

private def emptyLissePartition {X : Scheme.{u}}
    (F : Sheaf X.smallEtaleTopology (Type (u + 1))) : EtaleLissePartition F ∅ where
  n := 0
  domain := Fin.elim0
  immersion := fun i ↦ Fin.elim0 i
  isImmersion := fun i ↦ Fin.elim0 i
  covers := by simp
  disjoint := by intro i; exact Fin.elim0 i
  lisse := fun i ↦ Fin.elim0 i

private def adjoinLisseStratum {X : Scheme.{u}}
    (F : Sheaf X.smallEtaleTopology (Type (u + 1)))
    (T Z : Set X) (hZT : Z ⊆ T) (P : EtaleLissePartition F Z)
    (S : Scheme.{u}) (g : S ⟶ X) (hg : IsImmersion g)
    (hrange : Set.range g = T \ Z)
    (hlisse : IsLisseEtaleSheafOfSets ((etaleSetPullback g).obj F)) :
    EtaleLissePartition F T := by
  let D : Fin (P.n + 1) → Scheme.{u} := Fin.cases S P.domain
  let m : ∀ i, D i ⟶ X := Fin.cases g P.immersion
  have hpart (i : Fin P.n) : Set.range (P.immersion i) ⊆ Z := by
    intro x hx
    have h : x ∈ ⋃ j, Set.range (P.immersion j) := Set.mem_iUnion.mpr ⟨i, hx⟩
    simpa only [P.covers] using h
  have hdisj (i : Fin P.n) : Disjoint (Set.range g) (Set.range (P.immersion i)) := by
    rw [hrange]
    exact Set.disjoint_left.mpr (fun x hx hy ↦ hx.2 (hpart i hy))
  refine ⟨P.n + 1, D, m, ?_, ?_, ?_, ?_⟩
  · exact Fin.cases hg P.isImmersion
  · have hu : (⋃ i, Set.range (m i)) =
        Set.range g ∪ (⋃ i, Set.range (P.immersion i)) := by
      ext x
      simp only [Set.mem_iUnion, Set.mem_union]
      constructor
      · rintro ⟨i, hi⟩
        cases i using Fin.cases with
        | zero => exact Or.inl hi
        | succ i => exact Or.inr ⟨i, hi⟩
      · rintro (h | ⟨i, hi⟩)
        · exact ⟨0, h⟩
        · exact ⟨i.succ, hi⟩
    rw [hu, P.covers, hrange]
    exact Set.sdiff_union_of_subset hZT
  · intro i j hij
    cases i using Fin.cases with
    | zero =>
      cases j using Fin.cases with
      | zero => exact (hij rfl).elim
      | succ j => exact hdisj j
    | succ i =>
      cases j using Fin.cases with
      | zero => exact (hdisj i).symm
      | succ j => exact P.disjoint (fun h ↦ hij (congrArg Fin.succ h))
  · exact Fin.cases hlisse P.lisse

/-- On a Noetherian scheme, generic lissity on every integral affine locally closed
subscheme gives a finite constructible lisse stratification. The hypothesis concerns
restrictions of an arbitrary set sheaf and makes no claim about finite direct images.

Source: blueprint `lemma-detection-proper-direct-image--1`, steps 2--3;
Stacks Project, Tags 095E and 005L.
(blueprint: lem-weil-pbc-constructible-etale-noetherian-criterion).

Proof: Use Noetherian induction on closed subsets T of X, endowed with their reduced
induced scheme structure, to partition the restriction of F into finitely many lisse
locally closed subschemes. For the empty subset choose the empty partition. If T is
reducible, its finitely many irreducible components are proper closed subsets. Apply
induction to each component. Subtract the union of earlier components from each of its
strata. These differences remain locally closed and lisse, are pairwise disjoint, and
cover T. If T is irreducible and nonempty, its reduced scheme is integral. Choose a
nonempty affine open S in it. Its composite immersion into X satisfies the hypothesis;
the supplied dense open W of S is also a dense open of T. Its sheaf is lisse by the
hypothesis and the composition isomorphism for inverse images. Its complement is a
proper closed subset of T, so adjoin W to the partition supplied by induction there.
The induction terminates because the topology of X is Noetherian, without a dimension
bound. At T = X with its reduced structure, compose all stratum immersions into X;
their images partition X. Each image is constructible by Noetherianity (Tag 005L).
Composition of inverse images identifies the restrictions with the lisse sheaves just
constructed, giving the required Stratification witness (Tag 095E). Restriction of a
lisse sheaf to an open stays lisse: restrict a trivializing etale cover and use the
unchanged geometric stalks. This justifies the differences in the reducible case. -/
theorem isConstructibleEtaleSheafOfSets_of_generic_lisse
    (X : Scheme.{u}) [IsNoetherian X]
    (F : Sheaf X.smallEtaleTopology (Type (u + 1)))
    (hF : ∀ (S : Scheme.{u}) [IsIntegral S] [IsNoetherian S] [IsAffine S]
      (g : S ⟶ X) [IsImmersion g],
      ∃ W : S.Opens, Dense (W : Set S) ∧
        IsLisseEtaleSheafOfSets
          ((etaleSetPullback W.ι).obj ((etaleSetPullback g).obj F))) :
    IsConstructibleEtaleSheafOfSets F := by
  have hpartition (T : TopologicalSpace.Closeds X) :
      Nonempty (EtaleLissePartition F (T : Set X)) := by
    induction T using WellFoundedLT.induction with
    | _ T ih =>
      by_cases hne : (T : Set X).Nonempty
      · by_cases hirr : IsIrreducible (T : Set X)
        · obtain ⟨Z, hZT, S, g, hg, hrange, hlisse⟩ :=
            exists_etaleGenericLisseStratum F hF T hirr
          obtain ⟨P⟩ := ih Z hZT
          exact ⟨adjoinLisseStratum F T Z (le_of_lt hZT) P S g hg hrange hlisse⟩
        · exact nonempty_etaleLissePartition_of_reducible F T hne hirr ih
      · have hT : (T : Set X) = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
        rw [hT]
        exact ⟨emptyLissePartition F⟩
  obtain ⟨P⟩ := hpartition ⊤
  let (i : Fin P.n) : IsImmersion (P.immersion i) := P.isImmersion i
  refine ⟨Stratification.ofNoetherianSpace P.n
    (fun i ↦ Set.range (P.immersion i)) (fun i ↦ (P.immersion i).isLocallyClosed_range)
    P.covers P.disjoint P.domain P.immersion P.isImmersion (fun _ ↦ rfl), ?_⟩
  exact P.lisse

end AlgebraicGeometry.Scheme
