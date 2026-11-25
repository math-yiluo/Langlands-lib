/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.EtaleLissePartition
public import Mathlib.AlgebraicGeometry.Noetherian
import WeilConjectures.AlgebraicGeometry.EtaleLocallyConstantOpenPullback
import WeilConjectures.AlgebraicGeometry.EtaleSetInverseImageStalkGerm
import WeilConjectures.AlgebraicGeometry.EtaleSetInverseImageCompositionUnits
import WeilConjectures.AlgebraicGeometry.FundamentalGroup.FiniteStalksComparison

/-!
# The reducible step for finite lisse partitions

Source: finite pushforward constructibility blueprint, step 2.
(blueprint: lem-weil-pbc-etale-lisse-partition-reducible).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

private lemma lisse_open_comp {X Y : Scheme.{u}}
    (F : Sheaf X.smallEtaleTopology (Type (u + 1))) (g : Y ⟶ X) (U : Y.Opens)
    (hF : IsLisseEtaleSheafOfSets ((etaleSetPullback g).obj F)) :
    IsLisseEtaleSheafOfSets ((etaleSetPullback (U.ι ≫ g)).obj F) := by
  have hopen : IsLisseEtaleSheafOfSets
      ((etaleSetPullback U.ι).obj ((etaleSetPullback g).obj F)) := by
    refine ⟨isLocallyConstantEtaleSheafOfSets_open_pullback _ U hF.1, ?_⟩
    refine isFiniteSheaf_of_finite_algClosed_stalks _ fun Ω _ _ s ↦ ?_
    obtain ⟨c, hc, _⟩ := etaleSetInverseImageStalkGerm Y U U.ι
      ((etaleSetPullback g).obj F) Ω s
    have := hF.finite_sheafFiber Ω (s ≫ U.ι)
    exact Finite.of_injective c hc.1
  obtain ⟨c, _⟩ := etaleSetInverseImageCompositionUnits.2.2
  have transport : ∀ {V : Scheme.{u}}
      {G H : Sheaf V.smallEtaleTopology (Type (u + 1))}, (G ≅ H) →
      IsLisseEtaleSheafOfSets G → IsLisseEtaleSheafOfSets H := by
    intro V G H e hG
    obtain ⟨⟨𝒰, h𝒰⟩, hfin⟩ := hG
    refine ⟨⟨𝒰, fun i ↦ ?_⟩, ?_⟩
    · have := h𝒰 i
      exact Sheaf.isConstant_congr _
        ((V.smallEtaleTopology.overPullback (Type (u + 1))
          (𝒰.etalePrecoverageToEtale i)).mapIso e)
    · refine isFiniteSheaf_of_finite_algClosed_stalks _ fun Ω _ _ s ↦ ?_
      have := (ConcreteCategory.isFinitelyGenerated_iff_finite _).mp
        (hfin.isFinitelyGenerated_sheafFiber Ω s)
      exact Finite.of_equiv _
        (((pointSmallEtale s).sheafFiber (A := Type (u + 1))).mapIso e).toEquiv
  exact transport ((c X Y U g U.ι).app F) hopen

private def subtractClosed {X : Scheme.{u}}
    (F : Sheaf X.smallEtaleTopology (Type (u + 1))) {T : Set X}
    (P : EtaleLissePartition F T) (Z : TopologicalSpace.Closeds X) :
    EtaleLissePartition F (T \ (Z : Set X)) := by
  let U (i : Fin P.n) : (P.domain i).Opens :=
    ⟨P.immersion i ⁻¹' (Z : Set X)ᶜ,
      Z.isClosed.isOpen_compl.preimage (P.immersion i).continuous⟩
  let g (i : Fin P.n) : (U i : Scheme) ⟶ X := (U i).ι ≫ P.immersion i
  have hrange (i : Fin P.n) :
      Set.range (g i) = Set.range (P.immersion i) \ (Z : Set X) := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨⟨(U i).ι y, rfl⟩, y.property⟩
    · rintro ⟨⟨y, rfl⟩, hy⟩
      exact ⟨⟨y, hy⟩, rfl⟩
  refine ⟨P.n, (fun i ↦ (U i : Scheme)), g, ?_, ?_, ?_, ?_⟩
  · intro i
    let := P.isImmersion i
    exact inferInstance
  · simp only [hrange]
    rw [← Set.iUnion_sdiff, P.covers]
  · intro i j hij
    rw [hrange, hrange]
    exact (P.disjoint hij).mono Set.sdiff_subset Set.sdiff_subset
  · intro i
    exact lisse_open_comp F (P.immersion i) (U i) (P.lisse i)

private def unionDisjoint {X : Scheme.{u}}
    (F : Sheaf X.smallEtaleTopology (Type (u + 1))) {A B : Set X}
    (P : EtaleLissePartition F A) (Q : EtaleLissePartition F B)
    (hAB : Disjoint A B) : EtaleLissePartition F (A ∪ B) := by
  let S : Fin (P.n + Q.n) → Σ Y : Scheme.{u}, Y ⟶ X :=
    Fin.append (fun i ↦ ⟨P.domain i, P.immersion i⟩)
      (fun i ↦ ⟨Q.domain i, Q.immersion i⟩)
  let D : Fin (P.n + Q.n) → Scheme.{u} := fun i ↦ (S i).1
  let m : ∀ i, D i ⟶ X := fun i ↦ (S i).2
  have sP (i : Fin P.n) : S (i.castAdd Q.n) = ⟨P.domain i, P.immersion i⟩ :=
    Fin.append_left _ _ i
  have sQ (i : Fin Q.n) : S (i.natAdd P.n) = ⟨Q.domain i, Q.immersion i⟩ :=
    Fin.append_right _ _ i
  have rP (i : Fin P.n) : Set.range (m (i.castAdd Q.n)) =
      Set.range (P.immersion i) :=
    congrArg (fun t : Σ Y : Scheme.{u}, Y ⟶ X ↦ Set.range t.2) (sP i)
  have rQ (i : Fin Q.n) : Set.range (m (i.natAdd P.n)) =
      Set.range (Q.immersion i) :=
    congrArg (fun t : Σ Y : Scheme.{u}, Y ⟶ X ↦ Set.range t.2) (sQ i)
  have hP (i : Fin P.n) : Set.range (P.immersion i) ⊆ A := by
    intro x hx
    rw [← P.covers]
    exact Set.mem_iUnion.mpr ⟨i, hx⟩
  have hQ (i : Fin Q.n) : Set.range (Q.immersion i) ⊆ B := by
    intro x hx
    rw [← Q.covers]
    exact Set.mem_iUnion.mpr ⟨i, hx⟩
  refine ⟨P.n + Q.n, D, m, ?_, ?_, ?_, ?_⟩
  · intro i
    cases i using Fin.addCases with
    | left i =>
      change (fun t : Σ Y : Scheme.{u}, Y ⟶ X ↦ IsImmersion t.2) (S _)
      rw [sP]
      exact P.isImmersion i
    | right i =>
      change (fun t : Σ Y : Scheme.{u}, Y ⟶ X ↦ IsImmersion t.2) (S _)
      rw [sQ]
      exact Q.isImmersion i
  · have hu : (⋃ i, Set.range (m i)) =
        (⋃ i, Set.range (P.immersion i)) ∪ (⋃ i, Set.range (Q.immersion i)) := by
      ext x
      simp only [Set.mem_iUnion, Set.mem_union]
      constructor
      · rintro ⟨i, hi⟩
        cases i using Fin.addCases with
        | left i => exact Or.inl ⟨i, by simpa [rP, rQ] using hi⟩
        | right i => exact Or.inr ⟨i, by simpa [rP, rQ] using hi⟩
      · rintro (⟨i, hi⟩ | ⟨i, hi⟩)
        · exact ⟨i.castAdd Q.n, by simpa [rP, rQ] using hi⟩
        · exact ⟨i.natAdd P.n, by simpa [rP, rQ] using hi⟩
    rw [hu, P.covers, Q.covers]
  · intro i j hij
    cases i using Fin.addCases with
    | left i =>
      cases j using Fin.addCases with
      | left j => simpa [rP, rQ] using P.disjoint (fun h ↦ hij (congrArg (Fin.castAdd Q.n) h))
      | right j => simpa [rP, rQ] using hAB.mono (hP i) (hQ j)
    | right i =>
      cases j using Fin.addCases with
      | left j => simpa [rP, rQ] using hAB.symm.mono (hQ i) (hP j)
      | right j => simpa [rP, rQ] using Q.disjoint (fun h ↦ hij (congrArg (Fin.natAdd P.n) h))
  · intro i
    cases i using Fin.addCases with
    | left i =>
      change (fun t : Σ Y : Scheme.{u}, Y ⟶ X ↦
        IsLisseEtaleSheafOfSets ((etaleSetPullback t.2).obj F)) (S _)
      rw [sP]
      exact P.lisse i
    | right i =>
      change (fun t : Σ Y : Scheme.{u}, Y ⟶ X ↦
        IsLisseEtaleSheafOfSets ((etaleSetPullback t.2).obj F)) (S _)
      rw [sQ]
      exact Q.lisse i

/-- The reducible Noetherian induction step only uses partitions on proper closed subsets;
it does not require the generic-lissity hypothesis.

Source: blueprint `lemma-detection-proper-direct-image--1`, step 2.
(blueprint: lem-weil-pbc-etale-lisse-partition-reducible).

Proof: The nonempty closed subset T has finitely many irreducible components, by
Noetherianity of the closed subspace. List them as T_1,...,T_r. Because T is not
irreducible, every component is a proper closed subset of T. Apply the given hypothesis
to each component. For each stratum in component i, take the inverse image of the
complement of the closed subset T_1 union ... union T_{i-1}. This is an open subscheme
of the stratum; compose its open immersion with the old stratum immersion. Composition
preserves immersions. The images are the old images minus the earlier components,
so the resulting finite list is disjoint and covers T. Pullback composition identifies
the new sheaf with the open restriction of the old lisse sheaf. Restrict an etale
trivializing cover; the restriction comparison and the constant-sheaf pullback comparison
show local constancy, and the inverse-image geometric-stalk bijection shows finiteness.
Thus every new stratum is lisse. Empty differences can be kept as empty strata. -/
theorem nonempty_etaleLissePartition_of_reducible
    {X : Scheme.{u}} [IsNoetherian X]
    (F : Sheaf X.smallEtaleTopology (Type (u + 1)))
    (T : TopologicalSpace.Closeds X) (hne : (T : Set X).Nonempty)
    (hred : ¬ IsIrreducible (T : Set X))
    (ih : ∀ Z : TopologicalSpace.Closeds X, Z < T →
      Nonempty (EtaleLissePartition F (Z : Set X))) :
    Nonempty (EtaleLissePartition F (T : Set X)) := by
  classical
  have hpre : ¬ IsPreirreducible (T : Set X) := fun h ↦ hred ⟨hne, h⟩
  rw [isPreirreducible_iff_isClosed_union_isClosed] at hpre
  push Not at hpre
  obtain ⟨A, B, hA, hB, hcover, hTA, hTB⟩ := hpre
  let Z : TopologicalSpace.Closeds X := ⟨(T : Set X) ∩ A, T.isClosed.inter hA⟩
  let W : TopologicalSpace.Closeds X := ⟨(T : Set X) ∩ B, T.isClosed.inter hB⟩
  have hZT : Z < T := by
    refine lt_of_le_of_ne Set.inter_subset_left ?_
    intro heq
    apply hTA
    rw [← heq]
    exact Set.inter_subset_right
  have hWT : W < T := by
    refine lt_of_le_of_ne Set.inter_subset_left ?_
    intro heq
    apply hTB
    rw [← heq]
    exact Set.inter_subset_right
  obtain ⟨P⟩ := ih Z hZT
  obtain ⟨Q⟩ := ih W hWT
  have hdisj : Disjoint (Z : Set X) ((W : Set X) \ (Z : Set X)) :=
    Set.disjoint_sdiff_right
  have heq : (Z : Set X) ∪ ((W : Set X) \ (Z : Set X)) = (T : Set X) := by
    ext x
    constructor
    · rintro (hx | hx)
      · exact hx.1
      · exact hx.1.1
    · intro hx
      by_cases hxA : x ∈ A
      · exact Or.inl ⟨hx, hxA⟩
      · exact Or.inr ⟨⟨hx, (hcover hx).resolve_left hxA⟩, fun hz ↦ hxA hz.2⟩
  rw [← heq]
  exact ⟨unionDisjoint F P (subtractClosed F Q Z) hdisj⟩

end AlgebraicGeometry.Scheme
