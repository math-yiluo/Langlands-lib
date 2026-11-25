/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.Topology.KrullDimension
public import Mathlib.Topology.JacobsonSpace

/-!
# Coordinate projections lower the dimension of the generic fibre

Let `S` be an integral scheme, `f : X ⟶ S` locally of finite type and `t : X ⟶ 𝔸¹_S` a morphism
over `S` (a coordinate). The generic fibre of `t`, over the generic point of `𝔸¹_S`, has
dimension at most `dim X_K - 1`, where `X_K` is the generic fibre of `f`. This is the dimension
count driving the induction in Deligne's generic constructibility theorem
(`theorem-generic-constructibility-base-change-rj`).

Dimensions are topological Krull dimensions with values in `WithBot ℕ∞`, so an empty fibre has
dimension `⊥` and `⊥ + 1 = ⊥`.

## Main statements

- `AlgebraicGeometry.topologicalKrullDim_fiber_genericPoint_add_one_le`
  (`lemma-coordinate-projections--1`).

## Proof

Every point `x` of the fibre of `t` over the generic point `η'` of `𝔸¹_S` lies in the generic
fibre `X_K` of `f`, which is a Jacobson space; the closure of `x` in `X_K` contains a closed point
`y` of `X_K`. Closed points of `X_K` map to closed points of the fibre `𝔸¹_K` of `𝔸¹_S`, while
`η'` is not closed there, so `y` does not lie over `η'`. Hence every chain of irreducible closed
subsets of the fibre of `t` extends, inside `X_K`, by one more step at its bottom.
-/

@[expose] public section

universe u

open CategoryTheory Limits Order Topology

/-- If `f : α → β` is strictly monotone and every value of `f` has an element strictly below it,
then `dim α + 1 ≤ dim β`. -/
theorem Order.krullDim_add_one_le_of_strictMono {α β : Type*} [Preorder α] [Preorder β]
    (f : α → β) (hf : StrictMono f) (h : ∀ a, ∃ b, b < f a) :
    krullDim α + 1 ≤ krullDim β := by
  rcases isEmpty_or_nonempty α with hα | hα
  · simp [krullDim_eq_bot]
  have key (p : LTSeries α) : ((p.length + 1 : ℕ) : WithBot ℕ∞) ≤ krullDim β := by
    obtain ⟨b, hb⟩ := h p.head
    have := LTSeries.length_le_krullDim ((p.map f hf).cons b (by simpa using hb))
    simpa using this
  have hβ : krullDim β ≠ ⊥ := by
    have := key (RelSeries.singleton _ (Classical.arbitrary α))
    intro h; rw [h] at this; simp at this
  obtain ⟨m, hm⟩ := WithBot.ne_bot_iff_exists.mp hβ
  rw [krullDim_eq_iSup_length, ← hm]
  have : (⨆ p : LTSeries α, (p.length : ℕ∞)) + 1 ≤ m := by
    rw [ENat.iSup_add]
    refine iSup_le fun p ↦ ?_
    have := key p
    rw [← hm] at this
    exact_mod_cast this
  exact_mod_cast this

/-- Let `F ⊆ G` be subsets of a `T₀` space. If every point of `F` has a specialization in `G` which
is not in `F`, then `dim F + 1 ≤ dim G`. -/
theorem topologicalKrullDim_add_one_le_of_specializes {X : Type*} [TopologicalSpace X]
    [T0Space X] {F G : Set X} (hFG : F ⊆ G) (h : ∀ x ∈ F, ∃ y ∈ G, x ⤳ y ∧ y ∉ F) :
    topologicalKrullDim F + 1 ≤ topologicalKrullDim G := by
  have hi : IsInducing (Set.inclusion hFG) := (IsEmbedding.inclusion hFG).isInducing
  refine Order.krullDim_add_one_le_of_strictMono _
    (TopologicalSpace.IrreducibleCloseds.map_strictMono_of_isInducing hi) fun Z ↦ ?_
  obtain ⟨⟨x, hxF⟩, hxZ⟩ := Z.isIrreducible.nonempty
  obtain ⟨y, hyG, hxy, hyF⟩ := h x hxF
  let y' : G := ⟨y, hyG⟩
  have hxy' : Set.inclusion hFG ⟨x, hxF⟩ ⤳ y' :=
    (IsInducing.subtypeVal.specializes_iff (x := Set.inclusion hFG ⟨x, hxF⟩) (y := y')).mp hxy
  refine ⟨⟨closure {y'}, isIrreducible_singleton.closure, isClosed_closure⟩, ?_⟩
  have hmem : Set.inclusion hFG ⟨x, hxF⟩ ∈ closure (Set.inclusion hFG '' Z) :=
    subset_closure (Set.mem_image_of_mem _ hxZ)
  refine lt_of_le_of_ne ?_ fun heq ↦ ?_
  · change closure {y'} ⊆ closure (Set.inclusion hFG '' Z)
    refine closure_minimal (Set.singleton_subset_iff.mpr ?_) isClosed_closure
    exact closure_mono (Set.singleton_subset_iff.mpr (Set.mem_image_of_mem _ hxZ))
      (specializes_iff_mem_closure.mp hxy')
  · have h1 : Set.inclusion hFG ⟨x, hxF⟩ ∈ closure ({y'} : Set G) := by
      have := congrArg (fun W : TopologicalSpace.IrreducibleCloseds G ↦ (W : Set G)) heq
      change closure {y'} = closure (Set.inclusion hFG '' Z) at this
      rw [this]; exact hmem
    have := congrArg Subtype.val ((specializes_iff_mem_closure.mpr h1).antisymm hxy').eq
    change y = x at this
    exact hyF (this ▸ hxF)


namespace AlgebraicGeometry

/-- The fibre of the affine line `𝔸¹_S ⟶ S` over any point has at least two points. -/
lemma AffineSpace.not_subsingleton_fiber (S : Scheme.{u}) (s : S) :
    ¬ Subsingleton ((𝔸(PUnit; S) ↘ S).fiber s) := by
  intro (h : Subsingleton
    (Limits.pullback (𝔸(PUnit; S) ↘ S) (S.fromSpecResidueField s) : Scheme.{u}))
  let e := (AffineSpace.isPullback_map (n := PUnit) (S.fromSpecResidueField s)).isoPullback
  have h1 : Subsingleton 𝔸(PUnit; Spec (S.residueField s)) :=
    e.hom.isOpenEmbedding.injective.subsingleton
  let e' := AffineSpace.SpecIso PUnit (S.residueField s)
  have h2 : Subsingleton (Spec (.of (MvPolynomial PUnit (S.residueField s)))) :=
    e'.inv.isOpenEmbedding.injective.subsingleton
  let R := MvPolynomial PUnit (S.residueField s)
  let p : PrimeSpectrum R := ⟨⊥, Ideal.isPrime_bot⟩
  let q : PrimeSpectrum R :=
    ⟨RingHom.ker (MvPolynomial.eval (fun _ ↦ (0 : S.residueField s))), RingHom.ker_isPrime _⟩
  have : p = q := @Subsingleton.elim _ h2 p q
  have hX : (MvPolynomial.X PUnit.unit : R) ∈ q.asIdeal := by simp [q]
  rw [← this] at hX
  exact MvPolynomial.X_ne_zero _ hX

/-- The projection `𝔸¹_S ⟶ S` maps the generic point to the generic point. -/
lemma AffineSpace.over_genericPoint (S : Scheme.{u}) [IrreducibleSpace S] :
    (𝔸(PUnit; S) ↘ S) (genericPoint 𝔸(PUnit; S)) = genericPoint S := by
  refine (IsGenericPoint.eq ?_ (genericPoint_spec S))
  rw [isGenericPoint_iff_specializes]
  intro z
  obtain ⟨w, rfl⟩ := (𝔸(PUnit; S) ↘ S).surjective z
  exact iff_of_true (((genericPoint_spec _).specializes (Set.mem_univ w)).map
    (𝔸(PUnit; S) ↘ S).continuous) trivial

/-- Blueprint `lemma-coordinate-projections--1`: Coordinate projections lower generic
dimension.

Let `S` be integral with function field `K`, let `f : X ⟶ S` be locally of finite type (in the
blueprint `X` is open in a closed subscheme of `𝔸ᵐ_S`) and let `t : X ⟶ 𝔸¹_S` be a morphism over
`S` (in the blueprint, a coordinate `t_r`). If `dim X_K ≤ n`, then the fibre of `t` over the
generic point of `𝔸¹_S` has dimension at most `n - 1`, an empty fibre having dimension `⊥`. -/
theorem topologicalKrullDim_fiber_genericPoint_add_one_le {S X : Scheme.{u}} [IsIntegral S]
    (f : X ⟶ S) [LocallyOfFiniteType f] (t : X ⟶ 𝔸(PUnit; S))
    (ht : t ≫ 𝔸(PUnit; S) ↘ S = f) :
    topologicalKrullDim (t.fiber (genericPoint 𝔸(PUnit; S))) + 1 ≤
      topologicalKrullDim (f.fiber (genericPoint S)) := by
  set π := 𝔸(PUnit; S) ↘ S
  set η := genericPoint S
  set η' := genericPoint 𝔸(PUnit; S)
  have hπη : π η' = η := AffineSpace.over_genericPoint S
  rw [IsHomeomorph.topologicalKrullDim_eq _ (t.fiberHomeo η').isHomeomorph,
    IsHomeomorph.topologicalKrullDim_eq _ (f.fiberHomeo η).isHomeomorph]
  have hFG : t ⁻¹' {η'} ⊆ f ⁻¹' {η} := by
    intro x hx
    simp only [Set.mem_preimage, Set.mem_singleton_iff] at hx ⊢
    rw [← ht, Scheme.Hom.comp_apply, hx, hπη]
  refine topologicalKrullDim_add_one_le_of_specializes hFG fun x hx ↦ ?_
  have hxG := hFG hx
  let x' : f.fiber η := (f.fiberHomeo η).symm ⟨x, hxG⟩
  obtain ⟨z, hz, hzc⟩ := nonempty_inter_closedPoints (Set.singleton_nonempty x').closure
    isClosed_closure.isLocallyClosed
  refine ⟨f.fiberι η z, (f.range_fiberι η).subset ⟨z, rfl⟩, ?_, fun hyF ↦ ?_⟩
  · have : x' ⤳ z := specializes_iff_mem_closure.mpr hz
    simpa [x'] using this.map (f.fiberι η).continuous
  simp only [Set.mem_preimage, Set.mem_singleton_iff] at hyF
  let φ : f.fiber η ⟶ π.fiber η := pullback.map f (S.fromSpecResidueField η) π
    (S.fromSpecResidueField η) t (𝟙 _) (𝟙 _) (by simp [π, ht]) (by simp)
  have hφι : φ ≫ π.fiberι η = f.fiberι η ≫ t := pullback.lift_fst _ _ _
  have hφs : φ ≫ π.fiberToSpecResidueField η = f.fiberToSpecResidueField η := by
    simp [φ, Scheme.Hom.fiberToSpecResidueField]
  have : LocallyOfFiniteType φ := by
    have : LocallyOfFiniteType (φ ≫ π.fiberToSpecResidueField η) := by
      rw [hφs]; dsimp [Scheme.Hom.fiberToSpecResidueField]; infer_instance
    exact locallyOfFiniteType_of_comp φ (π.fiberToSpecResidueField η)
  have hw := φ.closedPoints_subset_preimage_closedPoints hzc
  have hwη : π.fiberι η (φ z) = η' := by
    rw [← Scheme.Hom.comp_apply, hφι, Scheme.Hom.comp_apply]; exact hyF
  apply AffineSpace.not_subsingleton_fiber S η
  suffices h : ∀ a, a = φ z from ⟨fun a b ↦ by rw [h a, h b]⟩
  intro a
  have h1 : η' ⤳ π.fiberι η a := (genericPoint_spec _).specializes (Set.mem_univ _)
  rw [← hwη] at h1
  have h2 : φ z ⤳ a :=
    ((IsPreimmersion.isEmbedding (π.fiberι η)).isInducing.specializes_iff).mp h1
  have h3 := specializes_iff_mem_closure.mp h2
  rw [(mem_closedPoints_iff.mp hw).closure_eq] at h3
  exact h3

end AlgebraicGeometry
