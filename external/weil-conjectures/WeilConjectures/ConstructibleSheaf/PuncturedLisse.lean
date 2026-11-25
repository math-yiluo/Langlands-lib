/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.ConstructibleSheaf.GenericConstancy
public import WeilConjectures.ConstructibleSheaf.Refinement
public import WeilConjectures.Mathlib.Topology.KrullDimension

/-!

# Constructible sheaves are lisse on a punctured neighbourhood of a point of a curve

Let `X` be an irreducible noetherian scheme of dimension at most one and `x` a closed point. For
finitely many constructible sheaves `F i` on `X_ét` there is an open neighbourhood `U` of `x` such
that every `F i` is finite locally constant on the punctured neighbourhood `U ∖ {x}`
(`AlgebraicGeometry.Scheme.exists_isFiniteLocallyConstantSheaf_punctured`): by generic constancy
the `F i` are finite locally constant on a dense open `W`, whose complement is a finite set of
closed points. This is the first step of blueprint `lemma-tangent-cones-on-cover` (i): the
terms of constructible models are lisse on the punctured neighbourhood.

-/

@[expose] public section

universe u' u

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry.Scheme

variable {X : Scheme.{u}} {A : Type u'} [Category.{u + 1} A] [Abelian A]
  [IsGrothendieckAbelian.{u + 1} A] [HasSmallSiteSheafify A]
  {FA : A → A → Type (u + 1)} {CA : A → Type (u + 1)}
  [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory.{u + 1} A FA]

/-- The punctured open `U ∖ {x}` of an open `U`, for a closed point `x`. -/
def puncturedOpens (U : X.Opens) (x : X) (hx : IsClosed ({x} : Set X)) : X.Opens :=
  U ⊓ ⟨{x}ᶜ, hx.isOpen_compl⟩

/-- **Lisse on a punctured neighbourhood** (blueprint `lemma-tangent-cones-on-cover` (i), first
step): on an irreducible noetherian scheme of dimension at most one, finitely many constructible
sheaves are finite locally constant on a punctured open neighbourhood of a closed point `x`. -/
theorem exists_isFiniteLocallyConstantSheaf_punctured [IrreducibleSpace X] [NoetherianSpace X]
    (hX : topologicalKrullDim X ≤ 1) {x : X} (hx : IsClosed ({x} : Set X)) {ι : Type*}
    [Finite ι] (F : ι → Sheaf X.smallEtaleTopology A) [∀ i, IsConstructibleSheaf (F i)] :
    ∃ U : X.Opens, x ∈ U ∧ ∀ i,
      IsFiniteLocallyConstantSheaf ((Etale.upperStar A (puncturedOpens U x hx).ι).obj (F i)) := by
  choose W hWd hW using fun i ↦ IsConstructibleSheaf.exists_dense_open (FA := FA) (CA := CA) (F i)
  have hne : ∀ i, (W i : Set X).Nonempty := fun i ↦
    (hWd i).nonempty_iff.2 ⟨(IrreducibleSpace.isIrreducible_univ X).nonempty.some⟩
  -- the bad points: the finitely many closed points outside some `W i`, other than `x`
  let Z : Set X := (⋃ i, (W i : Set X)ᶜ) \ {x}
  have hZf : Z.Finite := (Set.finite_iUnion fun i ↦
    (W i).isOpen.finite_compl_of_topologicalKrullDim_le_one hX (hne i)).sdiff
  have hZc : IsClosed Z := by
    rw [← Set.biUnion_of_singleton Z]
    refine hZf.isClosed_biUnion fun z hz ↦ ?_
    obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hz.1
    exact (W i).isOpen.isClosed_singleton_of_mem_compl hX (hne i) hi
  refine ⟨⟨Zᶜ, hZc.isOpen_compl⟩, fun h ↦ h.2 rfl, fun i ↦ ?_⟩
  have hsub : Set.range (puncturedOpens ⟨Zᶜ, hZc.isOpen_compl⟩ x hx).ι.base ⊆
      Set.range (W i).ι.base := by
    rw [Opens.range_ι, Opens.range_ι]
    rintro z ⟨hzZ, hzx⟩
    by_contra hzW
    exact hzZ ⟨Set.mem_iUnion.2 ⟨i, hzW⟩, hzx⟩
  have := hW i
  exact IsFiniteLocallyConstantSheaf.upperStar_of_range_subset _ (W i).ι hsub (F i)

end AlgebraicGeometry.Scheme
