/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.ConstructibleSheaf.GenericConstancy
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import WeilConjectures.Mathlib.Topology.KrullDimension
public import WeilConjectures.Topology.KrullDimension.Open

/-!
# A lisse locus for a constructible sheaf

Let `X` be a nonempty scheme of finite type over a field `k` and `F` a constructible sheaf on the
small étale site of `X`. Then `F` is lisse (finite locally constant) on an open subscheme `U` whose
complement has strictly smaller dimension than `X`
(`AlgebraicGeometry.Scheme.IsConstructibleSheaf.exists_open_topologicalKrullDim_compl_lt`).

By generic constancy (`AlgebraicGeometry.Scheme.IsConstructibleSheaf.exists_dense_open`) `F` is
finite locally constant on a dense open `U`. The dimension drop is topological: in a Noetherian
quasi-sober space a dense open contains the generic point of every irreducible component, because
each component contains a nonempty open subset (`Dense.exists_specializes_of_isOpen`); so every
point of the complement has a proper generalization outside it, and a chain of irreducible closed
subsets of the complement can be lengthened by one inside `X`
(`topologicalKrullDim_compl_lt_of_dense`). A finite type scheme over a field has finite dimension
(`AlgebraicGeometry.topologicalKrullDim_ne_top_of_compactSpace`).

## Main statements

- `topologicalKrullDim_compl_lt_of_dense`
- `AlgebraicGeometry.Scheme.IsConstructibleSheaf.exists_open_topologicalKrullDim_compl_lt`
-/

@[expose] public section

universe u u'

open CategoryTheory TopologicalSpace

section Topology

variable {X : Type*} [TopologicalSpace X]

/-- In a Noetherian quasi-sober space, a dense open subset `U` contains a generalization of
every point `x`: the generic point of an irreducible component `T` through `x`. Indeed `T`
contains a nonempty open subset of `X`, which meets `U`, and an open set meeting `T` contains its
generic point. -/
theorem Dense.exists_specializes_of_isOpen [NoetherianSpace X] [QuasiSober X] {U : Set X}
    (hU : Dense U) (hUo : IsOpen U) (x : X) : ∃ z ∈ U, z ⤳ x := by
  have hT := irreducibleComponent_mem_irreducibleComponents x
  obtain ⟨o, ho, hon, hoT⟩ :=
    NoetherianSpace.exists_isOpen_nonempty_subset_irreducibleComponent _ hT
  obtain ⟨y, hyo, hyU⟩ := hU.inter_open_nonempty o ho hon
  have hgen := hT.1.isGenericPoint_genericPoint_closure
  rw [(isClosed_of_mem_irreducibleComponents _ hT).closure_eq] at hgen
  exact ⟨_, (hgen.specializes (hoT hyo)).mem_open hUo hyU,
    hgen.specializes (mem_irreducibleComponent)⟩

/-- **The complement of a dense open has smaller dimension.** In a nonempty Noetherian
quasi-sober `T₀` space of finite Krull dimension, the closed complement of a dense open subset
`U` has strictly smaller Krull dimension: every point of `Uᶜ` has a generalization in `U`
(`Dense.exists_specializes_of_isOpen`), so a chain of irreducible closed subsets of `Uᶜ` extends
by one in `X`. -/
theorem topologicalKrullDim_compl_lt_of_dense [NoetherianSpace X] [QuasiSober X] [T0Space X]
    [Nonempty X] (hX : topologicalKrullDim X ≠ ⊤) {U : Set X} (hU : Dense U) (hUo : IsOpen U) :
    topologicalKrullDim (Uᶜ : Set X) < topologicalKrullDim X := by
  obtain ⟨d, hd⟩ : ∃ d : ℕ, topologicalKrullDim X = d := by
    obtain ⟨e, he⟩ := WithBot.ne_bot_iff_exists.1
      (ne_bot_of_le_ne_bot (by simp) (topologicalKrullDim_nonneg (X := X)))
    obtain ⟨d, rfl⟩ := ENat.ne_top_iff_exists.1 (show e ≠ ⊤ by rintro rfl; exact hX he.symm)
    exact ⟨d, he.symm⟩
  have huniv : topologicalKrullDim (Set.univ : Set X) = topologicalKrullDim X :=
    (Homeomorph.Set.univ X).isHomeomorph.topologicalKrullDim_eq
  rw [hd]
  refine topologicalKrullDim_lt_of_forall_exists_specializes isClosed_univ hUo.isClosed_compl
    (Set.subset_univ _) (fun w _ ↦ ?_) ?_
  · obtain ⟨z, hz, hzw⟩ := hU.exists_specializes_of_isOpen hUo w
    exact ⟨z, trivial, hzw, fun h ↦ h hz⟩
  · rw [huniv, hd]
    exact_mod_cast Nat.lt_succ_self d

end Topology

noncomputable section

namespace AlgebraicGeometry.Scheme

variable {A : Type u'} [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [HasSmallSiteSheafify A]
  {FA : A → A → Type (u + 1)} {CA : A → Type (u + 1)}
  [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory.{u + 1} A FA]

/-- Blueprint `proposition-purity-lisse-part-fourier-transform`: A lisse locus for a constructible
sheaf.

Let `X` be a nonempty scheme of finite type over a field `k` and `F` a constructible sheaf on
`X_et`. Then there is an open subscheme `U ⊆ X` with `dim (X \ U) < dim X` on which the
restriction `F|_U` is lisse, that is, finite locally constant.

(For `X` empty both dimensions are `⊥` and the strict inequality cannot hold, which is why `X`
is assumed nonempty.) Generic constancy gives a dense open `U` on which `F` is finite locally
constant, and the complement of a dense open in the Noetherian space `X`, of finite dimension,
has smaller dimension (`topologicalKrullDim_compl_lt_of_dense`). -/
theorem IsConstructibleSheaf.exists_open_topologicalKrullDim_compl_lt {k : Type u} [Field k]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f] [QuasiCompact f]
    [Nonempty X] (F : Sheaf X.smallEtaleTopology A) [IsConstructibleSheaf F] :
    ∃ U : X.Opens, topologicalKrullDim ((U : Set X)ᶜ : Set X) < topologicalKrullDim X ∧
      IsFiniteLocallyConstantSheaf ((Etale.upperStar A U.ι).obj F) := by
  obtain ⟨U, hU, hF⟩ := IsConstructibleSheaf.exists_dense_open (FA := FA) (CA := CA) F
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have := LocallyOfFiniteType.isLocallyNoetherian f
  have : IsNoetherian X := {}
  exact ⟨U, topologicalKrullDim_compl_lt_of_dense (topologicalKrullDim_ne_top_of_compactSpace f)
    hU U.isOpen, hF⟩

end AlgebraicGeometry.Scheme
