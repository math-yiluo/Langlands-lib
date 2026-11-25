/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

import WeilConjectures.AlgebraicGeometry.ProEtale.RepleteAddCommGrp

public import Mathlib.Topology.Algebra.OpenSubgroup
public import WeilConjectures.Algebra.Homology.DerivedCategory.Ext.TowerLimit
public import WeilConjectures.AlgebraicGeometry.ProEtale.FiniteCoefficientCohomology
public import WeilConjectures.AlgebraicGeometry.ProEtale.Replete

/-!
# Pro-étale cohomology with profinite coefficients

Let `A` be a compact abelian topological group with a decreasing sequence of open subgroups
`Uₘ` with trivial intersection, e.g. `A = 𝒪_E` for a finite extension `E` of `ℚ_ℓ` and
`Uₘ = ℓᵐ 𝒪_E`. Then `A = lim A / Uₘ`, and the pro-étale sheaf `U ↦ C(U, A)` is the limit of the
tower of the constant sheaves `U ↦ C(U, A / Uₘ)`, whose transition maps are epimorphisms with
finite constant kernels. The pro-étale topos being replete, the Milnor sequence of this tower
is short exact, and its long exact cohomology sequence shows: if `S` is a scheme of finite type
and dimension at most `d` over a separably closed field, then `Hᵠ(S_proét, C(-, A)) = 0` for
`q > 2d` (`AlgebraicGeometry.ProEtale.subsingleton_H_continuousSheaf_of_profinite`).

## Main statements

- `ContinuousMap.existsUnique_comp_mk_eq`: continuous maps to `A` are compatible families of
  continuous maps to the finite discrete quotients `A / Uₘ`.
- `AlgebraicGeometry.Scheme.ProEt.epiπAppZeroOfEpi_addCommGrpCat`: repleteness of the pro-étale
  topos for abelian sheaves.
- `AlgebraicGeometry.ProEtale.subsingleton_H_continuousSheaf_of_profinite`: the vanishing of
  `Hᵠ(S_proét, C(-, A))` for `q > 2d`.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

section Topology

variable {A : Type*} [TopologicalSpace A] [AddCommGroup A] [IsTopologicalAddGroup A]
  [CompactSpace A] (U : ℕ → OpenAddSubgroup A)

/-- In a compact group, a decreasing sequence of open subgroups with trivial intersection is a
basis of neighbourhoods of `0`. -/
lemma OpenAddSubgroup.exists_le_of_mem_nhds_zero (hU : ∀ m, U (m + 1) ≤ U m)
    (hU₀ : ∀ x, (∀ m, x ∈ U m) → x = 0) {V : Set A} (hV : V ∈ nhds (0 : A)) :
    ∃ m, (U m : Set A) ⊆ V := by
  have hanti : Antitone fun m ↦ (U m : Set A) :=
    antitone_nat_of_succ_le fun m ↦ (hU m : ((U (m + 1) : Set A) ⊆ U m))
  refine exists_subset_nhds_of_isCompact' hanti.directed_ge
    (fun m ↦ (U m).isClosed.isCompact) (fun m ↦ (U m).isClosed)
      (mem_nhdsSet_iff_forall.2 fun x hx ↦ ?_)
  rw [hU₀ x (Set.mem_iInter.1 hx)]
  exact hV

/-- **Continuous maps to a profinite group.** Let `A` be a compact group with a decreasing
sequence of open subgroups `Uₘ` with trivial intersection. A compatible family of continuous
maps `gₘ : T → A / Uₘ` lifts uniquely to a continuous map `f : T → A`. -/
lemma ContinuousMap.existsUnique_comp_mk_eq {T : Type*} [TopologicalSpace T]
    (hU : ∀ m, U (m + 1) ≤ U m) (hU₀ : ∀ x, (∀ m, x ∈ U m) → x = 0)
    (g : ∀ m, T → A ⧸ (U m : AddSubgroup A)) (hg : ∀ m, Continuous (g m))
    (hcompat : ∀ m t, QuotientAddGroup.map _ _ (AddMonoidHom.id A) (hU m) (g (m + 1) t) = g m t) :
    ∃! f : C(T, A), ∀ m t, (QuotientAddGroup.mk (f t) : A ⧸ (U m : AddSubgroup A)) = g m t := by
  have hanti : Antitone U := antitone_nat_of_succ_le hU
  -- the fibres `{a | a mod Uₘ = gₘ t}` are closed, nonempty and decreasing
  have hne (t : T) : (⋂ m, {a : A | (QuotientAddGroup.mk a : A ⧸ (U m : AddSubgroup A)) =
      g m t}).Nonempty := by
    refine IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed _ (fun m a ha ↦ ?_)
      (fun m ↦ ?_) ?_ (fun m ↦ ?_)
    · simp only [Set.mem_ofPred_eq] at ha ⊢
      rw [← hcompat m t, ← ha]
      rfl
    · obtain ⟨a, ha⟩ := QuotientAddGroup.mk_surjective (g m t)
      exact ⟨a, ha⟩
    · have : DiscreteTopology (A ⧸ (U 0 : AddSubgroup A)) :=
        QuotientAddGroup.discreteTopology (U 0).isOpen
      exact ((isClosed_discrete {g 0 t}).preimage continuous_quot_mk).isCompact
    · have : DiscreteTopology (A ⧸ (U m : AddSubgroup A)) :=
        QuotientAddGroup.discreteTopology (U m).isOpen
      exact (isClosed_discrete {g m t}).preimage continuous_quot_mk
  choose f hf using hne
  have hf' (m : ℕ) (t : T) : (QuotientAddGroup.mk (f t) : A ⧸ (U m : AddSubgroup A)) = g m t :=
    Set.mem_iInter.1 (hf t) m
  have hcont : Continuous f := by
    refine continuous_iff_continuousAt.2 fun t ↦ ?_
    rw [ContinuousAt, Filter.tendsto_def]
    intro W hW
    obtain ⟨m, hm⟩ := OpenAddSubgroup.exists_le_of_mem_nhds_zero U hU hU₀
      (V := (· + f t) ⁻¹' W) ((continuous_id.add continuous_const).continuousAt.preimage_mem_nhds
        (by simpa using hW))
    have : DiscreteTopology (A ⧸ (U m : AddSubgroup A)) :=
      QuotientAddGroup.discreteTopology (U m).isOpen
    refine Filter.mem_of_superset ((hg m).continuousAt.preimage_mem_nhds
      ((isOpen_discrete {g m t}).mem_nhds (Set.mem_singleton _))) fun s hs ↦ ?_
    have hs' : f s - f t ∈ U m := QuotientAddGroup.eq_iff_sub_mem.1
      ((hf' m s).trans ((Set.mem_singleton_iff.1 hs).trans (hf' m t).symm))
    simpa using hm hs'
  refine ⟨⟨f, hcont⟩, hf', fun f' hf'' ↦ ContinuousMap.ext fun t ↦ ?_⟩
  rw [← sub_eq_zero]
  refine hU₀ _ fun m ↦ ?_
  exact QuotientAddGroup.eq_iff_sub_mem.1 ((hf'' m t).trans (hf' m t).symm)

end Topology

namespace AlgebraicGeometry.Scheme

variable {S : Scheme.{u}}

/-- **Repleteness for abelian sheaves on the affine pro-étale site**: the projection
`lim Fₙ ⟶ F₀` of a tower of epimorphisms of abelian sheaves is an epimorphism. -/
lemma AffineProEt.epiπAppZeroOfEpi_addCommGrpCat :
    EpiπAppZeroOfEpi (Sheaf (AffineProEt.topology S) AddCommGrpCat.{u + 1}) :=
  AffineProEt.epi_π_app_zero_of_epi_addCommGrpCat.{u} (S := S)

/-- **Repleteness for abelian sheaves on the pro-étale site** (Bhatt–Scholze, Proposition
4.2.8): the projection `lim Fₙ ⟶ F₀` of a tower of epimorphisms of abelian sheaves is an
epimorphism. -/
lemma ProEt.epiπAppZeroOfEpi_addCommGrpCat :
    EpiπAppZeroOfEpi (Sheaf (ProEt.topology S) AddCommGrpCat.{u + 1}) :=
  ProEt.epi_π_app_zero_of_epi_addCommGrpCat.{u} (S := S)

end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.ProEtale

variable (S : Scheme.{u}) {A : Type} [TopologicalSpace A] [AddCommGroup A]
  [IsTopologicalAddGroup A] [CompactSpace A]

/-- The quotient map `A ⟶ A / Uₘ`, as a continuous homomorphism. -/
noncomputable def openAddSubgroupQuotientMk (U : ℕ → OpenAddSubgroup A) (m : ℕ) :
    ContinuousAddMonoidHom A (A ⧸ (U m : AddSubgroup A)) :=
  ⟨QuotientAddGroup.mk' _, continuous_quot_mk⟩

/-- The transition map `A / Uₘ₊₁ ⟶ A / Uₘ`, as a continuous homomorphism of discrete groups. -/
noncomputable def openAddSubgroupQuotientMap (U : ℕ → OpenAddSubgroup A)
    (hU : ∀ m, U (m + 1) ≤ U m) (m : ℕ) :
    ContinuousAddMonoidHom (A ⧸ (U (m + 1) : AddSubgroup A)) (A ⧸ (U m : AddSubgroup A)) :=
  ⟨QuotientAddGroup.map _ _ (AddMonoidHom.id A) (hU m),
    have := QuotientAddGroup.discreteTopology (U (m + 1)).isOpen
    continuous_of_discreteTopology⟩

/-- The tower of sheaves `U ↦ C(U, A / Uₘ)` on `S_proét`. -/
noncomputable def continuousSheafTower (U : ℕ → OpenAddSubgroup A) (hU : ∀ m, U (m + 1) ≤ U m) :
    ℕᵒᵖ ⥤ Sheaf (Scheme.ProEt.topology S) AddCommGrpCat.{u + 1} :=
  Functor.ofOpSequence (X := fun m ↦ continuousSheaf S (A ⧸ (U m : AddSubgroup A)))
    fun m ↦ continuousSheafMap S (openAddSubgroupQuotientMap U hU m)

omit [CompactSpace A] in
lemma continuousSheafTower_map_succ (U : ℕ → OpenAddSubgroup A) (hU : ∀ m, U (m + 1) ≤ U m)
    (m : ℕ) : (continuousSheafTower S U hU).map (homOfLE (m.le_add_right 1)).op =
      continuousSheafMap S (openAddSubgroupQuotientMap U hU m) :=
  Functor.ofOpSequence_map_homOfLE_succ _ m

/-- The cone `C(-, A) ⟶ C(-, A / Uₘ)` over the tower `continuousSheafTower`. -/
noncomputable def continuousSheafCone (U : ℕ → OpenAddSubgroup A) (hU : ∀ m, U (m + 1) ≤ U m) :
    Cone (continuousSheafTower S U hU) where
  pt := continuousSheaf S A
  π := NatTrans.ofOpSequence (F := (Functor.const ℕᵒᵖ).obj (continuousSheaf S A))
    (G := continuousSheafTower S U hU)
    (fun m ↦ continuousSheafMap S (openAddSubgroupQuotientMk U m))
    fun m ↦ by
      rw [continuousSheafTower_map_succ, ← continuousSheafMap_comp]
      exact Category.id_comp _

/-- **`C(-, A)` is the limit of the `C(-, A / Uₘ)`**: a continuous map to `A` is a compatible
family of continuous maps to the quotients `A / Uₘ`. -/
noncomputable def isLimitContinuousSheafCone (U : ℕ → OpenAddSubgroup A)
    (hU : ∀ m, U (m + 1) ≤ U m) (hU₀ : ∀ x, (∀ m, x ∈ U m) → x = 0) :
    IsLimit (continuousSheafCone S U hU) := by
  refine isLimitOfReflects (sheafToPresheaf _ _) (evaluationJointlyReflectsLimits _ fun V ↦ ?_)
  refine isLimitOfReflects (CategoryTheory.forget AddCommGrpCat.{u + 1}) ?_
  refine Classical.choice ((Types.isLimit_iff _).2 fun s hs ↦ ?_)
  let g (m : ℕ) : C(V.unop.left, A ⧸ (U m : AddSubgroup A)) := (s (op m) :
    ULift.{u + 1} C(V.unop.left, A ⧸ (U m : AddSubgroup A))).down
  have hcompat (m : ℕ) (t : V.unop.left) :
      QuotientAddGroup.map _ _ (AddMonoidHom.id A) (hU m) (g (m + 1) t) = g m t := by
    have := hs (homOfLE (m.le_add_right 1)).op
    rw [Functor.comp_map, Functor.comp_map, Functor.comp_map, continuousSheafTower_map_succ] at this
    exact congrArg (fun x : ULift.{u + 1} C(V.unop.left, A ⧸ (U m : AddSubgroup A)) ↦ x.down t) this
  obtain ⟨f, hf, huniq⟩ := ContinuousMap.existsUnique_comp_mk_eq U hU hU₀ (fun m ↦ g m)
    (fun m ↦ (g m).continuous) hcompat
  refine ⟨ULift.up f, fun ⟨m⟩ ↦ ?_, fun x hx ↦ ?_⟩
  · exact congrArg ULift.up (ContinuousMap.ext fun t ↦ hf m t)
  · refine congrArg ULift.up (huniq x.down fun m t ↦ ?_)
    exact congrArg (fun x : ULift.{u + 1} C(V.unop.left, A ⧸ (U m : AddSubgroup A)) ↦ x.down t)
      (hx (op m))

omit [CompactSpace A] in
/-- The morphism of sheaves `C(-, A) ⟶ C(-, B)` induced by a surjective homomorphism of discrete
groups is an epimorphism: a continuous map to `B` is locally constant, hence locally lifts. -/
lemma epi_continuousSheafMap_of_surjective {B : Type} [TopologicalSpace B] [AddCommGroup B]
    [IsTopologicalAddGroup B] [DiscreteTopology A] [DiscreteTopology B]
    (φ : ContinuousAddMonoidHom A B) (hφ : Function.Surjective φ) :
    Epi (continuousSheafMap S φ) := by
  rw [← Sheaf.isLocallySurjective_iff_epi']
  refine ⟨fun {V} s₀ ↦ ?_⟩
  let s : C(V.left, B) := s₀.down
  refine Scheme.ProEt.mem_topology_of_openImmersion _
    (fun x : V.left ↦ (V.left.fiberOpens s (s x)).ι)
    (fun x ↦ ⟨x, ⟨x, rfl⟩, Scheme.Opens.ι_apply _ _⟩) fun x ↦
      ⟨ULift.up (ContinuousMap.const _ (hφ (s x)).choose), ?_⟩
  exact congrArg ULift.up (ContinuousMap.ext fun y ↦ (hφ (s x)).choose_spec.trans y.2.symm)

end AlgebraicGeometry.ProEtale

namespace CategoryTheory.Sheaf

variable {C : Type*} [Category* C] {J : GrothendieckTopology C} [HasSheafify J AddCommGrpCat.{u}]

/-- A short complex `F₁ ⟶ F₂ ⟶ F₃` of abelian sheaves is exact if on sections `F₁(V) ⟶ F₂(V)` is
injective with image the kernel of `F₂(V) ⟶ F₃(V)`: then `F₁` is the kernel of `F₂ ⟶ F₃`. -/
lemma exact_of_injective_of_exact_sections {S : ShortComplex (Sheaf J AddCommGrpCat.{u})}
    (hf : ∀ V, Function.Injective (S.f.hom.app V))
    (hS : ∀ V (y : S.X₂.obj.obj V), S.g.hom.app V y = 0 → ∃ x, S.f.hom.app V x = y) :
    S.Exact := by
  refine S.exact_of_f_is_kernel (isLimitOfReflects (sheafToPresheaf J _)
    ((KernelFork.isLimitMapConeEquiv _ _).symm (evaluationJointlyReflectsLimits _ fun V ↦
      (KernelFork.isLimitMapConeEquiv _ _).symm ?_)))
  let T := S.map (sheafToPresheaf J _ ⋙ (evaluation _ _).obj V)
  have : Mono T.f := (AddCommGrpCat.mono_iff_injective _).2 (hf V)
  exact ((ShortComplex.ab_exact_iff T).2 (hS V)).fIsKernel

end CategoryTheory.Sheaf

namespace AlgebraicGeometry.ProEtale

variable (S : Scheme.{u}) {A : Type} [TopologicalSpace A] [AddCommGroup A]
  [IsTopologicalAddGroup A] [CompactSpace A]

omit [CompactSpace A] in
/-- The morphism of sheaves induced by the zero homomorphism is zero. -/
lemma continuousSheafMap_zero {B : Type} [TopologicalSpace B] [AddCommGroup B]
    [IsTopologicalAddGroup B] : continuousSheafMap S (0 : ContinuousAddMonoidHom A B) = 0 := by
  ext V x
  rfl

/-- The kernel `Uₘ / Uₘ₊₁` of the transition map `A / Uₘ₊₁ ⟶ A / Uₘ`, a finite group. -/
noncomputable abbrev openAddSubgroupQuotientMapKer (U : ℕ → OpenAddSubgroup A)
    (hU : ∀ m, U (m + 1) ≤ U m) (m : ℕ) : AddSubgroup (A ⧸ (U (m + 1) : AddSubgroup A)) :=
  (openAddSubgroupQuotientMap U hU m : A ⧸ (U (m + 1) : AddSubgroup A) →+
    A ⧸ (U m : AddSubgroup A)).ker

/-- The short exact sequence `0 ⟶ C(-, Uₘ / Uₘ₊₁) ⟶ C(-, A / Uₘ₊₁) ⟶ C(-, A / Uₘ) ⟶ 0` of
sheaves on `S_proét`. -/
noncomputable def continuousSheafShortComplex (U : ℕ → OpenAddSubgroup A)
    (hU : ∀ m, U (m + 1) ≤ U m) (m : ℕ) :
    ShortComplex (Sheaf (Scheme.ProEt.topology S) AddCommGrpCat.{u + 1}) :=
  ShortComplex.mk
    (continuousSheafMap S ⟨(openAddSubgroupQuotientMapKer U hU m).subtype, continuous_subtype_val⟩)
    (continuousSheafMap S (openAddSubgroupQuotientMap U hU m)) (by
      rw [← continuousSheafMap_comp, ← continuousSheafMap_zero S]
      congr 1
      ext x
      exact x.2)

omit [CompactSpace A] in
lemma shortExact_continuousSheafShortComplex (U : ℕ → OpenAddSubgroup A)
    (hU : ∀ m, U (m + 1) ≤ U m) (m : ℕ) :
    (continuousSheafShortComplex S U hU m).ShortExact := by
  have hinj (V : (Scheme.ProEt S)ᵒᵖ) :
      Function.Injective ((continuousSheafShortComplex S U hU m).f.hom.app V) := fun x y h ↦
    ULift.ext (ContinuousMap.ext fun t ↦ Subtype.ext (congrArg
      (fun z : ULift.{u + 1} C(V.unop.left, A ⧸ (U (m + 1) : AddSubgroup A)) ↦ z.down t) h))
  refine .mk' (Sheaf.exact_of_injective_of_exact_sections hinj fun V y hy ↦ ?_) ?_ ?_
  · let y' : ULift.{u + 1} C(V.unop.left, A ⧸ (U (m + 1) : AddSubgroup A)) := y
    have hy' (t : V.unop.left) : y'.down t ∈ openAddSubgroupQuotientMapKer U hU m :=
      congrArg (fun z : ULift.{u + 1} C(V.unop.left, A ⧸ (U m : AddSubgroup A)) ↦ z.down t) hy
    exact ⟨ULift.up ⟨fun t ↦ ⟨_, hy' t⟩, y'.down.continuous.subtype_mk _⟩, rfl⟩
  · have (V : (Scheme.ProEt S)ᵒᵖ) :
        Mono (((sheafToPresheaf _ _).map (continuousSheafShortComplex S U hU m).f).app V) :=
      (AddCommGrpCat.mono_iff_injective _).2 (hinj V)
    have : Mono ((sheafToPresheaf _ _).map (continuousSheafShortComplex S U hU m).f) :=
      NatTrans.mono_of_mono_app _
    exact (sheafToPresheaf _ _).mono_of_mono_map this
  · refine epi_continuousSheafMap_of_surjective S _ fun x ↦ ?_
    obtain ⟨a, rfl⟩ := QuotientAddGroup.mk_surjective x
    exact ⟨QuotientAddGroup.mk a, rfl⟩

/-- **Pro-étale cohomology with profinite coefficients in high degrees.** Let `S` be a scheme of
finite type and of dimension at most `d` over a separably closed field, and `A` a compact abelian
group with a decreasing sequence of open subgroups `Uₘ` with trivial intersection (e.g. `𝒪_E`
with `Uₘ = ℓᵐ 𝒪_E`). Then `Hᵠ(S_proét, C(-, A)) = 0` for `q > 2d`. -/
theorem subsingleton_H_continuousSheaf_of_profinite {K : Type u} [Field K] [IsSepClosed K]
    {S : Scheme.{u}} (a : S ⟶ Spec (.of K)) [LocallyOfFiniteType a] [QuasiCompact a] (d : ℕ)
    (hS : topologicalKrullDim S ≤ (d : WithBot ℕ∞)) (U : ℕ → OpenAddSubgroup A)
    (hU : ∀ m, U (m + 1) ≤ U m) (hU₀ : ∀ x, (∀ m, x ∈ U m) → x = 0) (q : ℕ) (hq : 2 * d < q) :
    Subsingleton (Sheaf.H (continuousSheaf S A) q) := by
  have hrep := Scheme.ProEt.epiπAppZeroOfEpi_addCommGrpCat (S := S)
  have := Abelian.hasFiniteBiproducts (C := Sheaf (Scheme.ProEt.topology S) AddCommGrpCat.{u + 1})
  have := lim_preservesEpimorphisms_of_epi_π_app_zero hrep
  have := hasExactLimitsOfShape_of_preservesEpi
    (Sheaf (Scheme.ProEt.topology S) AddCommGrpCat.{u + 1}) (Discrete ℕ)
  have hepi (m : ℕ) : Epi ((continuousSheafTower S U hU).map (homOfLE m.le_succ).op) := by
    rw [continuousSheafTower_map_succ]
    exact (shortExact_continuousSheafShortComplex S U hU m).epi_g
  refine Abelian.Ext.subsingleton_of_isLimit_tower _
    (fun P hP t ht ↦ epi_one_sub_of_epiπAppZeroOfEpi hrep hepi hP t ht)
    (isLimitContinuousSheafCone S U hU hU₀) (2 * d)
    (fun n q hq ↦ subsingleton_H_continuousSheaf_of_two_mul_lt a d hS _ q hq) (fun n ↦ ?_) q hq
  have h := Abelian.Ext.surjective_comp_mk₀_of_shortExact
    (shortExact_continuousSheafShortComplex S U hU n) _ (2 * d)
    (subsingleton_H_continuousSheaf_of_two_mul_lt a d hS _ (2 * d + 1) (by lia))
  rw [continuousSheafTower_map_succ]
  exact h

end AlgebraicGeometry.ProEtale
