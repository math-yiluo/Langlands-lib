/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Semilinear.SemilinearDerivedSections

/-! # Finite block constructions and ordinary coherence

Source: Zheng, Construction 4.1 and its finite-block reindexing generalization.
(blueprint: lem-pur-system-block-constructions).

The existing block constructions, their ring identifications and ordinary
composition, identity and coefficient coherence are extracted from
SystemBlockRepetition to keep each file within the single-file compilation limit.
Their public signatures, definition bodies and global attributes are retained.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward false
set_option Elab.async false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe c v r u₁ u₂ u₃ u₄ v₁ v₂ v₃ v₄ w₁ w₂ w₃ w₄ u h w
open CategoryTheory CategoryTheory.Limits Opposite
namespace WeilConjectures.SemilinearSections

/-- A nondecreasing surjection with finite nonempty interval fibers.
Source: finite-block generalization of Zheng 4.1
(blueprint: lem-pur-system-block-constructions). -/
structure SystemBlockMap where
  /-- The map on zero-based sequence indices. -/
  index : ℕ →o ℕ
  /-- Every block occurs. -/
  onto : Function.Surjective index
  /-- Every block is finite; monotonicity makes it an interval. -/
  finite : ∀ i : ℕ, Set.Finite {m : ℕ | index m = i}

/-- The first index of a block, not an arbitrary point in its fiber.
Source: finite-block endpoint construction following Zheng 4.1
(blueprint: lem-pur-system-block-constructions). -/
def SystemBlockMap.first (t : SystemBlockMap) (i : ℕ) : ℕ := Nat.find (t.onto i)

/-- The repeated coefficient objects.
Source: Zheng 4.1, finite-block reindexing
(blueprint: lem-pur-system-block-constructions). -/
def blockCoefficients {C : Type c} [Category.{v} C] {J : GrothendieckTopology C}
    (B : ℕ → Sheaf J CommRingCat.{r}) (t : SystemBlockMap) :
    ℕ → Sheaf J CommRingCat.{r} := fun m ↦ B (t.index m)

/-- The repeated transition is the specified composite; within a block it is the identity.
Source: Zheng 4.1, finite-block reindexing
(blueprint: lem-pur-system-block-constructions). -/
def blockTransitions {C : Type c} [Category.{v} C] [EssentiallySmall.{r} C]
    (J : GrothendieckTopology C) (B : ℕ → Sheaf J CommRingCat.{r})
    (τ : ∀ n : ℕ, B (n + 1) ⟶ B n) (t : SystemBlockMap) (m : ℕ) :
    blockCoefficients B t (m + 1) ⟶ blockCoefficients B t m :=
  coefficientMap J B τ (t.index.monotone (Nat.le_succ m))

/-- Endpoint and interval properties, and the no-skipped-level assertion at a boundary.
Source: finite-block generalization of Zheng 4.1
(blueprint: lem-pur-system-block-constructions).
Proof: Nat.find_spec gives t(a_i)=i and Nat.find_min' gives minimality. Monotonicity
then gives a_i≤m<a_(i+1) for t(m)=i and monotonicity of a. If t(m+1)>t(m)+1,
surjectivity at the missing integer contradicts monotonicity on either side of m.
Thus blockTransitions is identity within blocks and the original adjacent map at a boundary. -/
theorem systemBlockMap_endpoints (t : SystemBlockMap) :
    (∀ i : ℕ, t.index (t.first i) = i) ∧ Monotone t.first ∧
    (∀ m : ℕ, t.first (t.index m) ≤ m ∧ m < t.first (t.index m + 1)) ∧
    (∀ m : ℕ, t.index (m + 1) = t.index m ∨ t.index (m + 1) = t.index m + 1) := by
  have hf : ∀ i, t.index (t.first i) = i := fun i ↦ Nat.find_spec (t.onto i)
  have hmin : ∀ m, t.first (t.index m) ≤ m := fun m ↦
    Nat.find_min' (t.onto (t.index m)) rfl
  have hm : Monotone t.first := by
    intro i j hij
    by_contra hn
    have h := t.index.monotone (Nat.le_of_lt (Nat.lt_of_not_ge hn))
    rw [hf i, hf j] at h
    have he : i = j := Nat.le_antisymm hij h
    subst j
    exact hn le_rfl
  refine ⟨hf, hm, ?_, ?_⟩
  · intro m
    refine ⟨hmin m, ?_⟩
    by_contra hn
    have h := t.index.monotone (Nat.le_of_not_gt hn)
    rw [hf] at h
    exact Nat.not_succ_le_self _ h
  · intro m
    have hlo := t.index.monotone (Nat.le_succ m)
    by_cases he : t.index (m + 1) = t.index m
    · exact Or.inl he
    · right
      obtain ⟨k, hk⟩ := t.onto (t.index m + 1)
      by_cases hkm : k ≤ m
      · have h := t.index.monotone hkm
        rw [hk] at h
        exact False.elim (Nat.not_succ_le_self _ h)
      · have h := t.index.monotone (Nat.succ_le_of_lt (Nat.lt_of_not_ge hkm))
        rw [hk] at h
        exact Nat.le_antisymm h (Nat.succ_le_of_lt (lt_of_le_of_ne hlo (Ne.symm he)))

/-- First-endpoint monotonicity, needed by the real endpoint functor.
Source: Zheng 4.1 finite-block generalization (blueprint: lem-pur-system-block-constructions).
Proof: the endpoint and interval assertions of systemBlockMap_endpoints give this
projection; equivalently minimality and monotonicity of t prohibit reversed endpoints. -/
theorem SystemBlockMap.firstMonotone (t : SystemBlockMap) : Monotone t.first := by
  exact (systemBlockMap_endpoints t).2.1

/-- Reindexing of the sequence site by a monotone map.
Source: Zheng 4.1 (blueprint: lem-pur-system-block-constructions). -/
def blockSite {C : Type c} [Category.{v} C] (k : ℕ →o ℕ) : ℕ × C ⥤ ℕ × C :=
  k.toFunctor.prod (𝟭 C)

/-- Reindexing preserves the vertical sheaf condition.
Source: Zheng 4.1 (blueprint: lem-pur-system-block-constructions).
Proof: at (m,U) restriction along a vertical cover is exactly restriction of the
original sheaf along that same cover of U at level k(m); glue there. Thus
precomposition carries every sheaf to a sheaf, which is the continuity criterion. -/
theorem blockSite_continuous {C : Type c} [Category.{v} C]
    (J : GrothendieckTopology C) (k : ℕ →o ℕ) :
    (blockSite (C := C) k).IsContinuous
      (coefficientSequenceTopology J) (coefficientSequenceTopology J) := by
  apply Functor.isContinuous_of_coverPreserving
  · constructor
    intro G Z T x hx Y₁ Y₂ X f₁ f₂ g₁ g₂ hg₁ hg₂ he
    let W : ℕ × C := (min Y₁.1 Y₂.1, X.2)
    let p₁ : W ⟶ Y₁ := Prod.mkHom (homOfLE (min_le_left _ _)) f₁.2
    let p₂ : W ⟶ Y₂ := Prod.mkHom (homOfLE (min_le_right _ _)) f₂.2
    have hp : X.1 ≤ k (min Y₁.1 Y₂.1) := by
      rcases le_total Y₁.1 Y₂.1 with h | h
      · rw [min_eq_left h]
        exact leOfHom f₁.1
      · rw [min_eq_right h]
        exact leOfHom f₂.1
    let q : X ⟶ (blockSite (C := C) k).obj W :=
      Prod.mkHom (homOfLE hp) (𝟙 X.2)
    have e₁ : q ≫ (blockSite k).map p₁ = f₁ := by
      apply Prod.hom_ext
      · exact Subsingleton.elim _ _
      · simp [q, p₁, blockSite]
    have e₂ : q ≫ (blockSite k).map p₂ = f₂ := by
      apply Prod.hom_ext
      · exact Subsingleton.elim _ _
      · simp [q, p₂, blockSite]
    have hc := hx p₁ p₂ hg₁ hg₂ (by
      apply Prod.hom_ext
      · exact Subsingleton.elim _ _
      · change f₁.2 ≫ g₁.2 = f₂.2 ≫ g₂.2
        exact congrArg (fun f ↦ f.2) he)
    rw [← e₁, ← e₂, op_comp, op_comp, G.obj.map_comp, G.obj.map_comp]
    exact congrArg (G.obj.map q.op) hc
  · constructor
    intro X S hS
    apply J.superset_covering _ hS
    intro V f hf
    exact ⟨(X.1, V), Prod.mkHom (𝟙 _) f, 𝟙 _, hf, by
      ext <;> simp [blockSite]⟩

/-- Continuity for the canonical sequence-site reindexing.
Source: Zheng 4.1 (blueprint: lem-pur-system-block-constructions). -/
instance blockSiteContinuous {C : Type c} [Category.{v} C]
    (J : GrothendieckTopology C) (k : ℕ →o ℕ) :
    (blockSite (C := C) k).IsContinuous
      (coefficientSequenceTopology J) (coefficientSequenceTopology J) :=
  blockSite_continuous J k

/-- First endpoints as a bundled monotone map, with actual least-index data.
Source: Zheng 4.1 finite-block generalization (blueprint: lem-pur-system-block-constructions). -/
def SystemBlockMap.endpoints (t : SystemBlockMap) : ℕ →o ℕ :=
  ⟨t.first, t.firstMonotone⟩

/-- Fibers of a composite block map are finite unions of finite fibers.
Source: Zheng 4.1 finite-block composition (blueprint: lem-pur-system-block-constructions).
Proof: the fiber at i is the union, over the finite fiber t⁻¹(i), of the finite
fibers s⁻¹(j). Finite unions preserve finiteness. -/
theorem SystemBlockMap.comp_finite (t s : SystemBlockMap) (i : ℕ) :
    Set.Finite {m : ℕ | t.index (s.index m) = i} := by
  have h := (t.finite i).biUnion (fun j _ ↦ s.finite j)
  apply h.subset
  intro m hm
  exact Set.mem_iUnion₂.mpr ⟨s.index m, hm, rfl⟩

/-- Composite block map with its actual composed index function.
Source: Zheng 4.1 finite-block composition (blueprint: lem-pur-system-block-constructions). -/
def SystemBlockMap.comp (t s : SystemBlockMap) : SystemBlockMap where
  index := t.index.comp s.index
  onto := t.onto.comp s.onto
  finite := t.comp_finite s

/-- The identity block map, including singleton fibers.
Source: Zheng 4.1 identity reindexing (blueprint: lem-pur-system-block-constructions). -/
def SystemBlockMap.id : SystemBlockMap where
  index := OrderHom.id
  onto := Function.surjective_id
  finite := fun i ↦ Set.finite_singleton i

variable {C : Type c} [Category.{v} C] [EssentiallySmall.{r} C]
  (J : GrothendieckTopology C) (B : ℕ → Sheaf J CommRingCat.{r})
  (τ : ∀ n : ℕ, B (n + 1) ⟶ B n) (t : SystemBlockMap)

omit [EssentiallySmall.{r} C] in
private theorem blockRings (k : ℕ →o ℕ) :
    rings J (fun n ↦ B (k n))
      (fun n ↦ coefficientMap J B τ (k.monotone (Nat.le_succ n))) =
      k.toFunctor.op ⋙ rings J B τ := by
  let cmp : k.toFunctor.op ⋙ rings J B τ ⟶
      rings J (fun n ↦ B (k n))
        (fun n ↦ coefficientMap J B τ (k.monotone (Nat.le_succ n))) :=
    NatTrans.ofOpSequence (fun _ ↦ 𝟙 _) (by
      intro n
      simp only [Functor.comp_map, rings, Functor.ofOpSequence_map_homOfLE_succ,
        Category.id_comp, Category.comp_id]
      rfl)
  symm
  refine Functor.hext (fun _ ↦ rfl) ?_
  intro X Y f
  apply heq_of_eq
  have hh := cmp.naturality f
  dsimp only [cmp] at hh
  simpa only [NatTrans.ofOpSequence_app, Category.id_comp, Category.comp_id] using hh

omit [EssentiallySmall.{r} C] in
private theorem blockRingPresheaf (k : ℕ →o ℕ)
    (F : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{r}) :
    (blockSite (C := C) k).op ⋙ (prodOpEquiv (C := ℕ) (D := C)).functor ⋙
        Functor.uncurry.obj (F ⋙ sheafToPresheaf J CommRingCat.{r}) =
      (prodOpEquiv (C := ℕ) (D := C)).functor ⋙
        Functor.uncurry.obj ((k.toFunctor.op ⋙ F) ⋙ sheafToPresheaf J CommRingCat.{r}) := by
  refine CategoryTheory.Functor.ext (fun _ ↦ rfl) ?_
  intro X Y f
  rfl

/-- The identity coefficient identification for repetition on the sequence site.
Source: Zheng 4.1 (blueprint: lem-pur-system-block-constructions).
Proof: both ring sheaves have B_(t(m))(U) at (m,U). The horizontal maps are the
same composites of tau by functoriality of rings, including identity maps within
a block. Vertical maps are B_(t(m))'s restrictions. Extensionality proves equality. -/
theorem blockRepeatRing :
    ((blockSite (C := C) t.index).sheafPushforwardContinuous RingCat.{r}
      (coefficientSequenceTopology J) (coefficientSequenceTopology J)).obj
      (ring (coefficientSequenceTopology J) (systemRing J B τ)) =
    ring (coefficientSequenceTopology J)
      (systemRing J (blockCoefficients B t) (blockTransitions J B τ t)) := by
  let cmp : t.index.toFunctor.op ⋙ rings J B τ ⟶
      rings J (blockCoefficients B t) (blockTransitions J B τ t) :=
    NatTrans.ofOpSequence (fun _ ↦ 𝟙 _) (by
      intro n
      simp only [Functor.comp_map, rings, Functor.ofOpSequence_map_homOfLE_succ,
        Category.id_comp, Category.comp_id]
      rfl)
  apply ObjectProperty.FullSubcategory.ext
  refine Functor.hext (fun _ ↦ rfl) ?_
  intro X Y f
  have hh := cmp.naturality (f.unop.1).op
  dsimp only [cmp] at hh
  simp only [NatTrans.ofOpSequence_app, Category.id_comp, Category.comp_id] at hh
  dsimp [blockSite, ring, systemRing, ringPresheaf,
    Functor.sheafPushforwardContinuous]
  apply heq_of_eq
  change (forget₂ CommRingCat RingCat).map _ = (forget₂ CommRingCat RingCat).map _
  congr 1
  dsimp [Functor.uncurry]
  congr 1
  exact congrArg (fun α ↦ α.hom.app (op X.unop.2)) hh

/-- Actual repetition, as restriction on the ringed sequence site.
Source: Zheng 4.1 (blueprint: lem-pur-system-block-constructions). -/
def blockRepeat : Systems J B τ ⥤
    Systems J (blockCoefficients B t) (blockTransitions J B τ t) :=
  SheafOfModules.pushforward (F := blockSite (C := C) t.index)
    (eqToHom (blockRepeatRing J B τ t).symm)

/-- The identity coefficient identification at first endpoints.
Source: Zheng 4.1 finite-block generalization (blueprint: lem-pur-system-block-constructions).
Proof: t(a_i)=i identifies every section ring with B_i. The composite transition
from a_(i+1) to a_i reindexes to the original B_(i+1)→B_i by functoriality of the
coefficient sequence. Vertical restrictions are unchanged. Use sheaf extensionality. -/
theorem blockEndpointRing :
    ((blockSite (C := C) t.endpoints).sheafPushforwardContinuous RingCat.{r}
      (coefficientSequenceTopology J) (coefficientSequenceTopology J)).obj
      (ring (coefficientSequenceTopology J)
        (systemRing J (blockCoefficients B t) (blockTransitions J B τ t))) =
    ring (coefficientSequenceTopology J) (systemRing J B τ) := by
  have hi : t.endpoints.toFunctor ⋙ t.index.toFunctor = 𝟭 ℕ := by
    refine CategoryTheory.Functor.ext (fun n ↦ (systemBlockMap_endpoints t).1 n) ?_
    intro X Y f
    apply Subsingleton.elim
  have hr : t.endpoints.toFunctor.op ⋙
      rings J (blockCoefficients B t) (blockTransitions J B τ t) = rings J B τ := by
    rw [show rings J (blockCoefficients B t) (blockTransitions J B τ t) =
      t.index.toFunctor.op ⋙ rings J B τ from blockRings J B τ t.index]
    change (t.endpoints.toFunctor ⋙ t.index.toFunctor).op ⋙ rings J B τ = _
    rw [hi]
    rfl
  apply ObjectProperty.FullSubcategory.ext
  change ((blockSite (C := C) t.endpoints).op ⋙
      (prodOpEquiv (C := ℕ) (D := C)).functor ⋙
        Functor.uncurry.obj (rings J (blockCoefficients B t) (blockTransitions J B τ t) ⋙
          sheafToPresheaf J CommRingCat.{r})) ⋙ forget₂ CommRingCat RingCat = _
  rw [blockRingPresheaf, hr]
  rfl

/-- Actual first-endpoint evaluation, as restriction on the ringed sequence site.
Source: Zheng 4.1 finite-block generalization (blueprint: lem-pur-system-block-constructions). -/
def blockEndpoint : Systems J (blockCoefficients B t) (blockTransitions J B τ t) ⥤
    Systems J B τ :=
  SheafOfModules.pushforward (F := blockSite (C := C) t.endpoints)
    (eqToHom (blockEndpointRing J B τ t).symm)

/-- The actual endpoint/repetition pair, with all section and arrow formulas.
Source: Zheng 4.1, finite-block generalization; Stacks 08BJ
(blueprint: lem-pur-system-block-constructions). -/
structure SystemBlockRepetition where
  /-- Repetition of strict systems. -/
  repetition : Systems J B τ ⥤ Systems J (blockCoefficients B t) (blockTransitions J B τ t)
  /-- Repetition is the constructed restriction, not a chosen unrelated functor. -/
  repetition_canonical : repetition = blockRepeat J B τ t
  /-- Evaluation at first endpoints, with composite transitions. -/
  endpoint : Systems J (blockCoefficients B t) (blockTransitions J B τ t) ⥤ Systems J B τ
  /-- Endpoint evaluation is the constructed restriction. -/
  endpoint_canonical : endpoint = blockEndpoint J B τ t
  /-- The actual component modules, with their original coefficient actions. -/
  evaluation : ∀ m : ℕ,
    repetition ⋙ SemilinearSections.evaluation J (blockCoefficients B t)
      (blockTransitions J B τ t) m ≅ SemilinearSections.evaluation J B τ (t.index m)
  /-- These identifications are identities on section carriers. -/
  evaluation_sections : ∀ (m : ℕ) (M : Systems J B τ) (U : Cᵒᵖ)
    (x : ((SemilinearSections.evaluation J (blockCoefficients B t)
      (blockTransitions J B τ t) m).obj (repetition.obj M)).val.obj U),
    HEq ((((evaluation m).hom.app M).val.app U) x) x
  /-- Every presheaf restriction, including horizontal transitions, is reindexed. -/
  repeat_restrictions : ∀ (M : Systems J B τ) {U V : (ℕ × C)ᵒᵖ} (f : U ⟶ V),
    HEq (fun x ↦ (repetition.obj M).val.map f x)
      (fun x ↦ M.val.map (((t.index.toFunctor.prod (𝟭 C)).map f.unop).op) x)
  /-- The first-endpoint module is P_(a_i), including its module structure. -/
  endpoint_sections : ∀ (P : Systems J (blockCoefficients B t) (blockTransitions J B τ t))
    (i : ℕ) (U : Cᵒᵖ),
    HEq ((endpoint.obj P).val.obj (op (i, U.unop)))
      (P.val.obj (op (t.first i, U.unop)))
  /-- Endpoint morphisms are the original component maps. -/
  endpoint_maps : ∀ {P Q : Systems J (blockCoefficients B t) (blockTransitions J B τ t)}
    (f : P ⟶ Q) (i : ℕ) (U : Cᵒᵖ),
    HEq (fun x ↦ ((endpoint.map f).val.app (op (i, U.unop))) x)
      (fun x ↦ (f.val.app (op (t.first i, U.unop))) x)
  /-- First endpoints are monotone, permitting all composite transitions. -/
  first_monotone : Monotone t.first
  /-- Endpoint restrictions are the actual composites, including vertical restrictions. -/
  endpoint_restrictions : ∀
    (P : Systems J (blockCoefficients B t) (blockTransitions J B τ t))
    {U V : (ℕ × C)ᵒᵖ} (f : U ⟶ V),
    HEq (fun x ↦ (endpoint.obj P).val.map f x)
      (fun x ↦ P.val.map
        (((first_monotone.functor.prod (𝟭 C)).map f.unop).op) x)
  /-- The endpoint functor is LEFT adjoint to repetition. -/
  adjunction : endpoint ⊣ repetition
  /-- The adjunct formula uses the transition to the FIRST endpoint. -/
  adjunct : ∀
    (P : Systems J (blockCoefficients B t) (blockTransitions J B τ t))
    (M : Systems J B τ) (f : endpoint.obj P ⟶ M) (m : ℕ) (U : Cᵒᵖ)
    (h : t.first (t.index m) ≤ m),
    ∀ (x : P.val.obj (op (m, U.unop)))
      (y : (endpoint.obj P).val.obj (op (t.index m, U.unop))),
      HEq y (P.val.map (Prod.mkHom (homOfLE h) (𝟙 U.unop)).op x) →
      HEq ((((adjunction.homEquiv P M) f).val.app (op (m, U.unop))) x)
        ((f.val.app (op (t.index m, U.unop))) y)
  /-- Repetition is additive. -/
  [repeat_additive : repetition.Additive]
  /-- Repetition preserves kernels. -/
  [repeat_limits : PreservesFiniteLimits repetition]
  /-- Repetition preserves cokernels. -/
  [repeat_colimits : PreservesFiniteColimits repetition]
  /-- Endpoint evaluation is additive. -/
  [endpoint_additive : endpoint.Additive]
  /-- Endpoint evaluation preserves kernels. -/
  [endpoint_limits : PreservesFiniteLimits endpoint]
  /-- Endpoint evaluation preserves cokernels. -/
  [endpoint_colimits : PreservesFiniteColimits endpoint]
  /-- Repetition preserves K-injectives for UNBOUNDED complexes of systems. -/
  kinjective : ∀ I : CochainComplex (Systems J B τ) ℤ, I.IsKInjective →
    CochainComplex.IsKInjective ((repetition.mapHomologicalComplex (.up ℤ)).obj I)

attribute [instance] SystemBlockRepetition.repeat_additive SystemBlockRepetition.repeat_limits
  SystemBlockRepetition.repeat_colimits SystemBlockRepetition.endpoint_additive
  SystemBlockRepetition.endpoint_limits SystemBlockRepetition.endpoint_colimits

/-- K-injective preservation from the actual endpoint adjunction package.
Source: Stacks 08BJ (blueprint: lem-pur-system-block-constructions). -/
instance SystemBlockRepetition.preservesKInjective
    (R : SystemBlockRepetition J B τ t) : R.repetition.PreservesKInjectiveComplexes where
  isKInjective_map I := R.kinjective I inferInstance

end WeilConjectures.SemilinearSections
