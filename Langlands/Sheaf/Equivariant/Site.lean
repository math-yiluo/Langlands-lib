import Langlands.Sheaf.Equivariant.Topological
import Mathlib.CategoryTheory.Sites.Spaces
import Mathlib.CategoryTheory.Sites.CoverPreserving
import Mathlib.CategoryTheory.Sites.Continuous

/-!
# The transport site of a group action on a topological space

A sieve on an object of the transport category covers when its label-one
inclusions form an ordinary open cover. Sheaves for this topology are exactly
the published equivariant sheaves, so the two categories are equivalent.
-/

noncomputable section

namespace Langlands.Sheaf.Equivariant

open CategoryTheory TopologicalSpace Opposite

universe w uX uG uA vA

variable (G : Type uG) [Group G] (X : Type uX) [TopologicalSpace X] [MulAction G X]
variable [ContinuousConstSMul G X]

namespace ActionOpens

variable {G X}

/-- The translate of the source of an arrow by its label lies in the target. -/
theorem translate_le {V U : ActionOpens G X} (f : V ⟶ U) :
    (translate f.label V).openSet ≤ U.openSet := fun y hy => by
  simpa using f.mapsTo _ hy

/-- Every transport arrow is a translation isomorphism followed by a label-one inclusion. -/
theorem exists_translationIso_comp_inclusionHom {V U : ActionOpens G X} (f : V ⟶ U)
    (a : G) (ha : f.label = a) :
    ∃ h : (translate a V).openSet ≤ U.openSet,
      (translationIso a V).hom ≫ inclusionHom h = f := by
  subst ha
  refine ⟨translate_le f, Hom.ext ?_⟩
  change (1 : G) * f.label = f.label
  exact one_mul _

/-- Undoing the translation turns an arrow into the corresponding label-one inclusion. -/
theorem translationIso_inv_comp {V U : ActionOpens G X} (f : V ⟶ U) :
    (translationIso f.label V).inv ≫ f = inclusionHom (translate_le f) := by
  apply Hom.ext
  change f.label * f.label⁻¹ = 1
  exact mul_inv_cancel _

end ActionOpens

/-- A sieve contains every arrow equal to one of its arrows. -/
theorem sieve_arrows_of_eq {C : Type*} [Category C] {Y Z : C} (S : Sieve Z)
    {a b : Y ⟶ Z} (h : a = b) (ha : S a) : S b :=
  h ▸ ha

/-- The ordinary sieve of label-one inclusions belonging to a transport sieve. -/
abbrev inclusionSieve {G X} [Group G] [TopologicalSpace X] [MulAction G X]
    {U : ActionOpens G X} (S : Sieve U) : Sieve U.openSet :=
  Sieve.functorPullback (X := U.openSet) (ActionOpens.inclusion G X) S

/-- The transport topology: label-one inclusions in a covering sieve cover the open. -/
def transportTopology : GrothendieckTopology (ActionOpens G X) where
  sieves U := {S | inclusionSieve S ∈ Opens.grothendieckTopology X U.openSet}
  top_mem' U := by
    change inclusionSieve (⊤ : Sieve U) ∈ Opens.grothendieckTopology X U.openSet
    rw [Opens.mem_grothendieckTopology]
    intro x hx
    exact ⟨U.openSet, 𝟙 _, trivial, hx⟩
  pullback_stable' U V S f hS := by
    change inclusionSieve S ∈ Opens.grothendieckTopology X U.openSet at hS
    change inclusionSieve (S.pullback f) ∈ Opens.grothendieckTopology X V.openSet
    rw [Opens.mem_grothendieckTopology] at hS ⊢
    intro x hx
    obtain ⟨W, i, hi, hxW⟩ := hS (f.label • x) (f.mapsTo x hx)
    let W' : Opens X := V.openSet ⊓
      ⟨{y | f.label • y ∈ W}, W.isOpen.preimage (continuous_const_smul f.label)⟩
    let k : (ActionOpens.inclusion G X).obj W' ⟶ (ActionOpens.inclusion G X).obj W :=
      ⟨f.label, fun y hy => hy.2⟩
    have key : ((ActionOpens.inclusion G X).map (homOfLE inf_le_left : W' ⟶ V.openSet) :
          (ActionOpens.inclusion G X).obj W' ⟶ V) ≫ f =
        k ≫ (ActionOpens.inclusion G X).map i := by
      apply ActionOpens.Hom.ext
      change f.label * 1 = 1 * f.label
      rw [mul_one, one_mul]
    exact ⟨W', homOfLE inf_le_left,
      sieve_arrows_of_eq S key.symm (S.downward_closed hi k), ⟨hx, hxW⟩⟩
  transitive' U S hS R hR := by
    change inclusionSieve S ∈ Opens.grothendieckTopology X U.openSet at hS
    change inclusionSieve R ∈ Opens.grothendieckTopology X U.openSet
    rw [Opens.mem_grothendieckTopology] at hS ⊢
    intro x hx
    obtain ⟨W, i, hi, hxW⟩ := hS x hx
    have hRi : ∀ y ∈ W, ∃ (W₂ : Opens X) (j : W₂ ⟶ W),
        R ((ActionOpens.inclusion G X).map j ≫ (ActionOpens.inclusion G X).map i) ∧
          y ∈ W₂ :=
      hR hi
    obtain ⟨W₂, j, hj, hxW₂⟩ := hRi x hxW
    refine ⟨W₂, j ≫ i, ?_, hxW₂⟩
    change R ((ActionOpens.inclusion G X).map (j ≫ i))
    rw [Functor.map_comp]
    exact hj

variable {G X} in
/-- A sieve covers when the label-one inclusions it contains cover the open. -/
theorem mem_transportTopology_iff {U : ActionOpens G X} {S : Sieve U} :
    S ∈ transportTopology G X U ↔
      ∀ x ∈ U.openSet, ∃ (V : ActionOpens G X) (h : V.openSet ≤ U.openSet),
        S (ActionOpens.inclusionHom h) ∧ x ∈ V.openSet := by
  change inclusionSieve S ∈ Opens.grothendieckTopology X U.openSet ↔ _
  rw [Opens.mem_grothendieckTopology]
  constructor
  · intro hS x hx
    obtain ⟨W, i, hi, hxW⟩ := hS x hx
    exact ⟨⟨W⟩, i.le, hi, hxW⟩
  · intro hS x hx
    obtain ⟨V, h, hV, hxV⟩ := hS x hx
    exact ⟨V.openSet, homOfLE h, hV, hxV⟩

variable {G X} in
/-- Equivalently, the translated images of the arrows of a covering sieve cover the open. -/
theorem mem_transportTopology_iff_exists_smul {U : ActionOpens G X} {S : Sieve U} :
    S ∈ transportTopology G X U ↔
      ∀ x ∈ U.openSet, ∃ (V : ActionOpens G X) (f : V ⟶ U), S f ∧
        ∃ v ∈ V.openSet, f.label • v = x := by
  rw [mem_transportTopology_iff]
  constructor
  · intro hS x hx
    obtain ⟨V, h, hV, hxV⟩ := hS x hx
    exact ⟨V, ActionOpens.inclusionHom h, hV, x, hxV, one_smul G x⟩
  · intro hS x hx
    obtain ⟨V, f, hf, v, hv, rfl⟩ := hS x hx
    refine ⟨ActionOpens.translate f.label V, ActionOpens.translate_le f, ?_, ?_⟩
    · exact sieve_arrows_of_eq S (ActionOpens.translationIso_inv_comp f)
        (S.downward_closed hf _)
    · simpa using hv

/-- Ordinary covers generate transport covers. -/
theorem inclusion_coverPreserving :
    CoverPreserving (Opens.grothendieckTopology X) (transportTopology G X)
      (ActionOpens.inclusion G X) where
  cover_preserve {U S} hS := by
    change inclusionSieve (S.functorPushforward (ActionOpens.inclusion G X)) ∈
      Opens.grothendieckTopology X U
    exact GrothendieckTopology.superset_covering _
      (Sieve.le_functorPushforward_pullback (ActionOpens.inclusion G X) S) hS

/-- Restriction to label-one inclusions preserves compatible families. -/
theorem inclusion_compatiblePreserving :
    CompatiblePreserving.{w} (transportTopology G X) (ActionOpens.inclusion G X) where
  compatible ℱ Z T x hx Y₁ Y₂ W f₁ f₂ g₁ g₂ hg₁ hg₂ heq := by
    have hlab : f₁.label = f₂.label := by
      have h := congrArg ActionOpens.Hom.label heq
      change (1 : G) * f₁.label = 1 * f₂.label at h
      simpa using h
    obtain ⟨h₁, hfac₁⟩ :=
      ActionOpens.exists_translationIso_comp_inclusionHom f₁ f₁.label rfl
    obtain ⟨h₂, hfac₂⟩ :=
      ActionOpens.exists_translationIso_comp_inclusionHom f₂ f₁.label hlab.symm
    have h₁' : (ActionOpens.translate f₁.label W).openSet ≤ Y₁ := h₁
    have h₂' : (ActionOpens.translate f₁.label W).openSet ≤ Y₂ := h₂
    have hx' : ℱ.obj.map (ActionOpens.inclusionHom h₁).op (x g₁ hg₁) =
        ℱ.obj.map (ActionOpens.inclusionHom h₂).op (x g₂ hg₂) :=
      hx (homOfLE h₁') (homOfLE h₂') hg₁ hg₂ (Subsingleton.elim _ _)
    calc ℱ.obj.map f₁.op (x g₁ hg₁)
        = ℱ.obj.map ((ActionOpens.translationIso f₁.label W).hom ≫
            ActionOpens.inclusionHom h₁).op (x g₁ hg₁) := by rw [hfac₁]
      _ = ℱ.obj.map (ActionOpens.translationIso f₁.label W).hom.op
            (ℱ.obj.map (ActionOpens.inclusionHom h₁).op (x g₁ hg₁)) := by
          rw [op_comp, Functor.map_comp_apply]
      _ = ℱ.obj.map (ActionOpens.translationIso f₁.label W).hom.op
            (ℱ.obj.map (ActionOpens.inclusionHom h₂).op (x g₂ hg₂)) := by
          rw [hx']
      _ = ℱ.obj.map ((ActionOpens.translationIso f₁.label W).hom ≫
            ActionOpens.inclusionHom h₂).op (x g₂ hg₂) := by
          rw [op_comp, Functor.map_comp_apply]
      _ = ℱ.obj.map f₂.op (x g₂ hg₂) := by rw [hfac₂]

instance inclusion_isContinuous :
    (ActionOpens.inclusion G X).IsContinuous (Opens.grothendieckTopology X)
      (transportTopology G X) :=
  Functor.isContinuous_of_coverPreserving (inclusion_compatiblePreserving G X)
    (inclusion_coverPreserving G X)

variable {G X} in
/-- The ordinary sheaf condition implies the transport sheaf condition. -/
theorem isSheaf_of_isSheaf_inclusion {Q : (ActionOpens G X)ᵒᵖ ⥤ Type w}
    (hQ : Presieve.IsSheaf (Opens.grothendieckTopology X)
      ((ActionOpens.inclusion G X).op ⋙ Q)) :
    Presieve.IsSheaf (transportTopology G X) Q := by
  intro U S hS x hx
  obtain ⟨t, ht, hu⟩ := hQ (inclusionSieve S) hS
    (x.functorPullback (Z := U.openSet) (ActionOpens.inclusion G X)) (hx.functorPullback _)
  change Q.obj (op U) at t
  refine ⟨t, ?_, fun t' ht' => hu t' fun W i hi => ht' _ hi⟩
  intro V f hf
  obtain ⟨h, hfac⟩ := ActionOpens.exists_translationIso_comp_inclusionHom f f.label rfl
  have hj : S (ActionOpens.inclusionHom h) :=
    sieve_arrows_of_eq S (ActionOpens.translationIso_inv_comp f) (S.downward_closed hf _)
  have ht' : Q.map (ActionOpens.inclusionHom h).op t = x (ActionOpens.inclusionHom h) hj :=
    ht (homOfLE h) hj
  have hcomp := hx (𝟙 V) (ActionOpens.translationIso f.label V).hom hf hj
    (by rw [Category.id_comp, hfac])
  calc Q.map f.op t
      = Q.map ((ActionOpens.translationIso f.label V).hom ≫
          ActionOpens.inclusionHom h).op t := by rw [hfac]
    _ = Q.map (ActionOpens.translationIso f.label V).hom.op
          (Q.map (ActionOpens.inclusionHom h).op t) := by
        rw [op_comp, Functor.map_comp_apply]
    _ = Q.map (ActionOpens.translationIso f.label V).hom.op
          (x (ActionOpens.inclusionHom h) hj) := by
        rw [ht']
    _ = x f hf := by simpa using hcomp.symm

variable (A : Type uA) [Category.{vA} A]

/-- Transport sheaves are exactly the published equivariant sheaves. -/
theorem isSheaf_transportTopology_iff (P : (ActionOpens G X)ᵒᵖ ⥤ A) :
    Presheaf.IsSheaf (transportTopology G X) P ↔ sheafProperty G X A P := by
  constructor
  · intro h
    exact (ActionOpens.inclusion G X).op_comp_isSheaf_of_isSheaf
      (Opens.grothendieckTopology X) (transportTopology G X) P h
  · intro h E
    exact isSheaf_of_isSheaf_inclusion (h E)

/-- The published equivariant sheaf category is the category of transport sheaves. -/
def sheafEquivalence : TopologicalSheaf G X A ≌ Sheaf (transportTopology G X) A where
  functor := ObjectProperty.ιOfLE fun P hP => (isSheaf_transportTopology_iff G X A P).2 hP
  inverse := ObjectProperty.ιOfLE fun P hP => (isSheaf_transportTopology_iff G X A P).1 hP
  unitIso := Iso.refl _
  counitIso := Iso.refl _

@[simp]
theorem sheafEquivalence_functor_obj_obj (F : TopologicalSheaf G X A) :
    ((sheafEquivalence G X A).functor.obj F).obj = F.obj :=
  rfl

@[simp]
theorem sheafEquivalence_inverse_obj_obj (F : Sheaf (transportTopology G X) A) :
    ((sheafEquivalence G X A).inverse.obj F).obj = F.obj :=
  rfl

end Langlands.Sheaf.Equivariant
