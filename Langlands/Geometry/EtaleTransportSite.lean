import Langlands.Geometry.EtaleTransportCategory
import Mathlib.CategoryTheory.Sites.CoverPreserving
import Mathlib.CategoryTheory.Sites.Continuous

/-! # The group-labelled small-etale site -/

noncomputable section

universe u w wT uA vA

namespace Langlands.Geometry.EtaleTransport

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open EtaleCohomologyAction

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {Y : Scheme.{u}} {G : Type w} [Group G]
variable (ρ : G →* (Aut Y)ᵐᵒᵖ)

/-- The ordinary small-etale arrows belonging to a transport sieve. -/
abbrev inclusionSieve {U : Object ρ} (S : Sieve U) : Sieve U.etale :=
  Sieve.functorPullback (X := U.etale) (inclusion ρ) S

/-- Ordinary small-etale covers define covers in the group-labelled category. -/
def transportTopology : GrothendieckTopology (Object ρ) where
  sieves U := {S | inclusionSieve ρ S ∈ Y.smallEtaleTopology U.etale}
  top_mem' U := by
    change (⊤ : Sieve U.etale) ∈ Y.smallEtaleTopology U.etale
    exact Y.smallEtaleTopology.top_mem U.etale
  pullback_stable' U V S f hS := by
    change inclusionSieve ρ S ∈ Y.smallEtaleTopology U.etale at hS
    change inclusionSieve ρ (S.pullback f) ∈ Y.smallEtaleTopology V.etale
    have hT := Y.smallEtaleTopology.pullback_stable (Object.ordinaryPart f) hS
    have hT' := (EtaleAutomorphism.siteMap (aut ρ f.label)).cover_lift
      Y.smallEtaleTopology Y.smallEtaleTopology hT
    refine Y.smallEtaleTopology.superset_covering ?_ hT'
    intro W i hi
    change S ((inclusion ρ).map i ≫ f)
    have hj : S ((inclusion ρ).map
        ((EtaleAutomorphism.siteMap (aut ρ f.label)).map i ≫ Object.ordinaryPart f)) := hi
    have heq : (Object.translationIso f.label ((inclusion ρ).obj W)).hom ≫
        (inclusion ρ).map
          ((EtaleAutomorphism.siteMap (aut ρ f.label)).map i ≫ Object.ordinaryPart f) =
        (inclusion ρ).map i ≫ f :=
      Object.Hom.ext (by simp) (by simp)
    rw [← heq]
    exact S.downward_closed hj _
  transitive' U S hS R hR := by
    change inclusionSieve ρ S ∈ Y.smallEtaleTopology U.etale at hS
    change inclusionSieve ρ R ∈ Y.smallEtaleTopology U.etale
    apply Y.smallEtaleTopology.transitive hS
    intro W i hi
    have h := hR hi
    change inclusionSieve ρ (R.pullback ((inclusion ρ).map i)) ∈
      Y.smallEtaleTopology W at h
    dsimp only [inclusionSieve] at h ⊢
    erw [Sieve.functorPullback_pullback] at h
    exact h

/-- Covering in the transport site is tested on ordinary small-etale arrows. -/
theorem mem_transportTopology_iff {U : Object ρ} {S : Sieve U} :
    S ∈ transportTopology ρ U ↔
      inclusionSieve ρ S ∈ Y.smallEtaleTopology U.etale :=
  Iff.rfl

/-- Point-lifting characterization using the ordinary arrows of a sieve. -/
theorem mem_transportTopology_iff_ordinary {U : Object ρ} {S : Sieve U} :
    S ∈ transportTopology ρ U ↔
      ∀ x : U.etale.left, ∃ (V : Y.Etale) (f : V ⟶ U.etale) (v : V.left),
        S ((inclusion ρ).map f) ∧ f.left v = x := by
  rw [mem_transportTopology_iff, EtaleAutomorphism.mem_smallEtaleTopology_iff]
  rfl

/-- Equivalently, the underlying scheme maps of arrows of the sieve cover. -/
theorem mem_transportTopology_iff_points {U : Object ρ} {S : Sieve U} :
    S ∈ transportTopology ρ U ↔
      ∀ x : U.etale.left, ∃ (V : Object ρ) (f : V ⟶ U) (v : V.etale.left),
        S f ∧ f.left v = x := by
  rw [mem_transportTopology_iff_ordinary]
  constructor
  · intro h x
    obtain ⟨V, f, v, hf, hv⟩ := h x
    exact ⟨⟨V⟩, (inclusion ρ).map f, v, hf, hv⟩
  · intro h x
    obtain ⟨V, f, v, hf, hv⟩ := h x
    refine ⟨(Object.translate f.label V).etale, Object.ordinaryPart f, v, ?_, hv⟩
    rw [← Object.translationIso_inv_comp]
    exact S.downward_closed hf _

/-- Inclusion carries ordinary covering sieves to covering sieves. -/
theorem inclusion_coverPreserving :
    CoverPreserving Y.smallEtaleTopology (transportTopology ρ) (inclusion ρ) where
  cover_preserve {U S} hS := by
    change inclusionSieve ρ (S.functorPushforward (inclusion ρ)) ∈ Y.smallEtaleTopology U
    exact Y.smallEtaleTopology.superset_covering
      (Sieve.le_functorPushforward_pullback (inclusion ρ) S) hS

/-- The common label of two arrows gives an ordinary comparison of families. -/
theorem inclusion_compatiblePreserving :
    CompatiblePreserving.{wT} (transportTopology ρ) (inclusion ρ) where
  compatible ℱ Z T x hx Y₁ Y₂ W f₁ f₂ g₁ g₂ hg₁ hg₂ heq := by
    have hlab : f₁.label = f₂.label := by
      have h := congrArg Object.Hom.label heq
      simpa using h
    let k₁ := Object.ordinaryPart f₁
    let k₂ : (Object.translate f₁.label W).etale ⟶ Y₂ :=
      MorphismProperty.Over.homMk f₂.left (by
        change f₂.left ≫ Y₂.hom = W.etale.hom ≫ (aut ρ f₁.label).hom
        rw [hlab]
        exact f₂.w)
    have hk : k₁ ≫ g₁ = k₂ ≫ g₂ := by
      apply MorphismProperty.Over.Hom.ext
      exact congrArg Object.Hom.left heq
    have hx' : ℱ.obj.map ((inclusion ρ).map k₁).op (x g₁ hg₁) =
        ℱ.obj.map ((inclusion ρ).map k₂).op (x g₂ hg₂) :=
      hx k₁ k₂ hg₁ hg₂ hk
    have hfac₂ : (Object.translationIso f₁.label W).hom ≫ (inclusion ρ).map k₂ = f₂ :=
      Object.Hom.ext (by simp [hlab]) (by simp [k₂])
    calc ℱ.obj.map f₁.op (x g₁ hg₁)
        = ℱ.obj.map ((Object.translationIso f₁.label W).hom ≫
            (inclusion ρ).map k₁).op (x g₁ hg₁) := by
          erw [Object.translationIso_hom_comp_ordinaryPart]
          rfl
      _ = ℱ.obj.map (Object.translationIso f₁.label W).hom.op
            (ℱ.obj.map ((inclusion ρ).map k₁).op (x g₁ hg₁)) := by
          erw [op_comp, Functor.map_comp_apply]
          rfl
      _ = ℱ.obj.map (Object.translationIso f₁.label W).hom.op
            (ℱ.obj.map ((inclusion ρ).map k₂).op (x g₂ hg₂)) := by
          rw [hx']
      _ = ℱ.obj.map ((Object.translationIso f₁.label W).hom ≫
            (inclusion ρ).map k₂).op (x g₂ hg₂) := by
          erw [op_comp, Functor.map_comp_apply]
          rfl
      _ = ℱ.obj.map f₂.op (x g₂ hg₂) := by rw [hfac₂]

/-- Ordinary restriction is a continuous morphism of sites. -/
instance inclusion_isContinuous :
    (inclusion ρ).IsContinuous Y.smallEtaleTopology (transportTopology ρ) :=
  Functor.isContinuous_of_coverPreserving (inclusion_compatiblePreserving ρ)
    (inclusion_coverPreserving ρ)

/-- Ordinary sheaf descent suffices for descent along all labelled arrows. -/
theorem isSheaf_of_isSheaf_inclusion {Q : (Object ρ)ᵒᵖ ⥤ Type wT}
    (hQ : Presieve.IsSheaf Y.smallEtaleTopology ((inclusion ρ).op ⋙ Q)) :
    Presieve.IsSheaf (transportTopology ρ) Q := by
  intro U S hS x hx
  obtain ⟨t, ht, hu⟩ := hQ (inclusionSieve ρ S) hS
    (x.functorPullback (Z := U.etale) (inclusion ρ)) (hx.functorPullback _)
  change Q.obj (op U) at t
  refine ⟨t, ?_, fun t' ht' => hu t' fun W i hi => ht' _ hi⟩
  intro V f hf
  have hj : S ((inclusion ρ).map (Object.ordinaryPart f)) := by
    rw [← Object.translationIso_inv_comp]
    exact S.downward_closed hf _
  have ht' : Q.map ((inclusion ρ).map (Object.ordinaryPart f)).op t =
      x ((inclusion ρ).map (Object.ordinaryPart f)) hj :=
    ht (Object.ordinaryPart f) hj
  have hcomp := hx (𝟙 V) (Object.translationIso f.label V).hom hf hj
    (by rw [Category.id_comp, Object.translationIso_hom_comp_ordinaryPart])
  calc Q.map f.op t
      = Q.map ((Object.translationIso f.label V).hom ≫
          (inclusion ρ).map (Object.ordinaryPart f)).op t := by
        erw [Object.translationIso_hom_comp_ordinaryPart]
        rfl
    _ = Q.map (Object.translationIso f.label V).hom.op
          (Q.map ((inclusion ρ).map (Object.ordinaryPart f)).op t) := by
        erw [op_comp, Functor.map_comp_apply]
        rfl
    _ = Q.map (Object.translationIso f.label V).hom.op
          (x ((inclusion ρ).map (Object.ordinaryPart f)) hj) := by rw [ht']
    _ = x f hf := by simpa using hcomp.symm

variable (A : Type uA) [Category.{vA} A]

/-- The sheaf condition is exactly the ordinary small-etale sheaf condition. -/
theorem isSheaf_transportTopology_iff (P : (Object ρ)ᵒᵖ ⥤ A) :
    Presheaf.IsSheaf (transportTopology ρ) P ↔
      Presheaf.IsSheaf Y.smallEtaleTopology ((inclusion ρ).op ⋙ P) := by
  constructor
  · intro h
    exact (inclusion ρ).op_comp_isSheaf_of_isSheaf Y.smallEtaleTopology
      (transportTopology ρ) P h
  · intro h E
    exact isSheaf_of_isSheaf_inclusion ρ (h E)

/-- Equivariant small-etale sheaves, with all natural transformations as morphisms. -/
abbrev Sheaf := CategoryTheory.Sheaf (transportTopology ρ) A

/-- Forget group-labelled restriction maps, retaining the actual ordinary sheaf. -/
def toSheaf : Sheaf ρ A ⥤ CategoryTheory.Sheaf Y.smallEtaleTopology A :=
  (inclusion ρ).sheafPushforwardContinuous A Y.smallEtaleTopology (transportTopology ρ)

@[simp]
theorem toSheaf_obj_obj (F : Sheaf ρ A) :
    ((toSheaf ρ A).obj F).obj = (inclusion ρ).op ⋙ F.obj :=
  rfl

end Langlands.Geometry.EtaleTransport
