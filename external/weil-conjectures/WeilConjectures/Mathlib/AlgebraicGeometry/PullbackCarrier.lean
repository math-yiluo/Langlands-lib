/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.Gluing
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import WeilConjectures.Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-!
# Pullback squares of schemes along open immersions

In a pullback square of schemes whose bottom is an open immersion, the top is an open
immersion with range the preimage of the range of the bottom. In any pullback square the
range of a projection is the preimage of the range of the opposite side
(`AlgebraicGeometry.Scheme.range_snd_of_isPullback`).

We also show that being a cartesian square is local on the target
(`AlgebraicGeometry.isPullback_of_iSup_opensRange_eq_top`, with the two-chart version
`AlgebraicGeometry.isPullback_of_opensRange_sup_eq_top`), and that the intersection of the
preimages of two affine opens in a pullback over an affine scheme is affine
(`AlgebraicGeometry.isAffineOpen_preimage_inf_preimage_pullback`).

Finally, the image of a product map `X ×_S Y ⟶ X' ×_{S'} Y'` is the intersection of the
images of the base changes of the two factors
(`AlgebraicGeometry.Scheme.Pullback.range_map_eq_inter`), and the diagonal of a base change is
the preimage of the diagonal (`AlgebraicGeometry.Scheme.Pullback.map_fst_mem_range_diagonal_iff`).

A morphism all of whose geometric fibres are nonempty is surjective
(`AlgebraicGeometry.Surjective.of_forall_nonempty_pullback`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

variable {P X Y Z : Scheme.{u}} {fst : P ⟶ X} {snd : P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z}

/-- In a pullback square of schemes whose bottom is an open immersion, the top is an open
immersion. -/
lemma _root_.CategoryTheory.IsPullback.isOpenImmersion_fst [IsOpenImmersion g]
    (h : IsPullback fst snd f g) : IsOpenImmersion fst :=
  MorphismProperty.of_isPullback (P := @IsOpenImmersion) h.flip inferInstance

/-- In a pullback square of schemes whose bottom `g` is an open immersion, the range of the
top is the preimage under `f` of the range of `g`. -/
lemma _root_.CategoryTheory.IsPullback.opensRange_fst [IsOpenImmersion g]
    (h : IsPullback fst snd f g) :
    have : IsOpenImmersion fst := h.isOpenImmersion_fst
    fst.opensRange = f ⁻¹ᵁ g.opensRange := by
  have : IsOpenImmersion fst := h.isOpenImmersion_fst
  apply TopologicalSpace.Opens.ext
  apply Set.ext
  intro x
  constructor
  · rintro ⟨p, rfl⟩
    exact ⟨snd p, by rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, h.w]⟩
  · rintro ⟨y, hy⟩
    obtain ⟨p, hp, -⟩ := Scheme.Pullback.exists_preimage_pullback x y hy.symm
    have e : h.isoPullback.inv ≫ fst = Limits.pullback.fst f g := by
      rw [Iso.inv_comp_eq, h.isoPullback_hom_fst]
    exact ⟨h.isoPullback.inv p, by rw [← Scheme.Hom.comp_apply, e]; exact hp⟩

/-- In a pullback square of schemes, the range of the projection `snd` is the preimage under
`g` of the range of `f`. -/
lemma Scheme.range_snd_of_isPullback (h : IsPullback fst snd f g) :
    Set.range snd = g ⁻¹' Set.range f := by
  refine subset_antisymm ?_ fun y ⟨x, hx⟩ ↦ ?_
  · rintro _ ⟨p, rfl⟩
    exact ⟨fst p, by rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, h.w]⟩
  · obtain ⟨p, -, hp⟩ := Scheme.Pullback.exists_preimage_pullback x y hx
    exact ⟨h.isoPullback.inv p, by rw [← Scheme.Hom.comp_apply, h.isoPullback_inv_snd, hp]⟩

section IsPullbackLocal

/-- **Being a cartesian square is local on the target.** If `Y` is covered by the images of
open immersions `mₐ : Yₐ ⟶ Y`, if `Xₐ ⟶ X` is the base change of `mₐ` along `h : X ⟶ Y`, and if
every square `Xₐ ⟶ Yₐ` over `S ⟶ T` is cartesian, then the square `X ⟶ Y` over `S ⟶ T` is
cartesian. -/
lemma isPullback_of_iSup_opensRange_eq_top {X Y S T : Scheme.{u}} {h : X ⟶ Y} {g : X ⟶ S}
    {p : Y ⟶ T} {π : S ⟶ T} (w : h ≫ p = g ≫ π)
    {ι : Type*} {Ya Xa : ι → Scheme.{u}} {m : ∀ a, Ya a ⟶ Y} {n : ∀ a, Xa a ⟶ X}
    {k : ∀ a, Xa a ⟶ Ya a} [∀ a, IsOpenImmersion (m a)]
    (hm : ⨆ a, (m a).opensRange = ⊤)
    (hchart : ∀ a, IsPullback (k a) (n a) (m a) h)
    (H : ∀ a, IsPullback (k a) (n a ≫ g) (m a ≫ p) π) :
    IsPullback h g p π := by
  set q : X ⟶ pullback p π := pullback.lift h g w with hq
  have hq₁ : q ≫ pullback.fst p π = h := pullback.lift_fst ..
  have hq₂ : q ≫ pullback.snd p π = g := pullback.lift_snd ..
  suffices hiso : IsIso q from IsPullback.of_iso_pullback ⟨w⟩ (asIso q) hq₁ hq₂
  set μ : ∀ a, pullback (m a ≫ p) π ⟶ pullback p π := fun a ↦
    pullback.map (m a ≫ p) π p π (m a) (𝟙 S) (𝟙 T) (by simp) (by simp) with hμdef
  have hμ : ∀ a, IsPullback (pullback.fst (m a ≫ p) π) (μ a) (m a) (pullback.fst p π) :=
    fun a ↦ isPullback_pullback_map_left (m a) p π
  have : ∀ a, IsOpenImmersion (μ a) := fun a ↦
    MorphismProperty.of_isPullback (P := @IsOpenImmersion) (hμ a) inferInstance
  -- the square `Xₐ ⟶ Yₐ ×_T S` over `X ⟶ Y ×_T S` is cartesian
  have key : ∀ a, IsPullback ((H a).isoPullback.hom) (n a) (μ a) q := by
    intro a
    refine IsPullback.of_right ?_ ?_ (hμ a)
    · rw [show (H a).isoPullback.hom ≫ pullback.fst (m a ≫ p) π = k a from
        IsPullback.isoPullback_hom_fst _, hq₁]
      exact hchart a
    · have h1 : (H a).isoPullback.hom ≫ pullback.fst (m a ≫ p) π = k a :=
        IsPullback.isoPullback_hom_fst _
      have h2 : (H a).isoPullback.hom ≫ pullback.snd (m a ≫ p) π = n a ≫ g :=
        IsPullback.isoPullback_hom_snd _
      apply pullback.hom_ext
      · have : μ a ≫ pullback.fst p π = pullback.fst (m a ≫ p) π ≫ m a := by simp [hμdef]
        rw [Category.assoc, this, ← Category.assoc, h1, (hchart a).w, Category.assoc, hq₁]
      · have : μ a ≫ pullback.snd p π = pullback.snd (m a ≫ p) π := by simp [hμdef]
        rw [Category.assoc, this, h2, Category.assoc, hq₂]
  let 𝒰 : (pullback p π).OpenCover :=
    Scheme.Cover.mkOfCovers ι _ μ (fun x ↦ by
      have hx : pullback.fst p π x ∈ (⨆ a, (m a).opensRange) := by rw [hm]; trivial
      obtain ⟨a, ⟨y, hy⟩⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
      obtain ⟨z, -, hz⟩ := Scheme.exists_preimage_of_isPullback (hμ a) y x hy
      exact ⟨a, z, hz⟩)
  rw [← MorphismProperty.isomorphisms.iff]
  refine IsZariskiLocalAtTarget.of_openCover 𝒰 fun a ↦ ?_
  rw [MorphismProperty.isomorphisms.iff]
  change IsIso (pullback.snd q (μ a))
  rw [show pullback.snd q (μ a) = (key a).flip.isoPullback.inv ≫ (H a).isoPullback.hom by
    rw [Iso.eq_inv_comp]
    exact IsPullback.isoPullback_hom_snd _]
  infer_instance

/-- **Being a cartesian square is local on the target**, two-chart version. -/
lemma isPullback_of_opensRange_sup_eq_top {X Y S T : Scheme.{u}} {h : X ⟶ Y} {g : X ⟶ S}
    {p : Y ⟶ T} {π : S ⟶ T} (w : h ≫ p = g ≫ π) {Y₁ Y₂ X₁ X₂ : Scheme.{u}}
    (m₁ : Y₁ ⟶ Y) (m₂ : Y₂ ⟶ Y) [IsOpenImmersion m₁] [IsOpenImmersion m₂]
    {n₁ : X₁ ⟶ X} {n₂ : X₂ ⟶ X} {k₁ : X₁ ⟶ Y₁} {k₂ : X₂ ⟶ Y₂}
    (hm : m₁.opensRange ⊔ m₂.opensRange = ⊤)
    (hchart₁ : IsPullback k₁ n₁ m₁ h) (hchart₂ : IsPullback k₂ n₂ m₂ h)
    (H₁ : IsPullback k₁ (n₁ ≫ g) (m₁ ≫ p) π) (H₂ : IsPullback k₂ (n₂ ≫ g) (m₂ ≫ p) π) :
    IsPullback h g p π := by
  have : ∀ b : Bool, IsOpenImmersion (Bool.rec (motive := fun b ↦ (cond b Y₁ Y₂) ⟶ Y) m₂ m₁ b) :=
    fun b ↦ by cases b <;> assumption
  refine isPullback_of_iSup_opensRange_eq_top w (ι := Bool) (Ya := fun b ↦ cond b Y₁ Y₂)
    (Xa := fun b ↦ cond b X₁ X₂)
    (m := fun b ↦ Bool.rec (motive := fun b ↦ (cond b Y₁ Y₂) ⟶ Y) m₂ m₁ b)
    (n := fun b ↦ Bool.rec (motive := fun b ↦ (cond b X₁ X₂) ⟶ X) n₂ n₁ b)
    (k := fun b ↦ Bool.rec (motive := fun b ↦ (cond b X₁ X₂) ⟶ (cond b Y₁ Y₂)) k₂ k₁ b)
    ?_ ?_ ?_
  · rw [iSup_bool_eq]
    exact hm
  · intro b; cases b
    · exact hchart₂
    · exact hchart₁
  · intro b; cases b
    · exact H₂
    · exact H₁

end IsPullbackLocal

/-- If `A` is an affine open of `X` and `B` is an affine open of `Y`, then the intersection of
their preimages in `X ×[T] Y` is an affine open, provided `T` is affine. -/
lemma isAffineOpen_preimage_inf_preimage_pullback {X Y T : Scheme.{u}} [IsAffine T]
    (f : X ⟶ T) (g : Y ⟶ T) {A : X.Opens} {B : Y.Opens} (hA : IsAffineOpen A)
    (hB : IsAffineOpen B) :
    IsAffineOpen (pullback.fst f g ⁻¹ᵁ A ⊓ pullback.snd f g ⁻¹ᵁ B) := by
  have : IsAffine A.toScheme := hA
  have : IsAffine B.toScheme := hB
  obtain ⟨m, hm₁, hm₂⟩ : ∃ m : pullback (A.ι ≫ f) (B.ι ≫ g) ⟶ pullback f g,
      IsOpenImmersion m ∧ Set.range m =
        pullback.fst f g ⁻¹' (A : Set X) ∩ pullback.snd f g ⁻¹' (B : Set Y) := by
    refine ⟨pullback.map (A.ι ≫ f) (B.ι ≫ g) f g A.ι B.ι (𝟙 _) (by simp) (by simp), ?_, ?_⟩
    · exact MorphismProperty.pullbackMap (P := @IsOpenImmersion) inferInstance inferInstance
        rfl rfl
    · rw [Scheme.Pullback.range_map]
      simp
  have := hm₁
  have hr : pullback.fst f g ⁻¹ᵁ A ⊓ pullback.snd f g ⁻¹ᵁ B = m.opensRange :=
    TopologicalSpace.Opens.ext (by rw [Scheme.Hom.coe_opensRange, hm₂]; rfl)
  rw [hr]
  exact isAffineOpen_opensRange _

/-- The image of the product map `X ×_S Y ⟶ X' ×_{S'} Y'` of `i₁ : X ⟶ X'` and `i₂ : Y ⟶ Y'`
over a monomorphism `S ⟶ S'` is the intersection of the images of the base changes of `i₁` and
`i₂` along the two projections of `X' ×_{S'} Y'`. -/
lemma Scheme.Pullback.range_map_eq_inter {X Y S X' Y' S' : Scheme.{u}} {f : X ⟶ S}
    {g : Y ⟶ S} (f' : X' ⟶ S') (g' : Y' ⟶ S') (i₁ : X ⟶ X') (i₂ : Y ⟶ Y') (i₃ : S ⟶ S')
    (e₁ : f ≫ i₃ = i₁ ≫ f') (e₂ : g ≫ i₃ = i₂ ≫ g') [Mono i₃] :
    Set.range (pullback.map f g f' g' i₁ i₂ i₃ e₁ e₂) =
      Set.range (pullback.snd i₁ (pullback.fst f' g')) ∩
        Set.range (pullback.snd i₂ (pullback.snd f' g')) := by
  rw [Scheme.Pullback.range_map, Scheme.Pullback.range_snd, Scheme.Pullback.range_snd]

set_option backward.isDefEq.respectTransparency false in
/-- A point of `B ×_S B` whose two projections lie in the image of a section `s` of
`b : B ⟶ S` lies on the diagonal. -/
lemma Scheme.Pullback.mem_range_diagonal_of_mem_range {B S : Scheme.{u}} {b : B ⟶ S}
    (s : S ⟶ B) (hs : s ≫ b = 𝟙 S) (u : ↑(pullback b b))
    (h₁ : pullback.fst b b u ∈ Set.range s) (h₂ : pullback.snd b b u ∈ Set.range s) :
    u ∈ Set.range (pullback.diagonal b) := by
  have hu : u ∈ Set.range (pullback.map (𝟙 S) (𝟙 S) b b s s (𝟙 S) (by simp [hs])
      (by simp [hs])) := by
    rw [Scheme.Pullback.range_map]
    exact ⟨h₁, h₂⟩
  obtain ⟨t, rfl⟩ := hu
  refine ⟨s (pullback.fst (𝟙 S) (𝟙 S) t), ?_⟩
  have : pullback.fst (𝟙 S) (𝟙 S) ≫ s ≫ pullback.diagonal b =
      pullback.map (𝟙 S) (𝟙 S) b b s s (𝟙 S) (by simp [hs]) (by simp [hs]) := by
    have := pullback.condition (f := 𝟙 S) (g := 𝟙 S)
    simp only [Category.comp_id] at this
    ext <;> simp [pullback.map, this]
  rw [← this]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- Let `b : B ⟶ Y` and `p : P ⟶ Y`, and write `B_P = B ×_Y P`. A point `u` of `B_P ×_P B_P`
lies on the diagonal of `B_P ⟶ P` if and only if its image in `B ×_Y B` lies on the diagonal of
`b`: the diagonal of `B_P ⟶ P` is the base change of the diagonal of `b`. -/
lemma Scheme.Pullback.map_fst_mem_range_diagonal_iff {B Y P : Scheme.{u}} (b : B ⟶ Y)
    (p : P ⟶ Y) (u : ↑(pullback (pullback.snd b p) (pullback.snd b p))) :
    pullback.map _ _ b b (pullback.fst b p) (pullback.fst b p) p pullback.condition.symm
        pullback.condition.symm u ∈ Set.range (pullback.diagonal b) ↔
      u ∈ Set.range (pullback.diagonal (pullback.snd b p)) := by
  constructor
  · rintro ⟨β, hβ⟩
    have e : pullback.map (𝟙 _ ≫ pullback.snd b p) (𝟙 _ ≫ pullback.snd b p) b b
        (𝟙 _ ≫ pullback.fst b p) (𝟙 _ ≫ pullback.fst b p) p
        (by simp [pullback.condition]) (by simp [pullback.condition]) =
        pullback.map _ _ b b (pullback.fst b p) (pullback.fst b p) p pullback.condition.symm
          pullback.condition.symm := by
      congr 1
    rw [← e] at hβ
    obtain ⟨t, -, rfl⟩ := Scheme.Pullback.exists_preimage_pullback _ _ hβ
    refine ⟨pullback.fst (𝟙 (pullback b p)) (𝟙 _)
      ((pullbackDiagonalMapIso b p (𝟙 _) (𝟙 _)).hom t), ?_⟩
    have : pullback.fst (𝟙 _) (𝟙 _) ≫ pullback.diagonal (pullback.snd b p) =
        (pullbackDiagonalMapIso b p (𝟙 _) (𝟙 _)).inv ≫ pullback.snd _ _ := by
      have := pullback.condition (f := 𝟙 (pullback b p)) (g := 𝟙 _)
      simp only [Category.comp_id] at this
      apply pullback.hom_ext
      · rw [Category.assoc, pullback.diagonal_fst, Category.comp_id, Category.assoc]
        exact (pullbackDiagonalMapIso.inv_snd_fst b p (𝟙 _) (𝟙 _)).symm
      · rw [Category.assoc, pullback.diagonal_snd, Category.comp_id, Category.assoc, this]
        exact (pullbackDiagonalMapIso.inv_snd_snd b p (𝟙 _) (𝟙 _)).symm
    rw [← Scheme.Hom.comp_apply, this, ← Scheme.Hom.comp_apply, Iso.hom_inv_id_assoc]
  · rintro ⟨β, rfl⟩
    refine ⟨pullback.fst b p β, ?_⟩
    have : pullback.fst b p ≫ pullback.diagonal b = pullback.diagonal (pullback.snd b p) ≫
        pullback.map _ _ b b (pullback.fst b p) (pullback.fst b p) p pullback.condition.symm
          pullback.condition.symm := by
      ext <;> simp
    rw [← Scheme.Hom.comp_apply, this, Scheme.Hom.comp_apply]

/-- **Surjectivity from nonempty geometric fibres.** A morphism `f : X ⟶ Y` such that the
fibre `X ×_Y Spec Ω` over every geometric point `Spec Ω ⟶ Y`, with `Ω` algebraically closed, is
nonempty is surjective: a point of the fibre over the geometric point
`Spec κ(y)ᵃˡᵍ ⟶ Spec κ(y) ⟶ Y` lies over `y`. No finiteness hypothesis on `f` is needed.
(blueprint: `lem-weil-pbc-surjective-nonempty-fibres`) -/
theorem Surjective.of_forall_nonempty_pullback (f : X ⟶ Y)
    (h : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (y : Spec (.of Ω) ⟶ Y),
      Nonempty ↥(pullback f y)) : Surjective f := by
  refine ⟨fun y ↦ ?_⟩
  set η : Spec (.of (AlgebraicClosure (Y.residueField y))) ⟶ Y :=
    Spec.map (CommRingCat.ofHom (algebraMap (Y.residueField y) (AlgebraicClosure _))) ≫
      Y.fromSpecResidueField y
  obtain ⟨z⟩ := h _ η
  refine ⟨pullback.fst f η z, ?_⟩
  rw [← Scheme.Hom.comp_apply, pullback.condition, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply]
  exact Scheme.fromSpecResidueField_apply (X := Y) y _

end AlgebraicGeometry
