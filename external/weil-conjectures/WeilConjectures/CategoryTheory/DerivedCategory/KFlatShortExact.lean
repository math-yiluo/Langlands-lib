/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Homology.HomologySequenceLemmas
public import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel

/-!
# K-flatness and short exact sequences with flat quotient

Let `C` be a closed braided monoidal abelian category. We show:

* `CategoryTheory.ObjectProperty.mono_whiskerRight_of_shortExact`: if `0 ⟶ X₁ ⟶ X₂ ⟶ X₃ ⟶ 0`
  is short exact with `X₃` flat, then `X₁ ⊗ Z ⟶ X₂ ⊗ Z` is a monomorphism for every object
  `Z` (that is, `Tor₁(X₃, Z) = 0`), provided `Z` is a quotient of a flat object.
* `CategoryTheory.ObjectProperty.flat_of_shortExact`: in such a sequence, if moreover `X₂` is
  flat, so is `X₁`.
* `CochainComplex.kFlat_of_shortExact`: in a short exact sequence of complexes
  `0 ⟶ K₁ ⟶ K₂ ⟶ K₃ ⟶ 0` in which `K₁` and `K₂` are K-flat and the terms of `K₃` are flat,
  the complex `K₃` is K-flat (Stacks, Tag 064M?). The sequence stays short exact after
  tensoring with any complex, so this follows from the long exact homology sequence.
-/

@[expose] public section

open CategoryTheory Limits MonoidalCategory

universe w v u

namespace CategoryTheory.GradedObject

variable {I J : Type*} {C : Type*} [Category* C] {X Y : GradedObject I C} (φ : X ⟶ Y)
  (p : I → J) [X.HasMap p] [Y.HasMap p]

/-- The morphism `X.mapObj p j ⟶ Y.mapObj p j` induced by a family of monomorphisms is a
monomorphism, provided coproducts of monomorphisms indexed by the fibre `p ⁻¹' {j}` are
monomorphisms. -/
lemma mono_mapMap (j : J) [(MorphismProperty.monomorphisms C).IsStableUnderColimitsOfShape
      (Discrete (p ⁻¹' {j}))] (hφ : ∀ i, Mono (φ i)) :
    Mono (mapMap φ p j) :=
  MorphismProperty.IsStableUnderColimitsOfShape.condition
    (Discrete.functor (X.mapObjFun p j)) (Discrete.functor (Y.mapObjFun p j)) _ _
    (colimit.isColimit _) (colimit.isColimit _)
    (Discrete.natTrans fun i ↦ φ i.as.1) (fun i ↦ hφ i.as.1) (mapMap φ p j)
    (fun i ↦ ι_mapMap φ p i.as.1 j i.as.2)

end CategoryTheory.GradedObject

namespace CategoryTheory.ObjectProperty

variable {C : Type u} [Category.{v} C] [Abelian C] [MonoidalCategory C] [BraidedCategory C]
  [MonoidalClosed C] [MonoidalPreadditive C]

/-- **`Tor₁` against a flat quotient vanishes.** Let `0 ⟶ X₁ ⟶ X₂ ⟶ X₃ ⟶ 0` be short exact with
`X₃` flat, and let `Z` be a quotient `π : Q ⟶ Z` of a flat object `Q`. Then
`X₁ ⊗ Z ⟶ X₂ ⊗ Z` is a monomorphism. This is the usual diagram chase: tensor the sequence with
`0 ⟶ ker π ⟶ Q ⟶ Z ⟶ 0` and use that tensoring with `Q` or with `X₃` is exact. -/
lemma mono_whiskerRight_of_shortExact {S : ShortComplex C} (hS : S.ShortExact)
    (h₃ : flat S.X₃) {Q Z : C} (π : Q ⟶ Z) [Epi π] (hQ : flat Q) : Mono (S.f ▷ Z) := by
  have (F : C) : PreservesColimitsOfSize.{0, 0} (tensorRight F) :=
    preservesColimits_of_natIso (BraidedCategory.tensorLeftIsoTensorRight F)
  have := hS.mono_f
  have := hS.epi_g
  have := h₃.tensorLeft.preservesFiniteLimits
  have := hQ.tensorRight.preservesFiniteLimits
  have hK : (ShortComplex.mk (kernel.ι π) π (kernel.condition π)).Exact :=
    ShortComplex.exact_of_f_is_kernel _ (kernelIsKernel π)
  have hK₂ : (ShortComplex.mk (S.X₂ ◁ kernel.ι π) (S.X₂ ◁ π) (by
      rw [← MonoidalCategory.whiskerLeft_comp, kernel.condition,
        MonoidalPreadditive.whiskerLeft_zero])).Exact :=
    hK.map_of_epi_of_preservesCokernel (tensorLeft S.X₂) (by dsimp; infer_instance)
      inferInstance
  have hS₂ : (ShortComplex.mk (S.f ▷ kernel π) (S.g ▷ kernel π) (by
      rw [← comp_whiskerRight, S.zero, MonoidalPreadditive.zero_whiskerRight])).Exact :=
    hS.exact.map_of_epi_of_preservesCokernel (tensorRight _) hS.epi_g
      inferInstance
  have hmono₃ : Mono (S.X₃ ◁ kernel.ι π) := (tensorLeft S.X₃).map_mono (kernel.ι π)
  have hmonoQ : Mono (S.f ▷ Q) := (tensorRight Q).map_mono S.f
  have hπe : Epi (S.X₁ ◁ π) := (tensorLeft S.X₁).map_epi π
  refine Preadditive.mono_of_cancel_zero _ (fun {T} x hx ↦ ?_)
  -- lift `x` to `X₁ ⊗ Q`
  obtain ⟨T₁, π₁, _, y, hy⟩ := surjective_up_to_refinements_of_epi (S.X₁ ◁ π) x
  -- its image in `X₂ ⊗ Q` comes from `X₂ ⊗ ker π`
  obtain ⟨T₂, π₂, _, w, hw⟩ := hK₂.exact_up_to_refinements (y ≫ S.f ▷ Q) (by
    dsimp
    rw [Category.assoc, ← whisker_exchange, ← Category.assoc, ← hy, Category.assoc, hx,
      comp_zero])
  dsimp at hw
  -- that element dies in `X₃ ⊗ ker π`
  have hw₀ : w ≫ S.g ▷ kernel π = 0 := by
    rw [← cancel_mono (S.X₃ ◁ kernel.ι π), zero_comp, Category.assoc, ← whisker_exchange,
      ← Category.assoc, ← hw, Category.assoc, Category.assoc, ← comp_whiskerRight, S.zero,
      MonoidalPreadditive.zero_whiskerRight, comp_zero, comp_zero]
  -- so it comes from `X₁ ⊗ ker π`
  obtain ⟨T₃, π₃, _, v, hv⟩ := hS₂.exact_up_to_refinements w hw₀
  dsimp at hv
  have hyv : π₃ ≫ π₂ ≫ y = v ≫ S.X₁ ◁ kernel.ι π := by
    rw [← sub_eq_zero, ← cancel_mono (S.f ▷ Q), zero_comp, Preadditive.sub_comp,
      Category.assoc, Category.assoc, hw, ← Category.assoc, hv]
    simp [whisker_exchange]
  rw [← cancel_epi (π₃ ≫ π₂ ≫ π₁), comp_zero, Category.assoc, Category.assoc, hy,
    ← Category.assoc, ← Category.assoc, Category.assoc π₃, hyv, Category.assoc,
    ← MonoidalCategory.whiskerLeft_comp, kernel.condition, MonoidalPreadditive.whiskerLeft_zero,
    comp_zero]

variable [Abelian.HasFunctorialFlatResolution C]

/-- **`Tor₁` against a flat object vanishes.** If `0 ⟶ X₁ ⟶ X₂ ⟶ X₃ ⟶ 0` is short exact and
`X₃` is flat, then `X₁ ⊗ Z ⟶ X₂ ⊗ Z` is a monomorphism for every object `Z`. -/
lemma mono_whiskerRight_of_shortExact' {S : ShortComplex C} (hS : S.ShortExact)
    (h₃ : flat S.X₃) (Z : C) : Mono (S.f ▷ Z) := by
  let Λ := Classical.arbitrary (Abelian.LeftResolution (ObjectProperty.flat.ι : _ ⥤ C))
  exact mono_whiskerRight_of_shortExact hS h₃ (Λ.π.app Z) (Λ.F.obj Z).property

/-- The left handed version of
`CategoryTheory.ObjectProperty.mono_whiskerRight_of_shortExact'`. -/
lemma mono_whiskerLeft_of_shortExact {S : ShortComplex C} (hS : S.ShortExact)
    (h₃ : flat S.X₃) (Z : C) : Mono (Z ◁ S.f) := by
  have := mono_whiskerRight_of_shortExact' hS h₃ Z
  have h : Z ◁ S.f = (β_ S.X₁ Z).inv ≫ S.f ▷ Z ≫ (β_ S.X₂ Z).hom := by
    rw [BraidedCategory.braiding_naturality_left, Iso.inv_hom_id_assoc]
  rw [h]
  infer_instance

/-- **The kernel of an epimorphism between flat objects is flat.** -/
lemma flat_of_shortExact {S : ShortComplex C} (hS : S.ShortExact) (h₂ : flat S.X₂)
    (h₃ : flat S.X₃) : flat S.X₁ := by
  have := h₂.tensorLeft.preservesFiniteLimits
  rw [flat_iff_preservesFiniteLimits,
    Functor.preservesFiniteLimits_iff_forall_exact_map_and_mono]
  intro T hT
  have := hT.mono_f
  refine ⟨hT.exact.map_of_epi_of_preservesCokernel _ hT.epi_g inferInstance, ?_⟩
  have h₁ : Mono (S.f ▷ T.X₁) := mono_whiskerRight_of_shortExact' hS h₃ T.X₁
  have h₂' : Mono (S.X₂ ◁ T.f) := (tensorLeft S.X₂).map_mono T.f
  have : Mono (S.X₁ ◁ T.f ≫ S.f ▷ T.X₂) := by
    rw [whisker_exchange]
    infer_instance
  exact mono_of_mono (S.X₁ ◁ T.f) (S.f ▷ T.X₂)

end CategoryTheory.ObjectProperty

namespace CochainComplex

variable {C : Type u} [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{v} C]
  [MonoidalCategory C] [BraidedCategory C] [MonoidalClosed C] [MonoidalPreadditive C]

/-- If `f : K ⟶ L` is a morphism of complexes such that every `f^p ⊗ Z^q` is a monomorphism,
then so is `f ⊗ Z`: in each degree it is a coproduct of the `f^p ⊗ Z^q`. -/
lemma mono_whiskerRight_of_mono_f {K L : CochainComplex C ℤ} (f : K ⟶ L)
    (Z : CochainComplex C ℤ) (hf : ∀ p q, Mono (f.f p ▷ Z.X q)) : Mono (f ▷ Z) := by
  have : HasColimitsOfSize.{0, 0} C := hasColimitsOfSizeShrink C
  refine HomologicalComplex.mono_of_mono_f _ fun n ↦ ?_
  refine GradedObject.mono_mapMap _ _ n fun ⟨p, q⟩ ↦ ?_
  simpa using hf p q

/-- If `f : K ⟶ L` is a morphism of complexes such that every `Z^q ⊗ f^p` is a monomorphism,
then so is `Z ⊗ f`. -/
lemma mono_whiskerLeft_of_mono_f {K L : CochainComplex C ℤ} (f : K ⟶ L)
    (Z : CochainComplex C ℤ) (hf : ∀ p q, Mono (Z.X q ◁ f.f p)) : Mono (Z ◁ f) := by
  have : HasColimitsOfSize.{0, 0} C := hasColimitsOfSizeShrink C
  refine HomologicalComplex.mono_of_mono_f _ fun n ↦ ?_
  refine GradedObject.mono_mapMap _ _ n fun ⟨q, p⟩ ↦ ?_
  simpa using hf p q

variable [Abelian.HasFunctorialFlatResolution C]

/-- Tensoring a short exact sequence of complexes whose third term has flat terms with any
complex on the right gives a short exact sequence. -/
lemma shortExact_map_tensorRight {S : ShortComplex (CochainComplex C ℤ)} (hS : S.ShortExact)
    (h₃ : ∀ n, ObjectProperty.flat (S.X₃.X n)) (Z : CochainComplex C ℤ) :
    (S.map (tensorRight Z)).ShortExact := by
  have : HasColimitsOfSize.{0, 0} C := hasColimitsOfSizeShrink C
  have (F : C) : PreservesColimitsOfSize.{0, 0} (tensorRight F) :=
    preservesColimits_of_natIso (BraidedCategory.tensorLeftIsoTensorRight F)
  have : PreservesFiniteColimits (tensorRight Z) := ⟨fun J _ _ ↦
    inferInstanceAs (PreservesColimitsOfShape J
      ((Functor.map₂HomologicalComplex (curriedTensor C) (.up ℤ) (.up ℤ) (.up ℤ)).flip.obj Z))⟩
  have := hS.epi_g
  refine ShortComplex.ShortExact.mk' (hS.exact.map_of_epi_of_preservesCokernel _
    hS.epi_g inferInstance) ?_ ((tensorRight Z).map_epi S.g)
  refine mono_whiskerRight_of_mono_f _ _ fun p q ↦ ?_
  exact ObjectProperty.mono_whiskerRight_of_shortExact'
    (S := S.map (HomologicalComplex.eval _ _ p)) (hS.map_of_exact _) (h₃ p) (Z.X q)

/-- Tensoring a short exact sequence of complexes whose third term has flat terms with any
complex on the left gives a short exact sequence. -/
lemma shortExact_map_tensorLeft {S : ShortComplex (CochainComplex C ℤ)} (hS : S.ShortExact)
    (h₃ : ∀ n, ObjectProperty.flat (S.X₃.X n)) (Z : CochainComplex C ℤ) :
    (S.map (tensorLeft Z)).ShortExact := by
  have : HasColimitsOfSize.{0, 0} C := hasColimitsOfSizeShrink C
  have : PreservesFiniteColimits (tensorLeft Z) := ⟨fun J _ _ ↦
    inferInstanceAs (PreservesColimitsOfShape J
      ((Functor.map₂HomologicalComplex (curriedTensor C) (.up ℤ) (.up ℤ) (.up ℤ)).obj Z))⟩
  have := hS.epi_g
  refine ShortComplex.ShortExact.mk' (hS.exact.map_of_epi_of_preservesCokernel _
    hS.epi_g inferInstance) ?_ ((tensorLeft Z).map_epi S.g)
  refine mono_whiskerLeft_of_mono_f _ _ fun p q ↦ ?_
  exact ObjectProperty.mono_whiskerLeft_of_shortExact
    (S := S.map (HomologicalComplex.eval _ _ p)) (hS.map_of_exact _) (h₃ p) (Z.X q)

/-- **Two out of three for K-flatness with a flat quotient.** Let `0 ⟶ K₁ ⟶ K₂ ⟶ K₃ ⟶ 0` be a
short exact sequence of complexes in which `K₁` and `K₂` are K-flat and the terms of `K₃` are
flat. Then `K₃` is K-flat: for a quasi-isomorphism `Z ⟶ Z'`, the sequences `K• ⊗ Z` and
`K• ⊗ Z'` are short exact, and the five lemma for the long exact homology sequences applies. -/
lemma kFlat_of_shortExact {S : ShortComplex (CochainComplex C ℤ)} (hS : S.ShortExact)
    (h₁ : (HomologicalComplex.quasiIso C (.up ℤ)).kFlat S.X₁)
    (h₂ : (HomologicalComplex.quasiIso C (.up ℤ)).kFlat S.X₂)
    (h₃ : ∀ n, ObjectProperty.flat (S.X₃.X n)) :
    (HomologicalComplex.quasiIso C (.up ℤ)).kFlat S.X₃ := by
  rw [kFlat_iff_preservesQuasiIso]
  constructor
  · intro Z Z' φ hφ
    rw [MorphismProperty.inverseImage_iff, HomologicalComplex.mem_quasiIso_iff]
    have hτ₁ := h₁.1 φ hφ
    have hτ₂ := h₂.1 φ hφ
    rw [MorphismProperty.inverseImage_iff, HomologicalComplex.mem_quasiIso_iff] at hτ₁ hτ₂
    exact HomologicalComplex.HomologySequence.quasiIso_τ₃
      (S.mapNatTrans ((curriedTensor (CochainComplex C ℤ)).flip.map φ))
      (shortExact_map_tensorRight hS h₃ Z) (shortExact_map_tensorRight hS h₃ Z') hτ₁ hτ₂
  · intro Z Z' φ hφ
    rw [MorphismProperty.inverseImage_iff, HomologicalComplex.mem_quasiIso_iff]
    have hτ₁ := h₁.2 φ hφ
    have hτ₂ := h₂.2 φ hφ
    rw [MorphismProperty.inverseImage_iff, HomologicalComplex.mem_quasiIso_iff] at hτ₁ hτ₂
    exact HomologicalComplex.HomologySequence.quasiIso_τ₃
      (S.mapNatTrans ((curriedTensor (CochainComplex C ℤ)).map φ))
      (shortExact_map_tensorLeft hS h₃ Z) (shortExact_map_tensorLeft hS h₃ Z') hτ₁ hτ₂

end CochainComplex
