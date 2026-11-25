/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import WeilConjectures.AlgebraicGeometry.Morphisms.FiberDegree
public import WeilConjectures.AlgebraicGeometry.Sites.EtaleTopologicalInvariance.Coprod
public import WeilConjectures.AlgebraicGeometry.Sites.EtaleTopologicalInvariance.Cover
public import WeilConjectures.AlgebraicGeometry.Sites.EtaleTopologicalInvariance.Descent
public import WeilConjectures.AlgebraicGeometry.Sites.EtaleTopologicalInvariance.PropertyC
public import WeilConjectures.AlgebraicGeometry.Sites.EtaleTopologicalInvariance.Reduction
public import WeilConjectures.AlgebraicGeometry.Sites.EtaleTopologicalInvariance.Section

/-!
# Essential surjectivity of base change along a universal homeomorphism: the affine case

Let `f : X ⟶ Y` be a universal homeomorphism with `Y` quasi-affine and let `U ⟶ X` be an
affine étale morphism whose fibre degrees are bounded by `n`. We show by induction on `n`
that `U` is the base change of a quasi-affine étale `Y`-scheme, following the second proof
of [Stacks 04DZ]: an étale neighbourhood `W ⟶ Y` with a surjective `X`-morphism
`W ×_Y X ⟶ U` (property (C)) yields a section of `U ×_X W_X ⟶ W_X`, which splits off a
copy of `W_X`; the complement has fibre degrees bounded by `n - 1`, hence descends to `W`
by induction, and the resulting quasi-affine étale `W`-scheme descends to `Y` along the
étale cover `W ⟶ Y`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

namespace Scheme.Hom

/-- The statement proved by induction: for a universal homeomorphism `f : X ⟶ Y` with `Y`
quasi-affine, every affine étale `X`-scheme with fibre degrees bounded by `n` is the base
change of a quasi-affine étale `Y`-scheme. -/
def DescendsWithBound (n : ℕ) : Prop :=
  ∀ {X Y : Scheme.{u}} [Y.IsQuasiAffine] (f : X ⟶ Y) [IsUniversalHomeomorphism f]
    (U : X.Etale) [IsAffineHom U.hom], (∀ x, U.hom.fiberDegree x ≤ n) →
    ∃ V : Y.Etale, V.left.IsQuasiAffine ∧ Nonempty (f.Etale.obj V ≅ U)

/-- An empty étale `X`-scheme is the base change of the empty étale `Y`-scheme. -/
lemma exists_isQuasiAffine_iso_of_isEmpty {X Y : Scheme.{u}} (f : X ⟶ Y) (U : X.Etale)
    [IsEmpty U.left] : ∃ V : Y.Etale, V.left.IsQuasiAffine ∧ Nonempty (f.Etale.obj V ≅ U) := by
  have : IsEmpty (f.Etale.obj (Etale.mk (⊥ : Y.Opens).ι)).left := by
    constructor
    intro x
    exact (pullback.fst (⊥ : Y.Opens).ι f x).2
  have : IsEmpty (Etale.mk (⊥ : Y.Opens).ι).left := by
    constructor
    intro x
    exact x.2
  exact ⟨Etale.mk (⊥ : Y.Opens).ι, inferInstance, ⟨MorphismProperty.Over.isoMk
    (asIso (isInitialOfIsEmpty.to _)) (isInitialOfIsEmpty.hom_ext _ _)⟩⟩

lemma descendsWithBound_zero : DescendsWithBound.{u} 0 := by
  intro X Y _ f _ U _ hU
  have : IsEmpty U.left := U.hom.isEmpty_of_forall_fiberDegree_eq_zero
    fun x ↦ Nat.le_zero.mp (hU x)
  exact exists_isQuasiAffine_iso_of_isEmpty f U

section Step

variable {n : ℕ} (ih : DescendsWithBound.{u} n) {X Y : Scheme.{u}} [Y.IsQuasiAffine] (f : X ⟶ Y)
  [IsUniversalHomeomorphism f] (U : X.Etale) [IsAffineHom U.hom]

include ih in
/-- The inductive step in the case where `U ⟶ X` is surjective. -/
lemma step_of_surjective (hsurj : Function.Surjective U.hom)
    (hn : ∀ x, U.hom.fiberDegree x ≤ n + 1) :
    ∃ V : Y.Etale, V.left.IsQuasiAffine ∧ Nonempty (f.Etale.obj V ≅ U) := by
  classical
  have hX : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have : CompactSpace ((𝟭 Scheme).obj U.left) :=
    @QuasiCompact.compactSpace_of_compactSpace _ _ U.hom _ hX
  -- property (C): an affine étale `W ⟶ Y` with a surjective `X`-morphism `W ×_Y X ⟶ U`.
  obtain ⟨W, hW, p, hp, h, hhg, hh⟩ := exists_etale_surjective_of_forall f U.hom
    (fun u ↦ Scheme.Hom.exists_etale_hom_mem_range f U.hom u)
  have hpsurj : Surjective p := by
    constructor
    intro y
    obtain ⟨x, rfl⟩ := f.surjective y
    obtain ⟨u, rfl⟩ := hsurj x
    obtain ⟨w, rfl⟩ := hh u
    refine ⟨pullback.fst p f w, ?_⟩
    rw [← Scheme.Hom.comp_apply, pullback.condition, Scheme.Hom.comp_apply, ← hhg]
    rfl
  -- notation
  let π : pullback p f ⟶ W := pullback.fst p f
  let ρ : pullback p f ⟶ X := pullback.snd p f
  let U' : Scheme.{u} := pullback ρ U.hom
  let g' : U' ⟶ pullback p f := pullback.fst ρ U.hom
  -- the section of `g'` given by `h`
  let s : pullback p f ⟶ U' := pullback.lift (𝟙 _) h (by rw [Category.id_comp, hhg])
  have hs : s ≫ g' = 𝟙 _ := by simp [s, g']
  have : IsSeparated g' := IsSeparated.of_isAffineHom g'
  have hso : IsOpenImmersion s := IsOpenImmersion.of_section_of_etale g' s hs
  let R : U'.Opens := ⟨(Set.range s.base)ᶜ, isOpen_compl_range_of_section g' s hs⟩
  have hR : IsCompl s.opensRange R := isCompl_opensRange_of_section g' s hs
  have hR' : IsClosedImmersion R.ι := isClosedImmersion_ι_of_isCompl_right hR
  -- the fibre degrees of the complement are bounded by `n`.
  have hdeg : ∀ w, (R.ι ≫ g').fiberDegree w ≤ n := by
    intro w
    have h1 : g'.fiberDegree w = U.hom.fiberDegree (ρ w) :=
      U.hom.fiberDegree_of_isPullback (IsPullback.of_hasPullback ρ U.hom).flip w
    have h2 := g'.fiberDegree_of_isCompl w hR
    have h3 : (s.opensRange.ι ≫ g').fiberDegree w = 1 := by
      have : IsIso (s.opensRange.ι ≫ g') := by
        have : s.opensRange.ι ≫ g' = s.isoOpensRange.inv := by
          rw [← cancel_epi s.isoOpensRange.hom, Iso.hom_inv_id, ← Category.assoc,
            Scheme.Hom.isoOpensRange_hom_ι, hs]
        rw [this]
        infer_instance
      exact Scheme.Hom.fiberDegree_of_isIso _ w
    have := hn (ρ w)
    omega
  -- induction hypothesis applied to the complement over `W`.
  have hRa : IsAffineHom (Etale.mk (R.ι ≫ g')).hom := inferInstanceAs (IsAffineHom (R.ι ≫ g'))
  obtain ⟨V', hV', ⟨e'⟩⟩ := ih π (Etale.mk (R.ι ≫ g')) hdeg
  -- `V'' := W ⨿ V'`.
  have hV''e : AlgebraicGeometry.Etale (coprod.desc (𝟙 W) V'.hom) :=
    IsZariskiLocalAtSource.coprodDesc @AlgebraicGeometry.Etale inferInstance V'.prop
  let V'' : W.Etale := Etale.mk (coprod.desc (𝟙 W) V'.hom)
  have hV'' : V''.left.IsQuasiAffine := inferInstanceAs (W ⨿ V'.left).IsQuasiAffine
  -- the base change of `V''` to `W_X` is `U'`.
  obtain ⟨c₁⟩ := nonempty_isColimit_binaryCofan_pullbackCoprod (𝟙 W) V'.hom π
  obtain ⟨c₂⟩ := nonempty_isColimit_binaryCofanMk_of_isCompl s.opensRange.ι R.ι
    (by rwa [Scheme.Opens.opensRange_ι, Scheme.Opens.opensRange_ι])
  let i₁ : pullback (𝟙 W) π ≅ s.opensRange.toScheme :=
    asIso (pullback.snd (𝟙 W) π) ≪≫ s.isoOpensRange
  let i₂ : pullback V'.hom π ≅ R.toScheme :=
    (MorphismProperty.Over.forget _ _ _ ⋙ Over.forget _).mapIso e'
  let i : pullback (coprod.desc (𝟙 W) V'.hom) π ≅ U' :=
    c₁.coconePointsIsoOfNatIso c₂ (mapPairIso i₁ i₂)
  have hi : i.hom ≫ g' = pullback.snd (coprod.desc (𝟙 W) V'.hom) π := by
    apply c₁.hom_ext
    rintro ⟨(_ | _)⟩
    · rw [← Category.assoc, IsColimit.comp_coconePointsIsoOfNatIso_hom]
      change (i₁.hom ≫ s.opensRange.ι) ≫ g' =
        pullbackCoprodInl (𝟙 W) V'.hom π ≫ pullback.snd (coprod.desc (𝟙 W) V'.hom) π
      simp [i₁, hs, g']
    · rw [← Category.assoc, IsColimit.comp_coconePointsIsoOfNatIso_hom]
      change (i₂.hom ≫ R.ι) ≫ g' =
        pullbackCoprodInr (𝟙 W) V'.hom π ≫ pullback.snd (coprod.desc (𝟙 W) V'.hom) π
      have := MorphismProperty.Over.w e'.hom
      change i₂.hom ≫ R.ι ≫ g' = pullback.snd V'.hom π at this
      rw [Category.assoc, this]
      simp
  let e : π.Etale.obj V'' ≅ Etale.mk (pullback.fst ρ U.hom) :=
    MorphismProperty.Over.isoMk i hi
  exact exists_isQuasiAffine_etale_obj_iso_of_etale_cover p f U.hom V'' e

include ih in
/-- The inductive step. -/
lemma step (hn : ∀ x, U.hom.fiberDegree x ≤ n + 1) :
    ∃ V : Y.Etale, V.left.IsQuasiAffine ∧ Nonempty (f.Etale.obj V ≅ U) := by
  have hX : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have hUc : CompactSpace ((𝟭 Scheme).obj U.left) :=
    @QuasiCompact.compactSpace_of_compactSpace _ _ U.hom _ hX
  -- the open image of `U` in `Y`
  let Y₁ : Y.Opens := ⟨f.base '' Set.range U.hom.base,
    f.isHomeomorph.isOpenMap _ U.hom.isOpenMap.isOpen_range⟩
  have hrange : Set.range U.hom.base ⊆ Set.range (f ⁻¹ᵁ Y₁).ι.base := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨u, rfl⟩
    exact ⟨U.hom u, ⟨u, rfl⟩, rfl⟩
  let g₁ : U.left ⟶ f ⁻¹ᵁ Y₁ := IsOpenImmersion.lift (f ⁻¹ᵁ Y₁).ι U.hom hrange
  have hg₁ : g₁ ≫ (f ⁻¹ᵁ Y₁).ι = U.hom := IsOpenImmersion.lift_fac _ _ _
  have : AlgebraicGeometry.Etale (g₁ ≫ (f ⁻¹ᵁ Y₁).ι) := by rw [hg₁]; infer_instance
  have : AlgebraicGeometry.Etale g₁ := Etale.of_comp g₁ (f ⁻¹ᵁ Y₁).ι
  have : IsAffineHom (g₁ ≫ (f ⁻¹ᵁ Y₁).ι) := by rw [hg₁]; infer_instance
  have : IsAffineHom g₁ := IsAffineHom.of_comp g₁ (f ⁻¹ᵁ Y₁).ι
  have hsurj : Function.Surjective g₁ := by
    intro x₁
    obtain ⟨_, ⟨u, rfl⟩, hu⟩ := x₁.2
    refine ⟨u, (f ⁻¹ᵁ Y₁).ι.isOpenEmbedding.injective ?_⟩
    rw [← Scheme.Hom.comp_apply, hg₁]
    exact f.injective hu
  have hn₁ : ∀ x₁, g₁.fiberDegree x₁ ≤ n + 1 := fun x₁ ↦ by
    rw [U.hom.fiberDegree_of_isPullback (IsOpenImmersion.isPullback_lift_id _ _ hrange).flip x₁]
    exact hn _
  have : CompactSpace Y₁ := isCompact_iff_compactSpace.mp
    ((isCompact_range U.hom.continuous).image f.continuous)
  have : Y₁.toScheme.IsQuasiAffine := Scheme.IsQuasiAffine.of_isImmersion Y₁.ι
  have : IsAffineHom (Etale.mk g₁).hom := inferInstanceAs (IsAffineHom g₁)
  obtain ⟨V₁, hV₁, ⟨e₁⟩⟩ := step_of_surjective ih (f ∣_ Y₁) (Etale.mk g₁) hsurj hn₁
  refine ⟨(etaleOfOpens Y₁).obj V₁, hV₁, ⟨etaleObjEtaleOfOpensIso f Y₁ V₁ ≪≫
    (etaleOfRestrict f Y₁).mapIso e₁ ≪≫ MorphismProperty.Over.isoMk (Iso.refl _) ?_⟩⟩
  simpa using hg₁.symm

end Step

/-- **The affine case of the topological invariance of the small étale site**: for a universal
homeomorphism `f : X ⟶ Y` with `Y` quasi-affine, every affine étale `X`-scheme with bounded
fibre degrees is the base change of a quasi-affine étale `Y`-scheme. -/
theorem descendsWithBound (n : ℕ) : DescendsWithBound.{u} n := by
  induction n with
  | zero => exact descendsWithBound_zero
  | succ n ih =>
    intro X Y _ f _ U _ hn
    exact step ih f U hn

end Scheme.Hom

end AlgebraicGeometry
