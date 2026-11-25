/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
public import WeilConjectures.AlgebraicGeometry.GroupScheme.Defs
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Cartesian.Grp

/-!
# The image of a homomorphism of group schemes

Let `f : G ⟶ H` be a homomorphism of group schemes over a field `K`, with `G` proper and `H`
separated of finite type. The scheme-theoretic image `f.left.image` of `f` is of finite type
over `K`, `f` maps `G` onto it, and it is a closed subgroup scheme of `H`.

Products over `K` of scheme-theoretically dominant morphisms are scheme-theoretically dominant,
since every `K`-scheme is flat over `K`. So the multiplication and inverse of `H`, restricted to
the image, still factor through the image; this makes the image a group object of
`Over (Spec K)` (`CategoryTheory.GrpObj.ofMono`).

## Main statements

- `AlgebraicGeometry.exists_isClosedSubgroupScheme_imageι`,
  `AlgebraicGeometry.exists_isMonHom_imageι`: the scheme-theoretic image of a homomorphism
  from a proper group scheme to a separated group scheme of finite type over a field is a
  closed subgroup scheme of finite type, onto which the homomorphism is surjective.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj

namespace AlgebraicGeometry

section Whisker

variable {S : Scheme.{u}}

/-- The product `g × Y : X ×_S Y ⟶ X' ×_S Y` of a quasi-compact scheme-theoretically dominant
morphism `g` with a flat `S`-scheme `Y` is scheme-theoretically dominant: it is the base change
of `g` along the flat projection `X' ×_S Y ⟶ X'`. -/
theorem isSchemeTheoreticallyDominant_whiskerRight_left {X X' : Over S} (g : X ⟶ X')
    [IsSchemeTheoreticallyDominant g.left] [QuasiCompact g.left] (Y : Over S) [Flat Y.hom] :
    IsSchemeTheoreticallyDominant (g ▷ Y).left := by
  have s : IsPullback ((g ▷ Y).left ≫ pullback.snd X'.hom Y.hom) (pullback.fst X.hom Y.hom)
      Y.hom (g.left ≫ X'.hom) := by
    rw [Over.whiskerRight_left_snd, Over.w g]
    exact (IsPullback.of_hasPullback X.hom Y.hom).flip
  exact .of_isPullback (IsPullback.of_right s (Over.whiskerRight_left_fst g)
    (IsPullback.of_hasPullback X'.hom Y.hom).flip).flip

/-- The product `X × g : X ×_S Y ⟶ X ×_S Y'` of a flat `S`-scheme `X` with a quasi-compact
scheme-theoretically dominant morphism `g` is scheme-theoretically dominant: it is the base
change of `g` along the flat projection `X ×_S Y' ⟶ Y'`. -/
theorem isSchemeTheoreticallyDominant_whiskerLeft_left {Y Y' : Over S} (g : Y ⟶ Y')
    [IsSchemeTheoreticallyDominant g.left] [QuasiCompact g.left] (X : Over S) [Flat X.hom] :
    IsSchemeTheoreticallyDominant (X ◁ g).left := by
  have s : IsPullback ((X ◁ g).left ≫ pullback.fst X.hom Y'.hom) (pullback.snd X.hom Y.hom)
      X.hom (g.left ≫ Y'.hom) := by
    rw [Over.whiskerLeft_left_fst, Over.w g]
    exact IsPullback.of_hasPullback X.hom Y.hom
  exact .of_isPullback (IsPullback.of_right s (Over.whiskerLeft_left_snd g)
    (IsPullback.of_hasPullback X.hom Y'.hom)).flip

end Whisker

variable {K : Type u} [Field K] {G H : Over (Spec (.of K))} [GrpObj G] [GrpObj H]

/-- Blueprint `lemma-connected-components-images-homomorphisms--2`: The image of a homomorphism is a
closed subgroup scheme.

Let `f : G ⟶ H` be a homomorphism of group schemes over a field `K`, with `G` proper and `H`
separated and of finite type over `K`. Then the scheme-theoretic image `Z` of `f` is of finite
type over `K`, the induced morphism `G ⟶ Z` is surjective, and `Z` is a closed subgroup scheme
of `H`: it carries a group structure for which the closed immersion `Z ⟶ H` is a homomorphism.

The morphism `f' : G ⟶ Z` is proper and dominant, hence surjective. It is
scheme-theoretically dominant, and so is `f' × f'`, every `K`-scheme being flat over `K`. Since
`(f' × f') ≫ (m_H ∘ (j × j)) = m_G ≫ f` factors through `j`, so does `m_H ∘ (j × j)`; similarly
for the inverse, and the unit `e_H = e_G ≫ f` factors through `j`. -/
theorem exists_isMonHom_imageι (f : G ⟶ H) [IsMonHom f] [IsProper G.hom] [IsSeparated H.hom]
    [LocallyOfFiniteType H.hom] :
    LocallyOfFiniteType (f.left.imageι ≫ H.hom) ∧ Surjective f.left.toImage ∧
      ∃ _ : GrpObj (Over.mk (f.left.imageι ≫ H.hom)),
        IsMonHom (Over.homMk f.left.imageι : Over.mk (f.left.imageι ≫ H.hom) ⟶ H) := by
  have : IsProper (f.left ≫ H.hom) := by rw [Over.w f]; infer_instance
  have : IsProper f.left := .of_comp f.left H.hom
  let Z := Over.mk (f.left.imageι ≫ H.hom)
  let j : Z ⟶ H := Over.homMk f.left.imageι
  let f' : G ⟶ Z := Over.homMk f.left.toImage (by simp [Z, Over.w f])
  have hf : f' ≫ j = f := Over.OverMorphism.ext f.left.toImage_imageι
  -- a morphism `g` to `H` which factors through `f` after a scheme-theoretically dominant `d`
  -- factors through the scheme-theoretic image of `f`
  have key {V W : Over (Spec (.of K))} (g : W ⟶ H) (d : V ⟶ W)
      [IsSchemeTheoreticallyDominant d.left] (c : V ⟶ G) (h : d ≫ g = c ≫ f) :
      ∃ l : W ⟶ Z, l ≫ j = g := by
    have hker : f.left.imageι.ker ≤ g.left.ker := by
      rw [← d.left.ker_comp_of_isSchemeTheoreticallyDominant, ← Over.comp_left, h,
        Scheme.IdealSheafData.ker_subschemeι]
      exact Scheme.Hom.le_ker_comp _ _
    exact ⟨Over.homMk (IsClosedImmersion.lift f.left.imageι g.left hker) (by
      simp only [Z, Over.mk_hom, IsClosedImmersion.lift_fac_assoc, Over.w g]),
      Over.OverMorphism.ext (IsClosedImmersion.lift_fac _ _ _)⟩
  have : IsSchemeTheoreticallyDominant f'.left :=
    inferInstanceAs (IsSchemeTheoreticallyDominant f.left.toImage)
  have : QuasiCompact f'.left := inferInstanceAs (QuasiCompact f.left.toImage)
  refine ⟨inferInstance, ?_, ?_⟩
  · have : IsProper (f.left.toImage ≫ f.left.imageι ≫ H.hom) := by
      rw [f.left.toImage_imageι_assoc, Over.w f]; infer_instance
    have : IsProper f.left.toImage := .of_comp _ (f.left.imageι ≫ H.hom)
    have := f.left.toImage.denseRange.closure_eq
    rw [f.left.toImage.isClosedMap.isClosed_range.closure_eq] at this
    exact ⟨Set.range_eq_univ.mp this⟩
  have hone : ∃ e : 𝟙_ _ ⟶ Z, e ≫ j = η[H] :=
    ⟨η[G] ≫ f', by rw [Category.assoc, hf, IsMonHom.one_hom]⟩
  have hinv : ∃ i : Z ⟶ Z, i ≫ j = j ≫ ι[H] := by
    have := GrpObj.inv_comp (𝟙 G) f
    simp only [CategoryTheory.Hom.inv_def, Category.id_comp] at this
    exact key _ f' ι[G] (by rw [reassoc_of% hf, this])
  have hmul : ∃ m : Z ⊗ Z ⟶ Z, m ≫ j = (j ⊗ₘ j) ≫ μ[H] := by
    have := isSchemeTheoreticallyDominant_whiskerRight_left f' G
    have := isSchemeTheoreticallyDominant_whiskerLeft_left f' Z
    have : IsSchemeTheoreticallyDominant (f' ⊗ₘ f').left := by
      rw [tensorHom_def, Over.comp_left]; infer_instance
    exact key _ (f' ⊗ₘ f') μ[G] (by rw [tensorHom_comp_tensorHom_assoc, hf, IsMonHom.mul_hom])
  exact ⟨GrpObj.ofMono j hone hmul hinv, GrpObj.isMonHom_ofMono j hone hmul hinv⟩


/-- Blueprint `lemma-connected-components-images-homomorphisms--2`: The image of a homomorphism is a
closed subgroup scheme.

Let `f : G ⟶ H` be a homomorphism of group schemes over a field `K`, with `G` proper and `H`
separated and of finite type over `K`. Then the scheme-theoretic image `Z` of `f` is of finite
type over `K` (locally of finite type and quasi-compact), the induced morphism `G ⟶ Z` is
surjective, and `Z ⟶ H` is a closed subgroup scheme.

This completes `AlgebraicGeometry.exists_isMonHom_imageι`: `Z` is quasi-compact as the image of
the quasi-compact `G`, and the closed immersion `Z ⟶ H` is a monomorphism, hence injective on
points. -/
theorem exists_isClosedSubgroupScheme_imageι (f : G ⟶ H) [IsMonHom f] [IsProper G.hom]
    [IsSeparated H.hom] [LocallyOfFiniteType H.hom] :
    LocallyOfFiniteType (f.left.imageι ≫ H.hom) ∧ QuasiCompact (f.left.imageι ≫ H.hom) ∧
      Surjective f.left.toImage ∧ ∃ _ : GrpObj (Over.mk (f.left.imageι ≫ H.hom)),
        IsClosedSubgroupScheme
          (Over.homMk f.left.imageι : Over.mk (f.left.imageι ≫ H.hom) ⟶ H) := by
  obtain ⟨h₁, h₂, inst, h₃⟩ := exists_isMonHom_imageι f
  refine ⟨h₁, ?_, h₂, inst, ?_⟩
  · have : CompactSpace G.left := QuasiCompact.compactSpace_of_compactSpace G.hom
    have : CompactSpace f.left.image := ⟨by
      rw [← Set.range_eq_univ.mpr h₂.surj]
      exact isCompact_range f.left.toImage.continuous⟩
    exact (HasAffineProperty.iff_of_isAffine (P := @QuasiCompact)).mpr this
  · have : Mono (Over.homMk f.left.imageι : Over.mk (f.left.imageι ≫ H.hom) ⟶ H) :=
      Over.mono_of_mono_left _
    exact { toIsSubgroupScheme := .of_mono _, isClosedImmersion := inferInstanceAs
      (IsClosedImmersion f.left.imageι) }

end AlgebraicGeometry
