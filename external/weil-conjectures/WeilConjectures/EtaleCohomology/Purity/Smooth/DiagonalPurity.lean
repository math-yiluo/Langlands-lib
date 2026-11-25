/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.AffineSpace.ZeroSection
public import WeilConjectures.AlgebraicGeometry.Morphisms.RegularImmersion
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Line
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.LineSmooth
public import WeilConjectures.EtaleCohomology.Purity.Smooth.SupportedTatePureLocal
public import WeilConjectures.EtaleCohomology.Purity.Smooth.ZeroSectionPurity
public import WeilConjectures.Mathlib.CategoryTheory.Limits.Shapes.Diagonal

/-!
# Purity for the zero section of the affine line and for the diagonal of the projective line

From relative purity for the zero section of `𝔸¹_B`
(`AlgebraicGeometry.Etale.isIso_supportedClassMap_kummerBoundary_coord_of_hasInvertibleExponent`)
we obtain the purity
hypothesis `AlgebraicGeometry.Etale.SupportedTatePure` of
`WeilConjectures.EtaleCohomology.Purity.Smooth.CartierKummerClass`:

* for the zero section of `𝔸¹_B` over every base `B`
  (`AlgebraicGeometry.Etale.supportedTatePure_zeroSection`);
* for the diagonal of `𝔸¹_S` over `S`, which the shear `(x, y) ↦ (x, x - y)` identifies with the
  zero section of `𝔸¹` over the first factor (`AlgebraicGeometry.AffineSpace.diagonalShear`);
* for the diagonal of any separated `S`-scheme covered by open charts isomorphic to `𝔸¹_S`
  (`AlgebraicGeometry.Etale.supportedTatePure_diagonal_of_cover`), as the hypothesis is local
  (`AlgebraicGeometry.Etale.SupportedTatePure.of_isOpenImmersion_cover`); in particular for the
  diagonal `Δ : ℙ¹_S ⟶ ℙ¹_S ×_S ℙ¹_S` of the projective line
  (`AlgebraicGeometry.Etale.supportedTatePure_diagonal_projectiveLine`), a regular immersion of
  codimension one, so that its cycle class `AlgebraicGeometry.Etale.cartierKummerClass` is
  defined.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

namespace AffineSpace

variable (n : Type u) (S : Scheme.{u})

set_option hygiene false in
/-- The first projection `𝔸(n; S) ×_S 𝔸(n; S) ⟶ 𝔸(n; S)`. -/
local notation "pr₁" => Limits.pullback.fst (𝔸(n; S) ↘ S) (𝔸(n; S) ↘ S)

set_option hygiene false in
/-- The second projection `𝔸(n; S) ×_S 𝔸(n; S) ⟶ 𝔸(n; S)`. -/
local notation "pr₂" => Limits.pullback.snd (𝔸(n; S) ↘ S) (𝔸(n; S) ↘ S)

/-- The *shear* `(x, y) ↦ (x, x - y)`, an isomorphism from `𝔸(n; S) ×_S 𝔸(n; S)` to affine
space `𝔸(n; 𝔸(n; S))` over the first factor. It maps the diagonal to the zero section
(`AlgebraicGeometry.AffineSpace.diagonal_diagonalShear`). -/
noncomputable def diagonalShear : pullback (𝔸(n; S) ↘ S) (𝔸(n; S) ↘ S) ⟶ 𝔸(n; 𝔸(n; S)) :=
  homOfVector pr₁ fun i ↦ (pr₁).appTop (coord S i) - (pr₂).appTop (coord S i)

/-- The inverse `(x, t) ↦ (x, x - t)` of the shear. -/
noncomputable def diagonalShearInv : 𝔸(n; 𝔸(n; S)) ⟶ pullback (𝔸(n; S) ↘ S) (𝔸(n; S) ↘ S) :=
  pullback.lift (𝔸(n; 𝔸(n; S)) ↘ 𝔸(n; S))
    (homOfVector (𝔸(n; 𝔸(n; S)) ↘ 𝔸(n; S) ≫ 𝔸(n; S) ↘ S) fun i ↦
      (𝔸(n; 𝔸(n; S)) ↘ 𝔸(n; S)).appTop (coord S i) - coord 𝔸(n; S) i) (by simp)

@[reassoc (attr := simp)]
lemma diagonalShear_over : diagonalShear n S ≫ 𝔸(n; 𝔸(n; S)) ↘ 𝔸(n; S) = pr₁ :=
  homOfVector_over _ _

@[simp]
lemma diagonalShear_appTop_coord (i : n) :
    (diagonalShear n S).appTop (coord 𝔸(n; S) i) =
      (pr₁).appTop (coord S i) - (pr₂).appTop (coord S i) :=
  homOfVector_appTop_coord _ _ _

@[reassoc (attr := simp)]
lemma diagonalShearInv_fst : diagonalShearInv n S ≫ pr₁ = 𝔸(n; 𝔸(n; S)) ↘ 𝔸(n; S) :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
lemma diagonalShearInv_snd : diagonalShearInv n S ≫ pr₂ =
    homOfVector (𝔸(n; 𝔸(n; S)) ↘ 𝔸(n; S) ≫ 𝔸(n; S) ↘ S) fun i ↦
      (𝔸(n; 𝔸(n; S)) ↘ 𝔸(n; S)).appTop (coord S i) - coord 𝔸(n; S) i :=
  pullback.lift_snd _ _ _

/-- `(f ≫ g)^* a = f^* (g^* a)` for global sections. -/
lemma appTop_comp_apply {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (a : Γ(Z, ⊤)) :
    (f ≫ g).appTop a = f.appTop (g.appTop a) := by
  rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply]

@[reassoc (attr := simp)]
lemma diagonalShear_diagonalShearInv : diagonalShear n S ≫ diagonalShearInv n S = 𝟙 _ := by
  refine pullback.hom_ext ?_ ?_
  · rw [Category.assoc, diagonalShearInv_fst, diagonalShear_over, Category.id_comp]
  · rw [Category.assoc, diagonalShearInv_snd, Category.id_comp]
    refine hom_ext ?_ fun i ↦ ?_
    · rw [Category.assoc, homOfVector_over, diagonalShear_over_assoc, pullback.condition]
    · rw [appTop_comp_apply, homOfVector_appTop_coord, map_sub, diagonalShear_appTop_coord,
        ← appTop_comp_apply, diagonalShear_over, sub_sub_cancel]

@[reassoc (attr := simp)]
lemma diagonalShearInv_diagonalShear : diagonalShearInv n S ≫ diagonalShear n S = 𝟙 _ := by
  refine hom_ext ?_ fun i ↦ ?_
  · rw [Category.assoc, diagonalShear_over, diagonalShearInv_fst, Category.id_comp]
  · rw [appTop_comp_apply, diagonalShear_appTop_coord, map_sub, ← appTop_comp_apply,
      ← appTop_comp_apply, diagonalShearInv_fst, diagonalShearInv_snd, homOfVector_appTop_coord,
      sub_sub_cancel, Scheme.Hom.id_appTop, CommRingCat.id_apply]

instance : IsIso (diagonalShear n S) :=
  ⟨diagonalShearInv n S, diagonalShear_diagonalShearInv n S, diagonalShearInv_diagonalShear n S⟩

/-- The shear maps the diagonal of `𝔸(n; S)` to the zero section of `𝔸(n; 𝔸(n; S))`. -/
@[reassoc (attr := simp)]
lemma diagonal_diagonalShear :
    pullback.diagonal (𝔸(n; S) ↘ S) ≫ diagonalShear n S = zeroSection n 𝔸(n; S) := by
  refine hom_ext ?_ fun i ↦ ?_
  · rw [Category.assoc, diagonalShear_over, pullback.diagonal_fst, zeroSection_over]
  · rw [appTop_comp_apply, diagonalShear_appTop_coord, map_sub, ← appTop_comp_apply,
      ← appTop_comp_apply, pullback.diagonal_fst, pullback.diagonal_snd, sub_self,
      zeroSection_appTop_coord]

/-- The zero section of `𝔸(n; S)` commutes with reindexing. -/
@[reassoc (attr := simp)]
lemma zeroSection_reindex {m : Type u} (f : m → n) :
    zeroSection n S ≫ reindex f S = zeroSection m S := by
  refine hom_ext ?_ fun i ↦ ?_
  · rw [Category.assoc, reindex_over, zeroSection_over, zeroSection_over]
  · rw [appTop_comp_apply, reindex_appTop_coord, zeroSection_appTop_coord,
      zeroSection_appTop_coord]

/-- Reindexing along a map between types with a single element is an isomorphism. -/
instance isIso_reindex_of_unique {m : Type u} [Unique n] [Unique m] (f : m → n) :
    IsIso (reindex f S) := by
  refine ⟨reindex (fun _ : n ↦ (default : m)) S, ?_, ?_⟩
  · refine hom_ext (by simp) fun i ↦ ?_
    rw [appTop_comp_apply, reindex_appTop_coord, reindex_appTop_coord, Scheme.Hom.id_appTop,
      CommRingCat.id_apply, Subsingleton.elim (f _) i]
  · refine hom_ext (by simp) fun i ↦ ?_
    rw [appTop_comp_apply, reindex_appTop_coord, reindex_appTop_coord, Scheme.Hom.id_appTop,
      CommRingCat.id_apply, Subsingleton.elim (default : m) i]

end AffineSpace

open Scheme

namespace Etale

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] [HasKummerClass Λ]
  [HasKummerClass.IsNormalized Λ]

/-- **Purity for the zero locus of the coordinate of `𝔸¹_B`**, over every base `B` on which the
exponent of `Λ` is invertible: `Rs^!(Λ(1)[2]) ≅ Λ_{V(t)}`
(`AlgebraicGeometry.Etale.isIso_supportedClassMap_kummerBoundary_coord_of_hasInvertibleExponent`).
-/
theorem supportedTatePure_zeroLocusSubschemeι_coord (B : Scheme.{u})
    [HasInvertibleExponent Λ B] :
    haveI : HasInvertibleExponent Λ 𝔸(ULift.{u} (Fin 1); B) := .of_hom (𝔸(ULift.{u} (Fin 1); B) ↘ B)
    SupportedTatePure Λ 1 (𝔸(ULift.{u} (Fin 1); B).zeroLocusSubschemeι
      {AffineSpace.coord B (ULift.up 0)}) := by
  have : HasInvertibleExponent Λ 𝔸(ULift.{u} (Fin 1); B) := .of_hom (𝔸(ULift.{u} (Fin 1); B) ↘ B)
  have := isIso_supportedClassMap_kummerBoundary_coord_of_hasInvertibleExponent Λ B
  exact supportedTatePure_of_iso_constantComplex Λ 1 _ (asIso (supportedClassMap Λ _
    (shiftSupportedClass Λ _ 2 (kummerBoundary Λ (AffineSpace.coord B (ULift.up 0)))))).symm

/-- **Purity for the zero section of `𝔸¹_B`**, for any one-element index type `n`, over every
base `B` on which the exponent of `Λ` is invertible. -/
theorem supportedTatePure_zeroSection (n : Type u) [Unique n] (B : Scheme.{u})
    [HasInvertibleExponent Λ B] :
    haveI : HasInvertibleExponent Λ 𝔸(n; B) := .of_hom (𝔸(n; B) ↘ B)
    SupportedTatePure Λ 1 (AffineSpace.zeroSection n B) := by
  have : HasInvertibleExponent Λ 𝔸(n; B) := .of_hom (𝔸(n; B) ↘ B)
  have : HasInvertibleExponent Λ 𝔸(ULift.{u} (Fin 1); B) := .of_hom (𝔸(ULift.{u} (Fin 1); B) ↘ B)
  have h₁ : SupportedTatePure Λ 1 (AffineSpace.zeroSection (ULift.{u} (Fin 1)) B) :=
    (supportedTatePure_zeroLocusSubschemeι_coord Λ B).of_etale (𝟙 _) _
      (AffineSpace.zeroSectionIsoZeroLocusSubscheme (ULift.{u} (Fin 1)) B
        (s := {AffineSpace.coord B (ULift.up 0)}) Set.range_unique).hom
      (IsPullback.of_horiz_isIso ⟨by simp⟩)
  exact h₁.of_etale (AffineSpace.reindex (fun _ : ULift.{u} (Fin 1) ↦ (default : n)) B) _ (𝟙 B)
    (IsPullback.of_horiz_isIso ⟨by simp⟩)

/-- **Purity for the diagonal of `𝔸¹_S`**: the shear identifies it with the zero section of
`𝔸¹` over the first factor (`AlgebraicGeometry.AffineSpace.diagonal_diagonalShear`). -/
theorem supportedTatePure_diagonal_affineSpace (n : Type u) [Unique n] (S : Scheme.{u})
    [HasInvertibleExponent Λ S] :
    haveI : HasInvertibleExponent Λ (pullback (𝔸(n; S) ↘ S) (𝔸(n; S) ↘ S)) :=
      .of_hom (pullback.fst _ _ ≫ 𝔸(n; S) ↘ S)
    SupportedTatePure Λ 1 (pullback.diagonal (𝔸(n; S) ↘ S)) := by
  have : HasInvertibleExponent Λ (pullback (𝔸(n; S) ↘ S) (𝔸(n; S) ↘ S)) :=
    .of_hom (pullback.fst _ _ ≫ 𝔸(n; S) ↘ S)
  have : HasInvertibleExponent Λ 𝔸(n; S) := .of_hom (𝔸(n; S) ↘ S)
  have : HasInvertibleExponent Λ 𝔸(n; 𝔸(n; S)) := .of_hom (𝔸(n; 𝔸(n; S)) ↘ 𝔸(n; S))
  exact (supportedTatePure_zeroSection Λ n 𝔸(n; S)).of_etale (AffineSpace.diagonalShear n S) _
    (𝟙 _) (IsPullback.of_horiz_isIso ⟨by simp⟩)

/-- **Purity for the diagonal of a scheme covered by affine lines.** Let `f : X ⟶ S` be
separated, and `c_a : 𝔸¹_S ⟶ X` open immersions over `S` covering `X`. Then the purity
hypothesis holds for the diagonal `X ⟶ X ×_S X`: on the open `𝔸¹_S ×_S 𝔸¹_S` of `X ×_S X` the
diagonal of `X` restricts to that of `𝔸¹_S`
(`AlgebraicGeometry.Etale.supportedTatePure_diagonal_affineSpace`). -/
theorem supportedTatePure_diagonal_of_cover (n : Type u) [Unique n] {X S : Scheme.{u}}
    (f : X ⟶ S) [IsSeparated f] [HasInvertibleExponent Λ S] {ι : Type u}
    (c : ι → (𝔸(n; S) ⟶ X)) [∀ a, IsOpenImmersion (c a)] (hc : ∀ a, c a ≫ f = 𝔸(n; S) ↘ S)
    (hcov : ∀ x : X, ∃ a y, (c a).base y = x) :
    haveI : HasInvertibleExponent Λ (pullback f f) := .of_hom (pullback.fst _ _ ≫ f)
    SupportedTatePure Λ 1 (pullback.diagonal f) := by
  have : HasInvertibleExponent Λ (pullback f f) := .of_hom (pullback.fst _ _ ≫ f)
  have : HasInvertibleExponent Λ (pullback (𝔸(n; S) ↘ S) (𝔸(n; S) ↘ S)) :=
    .of_hom (pullback.fst _ _ ≫ 𝔸(n; S) ↘ S)
  have hmap (a : ι) : IsOpenImmersion (pullback.map (𝔸(n; S) ↘ S) (𝔸(n; S) ↘ S) f f (c a) (c a)
      (𝟙 S) ((Category.comp_id _).trans (hc a).symm) ((Category.comp_id _).trans (hc a).symm)) :=
    MorphismProperty.pullbackMap (P := @IsOpenImmersion) inferInstance inferInstance
      (hc a).symm (hc a).symm
  refine SupportedTatePure.of_isOpenImmersion_cover (fun a ↦ pullback.map _ _ _ _ (c a) (c a)
    (𝟙 S) ((Category.comp_id _).trans (hc a).symm) ((Category.comp_id _).trans (hc a).symm))
    (fun _ ↦ pullback.diagonal (𝔸(n; S) ↘ S)) c
    (fun a ↦ isPullback_diagonal_map_of_mono (c a) (𝟙 S) ((Category.comp_id _).trans (hc a).symm))
    ?_ fun _ ↦ supportedTatePure_diagonal_affineSpace Λ n S
  rintro _ ⟨x, rfl⟩
  obtain ⟨a, y, rfl⟩ := hcov x
  refine Set.mem_iUnion.2 ⟨a, (pullback.diagonal (𝔸(n; S) ↘ S)).base y, ?_⟩
  rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply,
    (isPullback_diagonal_map_of_mono (c a) (𝟙 S)
      ((Category.comp_id _).trans (hc a).symm)).w]

/-- The diagonal `Δ : ℙ¹_S ⟶ ℙ¹_S ×_S ℙ¹_S` of the projective line is a regular immersion of
codimension one (`AlgebraicGeometry.isRegularImmersion_diagonal`), so that its cycle class
`AlgebraicGeometry.Etale.cartierKummerClass` is defined under the purity hypothesis
`AlgebraicGeometry.Etale.supportedTatePure_diagonal_projectiveLine`. -/
instance isRegularImmersion_diagonal_projectiveLine (S : Scheme.{u}) :
    IsRegularImmersion 1 (pullback.diagonal (ProjectiveLine S ↘ S)) :=
  isRegularImmersion_diagonal 1 _

/-- **Purity for the diagonal of the projective line** `Δ : ℙ¹_S ⟶ ℙ¹_S ×_S ℙ¹_S`, over every
base `S` on which the exponent of `Λ` is invertible: `ℙ¹_S` is covered by the two charts
`𝔸¹_S ⟶ ℙ¹_S` (`AlgebraicGeometry.Etale.supportedTatePure_diagonal_of_cover`). -/
theorem supportedTatePure_diagonal_projectiveLine (S : Scheme.{u}) [HasInvertibleExponent Λ S] :
    haveI : HasInvertibleExponent Λ (pullback (ProjectiveLine S ↘ S) (ProjectiveLine S ↘ S)) :=
      .of_hom (pullback.fst _ _ ≫ ProjectiveLine S ↘ S)
    SupportedTatePure Λ 1 (pullback.diagonal (ProjectiveLine S ↘ S)) := by
  have (a : ULift.{u} Bool) : IsOpenImmersion (bif a.down then ProjectiveLine.affineChart S
      else ProjectiveLine.infinityChart S) := by
    rcases a with ⟨_ | _⟩
    · exact inferInstanceAs (IsOpenImmersion (ProjectiveLine.infinityChart S))
    · exact inferInstanceAs (IsOpenImmersion (ProjectiveLine.affineChart S))
  refine supportedTatePure_diagonal_of_cover Λ PUnit.{u + 1} (ProjectiveLine S ↘ S)
    (ι := ULift.{u} Bool) (fun a ↦ bif a.down then ProjectiveLine.affineChart S
      else ProjectiveLine.infinityChart S) ?_ ?_
  · rintro ⟨_ | _⟩
    · exact ProjectiveLine.infinityChart_over
    · exact ProjectiveLine.affineChart_over S
  · intro x
    have hx : x ∈ (ProjectiveLine.affineChart S).opensRange ⊔
        (ProjectiveLine.infinityChart S).opensRange := by
      rw [ProjectiveLine.opensRange_affineChart_sup_opensRange_infinityChart]
      trivial
    rcases hx with ⟨y, hy⟩ | ⟨y, hy⟩
    · exact ⟨⟨true⟩, y, hy⟩
    · exact ⟨⟨false⟩, y, hy⟩

end Etale

end AlgebraicGeometry
