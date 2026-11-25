/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Cohomology.FlatCohomologyComparison
import Mathlib.CategoryTheory.Adjunction.Unique

/-! # Sections of inverse images of locally split exact sequences

Source: `lem-pc-cech-cover-relative-effacement`, inverse-image splitting paragraph.
(blueprint: lem-pc-inverse-image-locally-split-sections)
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
namespace AlgebraicGeometry.Scheme.Modules
attribute [local instance] cohomologyHasSheafify cohomologyHasExt

/-- Composition compatibility, constructed by Mathlib adjunction uniqueness. -/
private noncomputable def pullbackCompIso {X Y Z : TopCat.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    TopCat.Sheaf.pullback AddCommGrpCat.{u} g ⋙ TopCat.Sheaf.pullback AddCommGrpCat.{u} f ≅
      TopCat.Sheaf.pullback AddCommGrpCat.{u} (f ≫ g) :=
  ((TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} g).comp
    (TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} f)).leftAdjointUniq
      (TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} (f ≫ g))

/-- A short exact sequence split on an open remains surjective on sections
of every open contained in its inverse image.
Source: `lem-pc-cech-cover-relative-effacement`, inverse-image splitting paragraph.
(blueprint: lem-pc-inverse-image-locally-split-sections)

Proof: Identify open restriction with inverse image along the open inclusion
using Mathlib `sheafPullbackIso`. Restriction preserves limits and, being a
left adjoint, colimits. Restrict the sequence to W. Its first arrow has a retraction, so exactness
supplies a splitting of the whole sequence. For B contained in g inverse-image W, construct the
continuous map B to W by b maps to g(b). Pull the splitting back along this map.
The canonical composition isomorphisms for
inverse image identify this sequence with the restriction of g inverse-image T
to B. The images of the splitting maps still satisfy the
splitting identities, since inverse image is additive and preserves composition.
Evaluate the resulting split epimorphism on the top open of B. Its image
in Y is exactly B, so evaluating the section of the quotient map gives
a right inverse of the displayed group homomorphism, hence surjectivity. This
also covers B empty and W empty, where the section groups of a sheaf are zero.
No covering hypothesis is used. -/
theorem inverseImage_surjective_sections_of_localSplit
    {X Y : Scheme.{u}} (g : Y ⟶ X)
    (T : ShortComplex (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}))
    (hT : T.ShortExact) (W : X.Opens)
    (hsplit : IsSplitMono (W.sheafRestrict.map T.f))
    (B : Y.Opens) (hB : B ≤ g ⁻¹ᵁ W) :
    Function.Surjective (((invImage g).map T.g).hom.app (op B)) := by
  classical
  let eW : TopCat.Sheaf.pullback AddCommGrpCat.{u} (Opens.inclusion' W) ≅
      W.sheafRestrict := W.isOpenEmbedding.sheafPullbackIso AddCommGrpCat.{u}
  have : (TopCat.Sheaf.pullback AddCommGrpCat.{u} (Opens.inclusion' W)).IsLeftAdjoint :=
    (TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u}
      (Opens.inclusion' W)).isLeftAdjoint
  have : (W.sheafRestrict (C := AddCommGrpCat.{u})).IsLeftAdjoint :=
    Functor.isLeftAdjoint_of_iso eW
  have : PreservesFiniteColimits (W.sheafRestrict (C := AddCommGrpCat.{u})) := inferInstance
  have := hsplit
  let TW := T.map W.sheafRestrict
  have hTW : TW.ShortExact := hT.map_of_exact W.sheafRestrict
  let sp := ShortComplex.Splitting.ofExactOfRetraction TW hTW.exact
    (retraction (W.sheafRestrict.map T.f)) (IsSplitMono.id (W.sheafRestrict.map T.f))
    hTW.epi_g
  have : IsSplitEpi (W.sheafRestrict.map T.g) := sp.isSplitEpi_g
  let p : TopCat.of B ⟶ TopCat.of W := TopCat.ofHom
    ⟨fun b ↦ ⟨g b.val, hB b.property⟩,
      (g.base.hom.continuous.comp continuous_subtype_val).subtype_mk _⟩
  have hp : p ≫ Opens.inclusion' W = Opens.inclusion' B ≫ g.base := rfl
  let eB : TopCat.Sheaf.pullback AddCommGrpCat.{u} (Opens.inclusion' B) ≅
      B.sheafRestrict := B.isOpenEmbedding.sheafPullbackIso AddCommGrpCat.{u}
  let P := TopCat.Sheaf.pullback AddCommGrpCat.{u} p
  let e : W.sheafRestrict ⋙ P ≅ invImage g ⋙ B.sheafRestrict :=
    Functor.isoWhiskerRight eW.symm P ≪≫ pullbackCompIso p (Opens.inclusion' W) ≪≫
      eqToIso (congrArg (TopCat.Sheaf.pullback AddCommGrpCat.{u}) hp) ≪≫
      (pullbackCompIso (Opens.inclusion' B) g.base).symm ≪≫
      Functor.isoWhiskerLeft (invImage g) eB
  have hmap : B.sheafRestrict.map ((invImage g).map T.g) =
      e.inv.app T.X₂ ≫ P.map (W.sheafRestrict.map T.g) ≫ e.hom.app T.X₃ := by
    change (invImage g ⋙ B.sheafRestrict).map T.g =
      e.inv.app T.X₂ ≫ (W.sheafRestrict ⋙ P).map T.g ≫ e.hom.app T.X₃
    rw [← e.inv.naturality_assoc]
    simp
  have : IsSplitEpi (B.sheafRestrict.map ((invImage g).map T.g)) := by
    rw [hmap]
    infer_instance
  have : Epi ((B.sheafRestrict.map ((invImage g).map T.g)).hom.app (op ⊤)) := by
    exact inferInstanceAs (Epi (((sheafToPresheaf _ _ ⋙
      (CategoryTheory.evaluation _ _).obj (op ⊤))).map
        (B.sheafRestrict.map ((invImage g).map T.g))))
  have he := (AddCommGrpCat.epi_iff_surjective
    ((B.sheafRestrict.map ((invImage g).map T.g)).hom.app (op ⊤))).mp inferInstance
  have htop : B.isOpenEmbedding.functor.obj ⊤ = B := by
    ext x
    change (∃ b : B, b ∈ (⊤ : Opens B) ∧ (b : Y) = x) ↔ x ∈ B
    constructor
    · rintro ⟨b, _, rfl⟩
      exact b.property
    · intro hx
      exact ⟨⟨x, hx⟩, trivial, rfl⟩
  change Function.Surjective (((invImage g).map T.g).hom.app
    (op (B.isOpenEmbedding.functor.obj ⊤))) at he
  rw [htop] at he
  exact he

end AlgebraicGeometry.Scheme.Modules
