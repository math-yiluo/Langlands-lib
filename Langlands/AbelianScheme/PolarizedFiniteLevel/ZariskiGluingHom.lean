import Langlands.AbelianScheme.PolarizedFiniteLevel.ZariskiGluingAbelian

/-! # Gluing homomorphisms of abelian schemes along the cover by small opens -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.AbelianScheme.PolarizedFiniteLevel.ZariskiGluing

open Langlands.AlgebraicGeometry.Picard

variable {S : Scheme.{u}} {J : Type*} {U : J → S.Opens} (hU : iSup U = ⊤)
  {A A' : AbelianScheme S}
  (loc : ∀ W : SubOpens U, (baseChange W.1.ι).obj A ⟶ (baseChange W.1.ι).obj A')
  (hloc : ∀ (W W' : SubOpens U) (h : W.1 ≤ W'.1),
    hom (loc W) ≫ pullback.map A'.X.hom W.1.ι A'.X.hom W'.1.ι (𝟙 _) (S.homOfLE h) (𝟙 _)
        (by simp) (by simp [Scheme.homOfLE_ι]) =
      pullback.map A.X.hom W.1.ι A.X.hom W'.1.ι (𝟙 _) (S.homOfLE h) (𝟙 _)
        (by simp) (by simp [Scheme.homOfLE_ι]) ≫ hom (loc W'))

/-- The cover of `A` by the preimages of the small opens. -/
abbrev homCover : A.X.left.OpenCover := (subCover hU).pullback₁ A.X.hom

include hloc in
theorem homCover_compat {W W' : (homCover hU (A := A)).I₀} (h : W ⟶ W') :
    (homCover hU).trans h ≫ (hom (loc W') ≫ pullback.fst A'.X.hom W'.1.ι) =
      hom (loc W) ≫ pullback.fst A'.X.hom W.1.ι := by
  have e : (homCover hU).trans h = pullback.map A.X.hom W.1.ι A.X.hom W'.1.ι (𝟙 _)
      (S.homOfLE (leOfHom h)) (𝟙 _) (by simp) (by simp [Scheme.homOfLE_ι]) := by
    apply pullback.hom_ext
    · erw [pullback.lift_fst]
    · erw [pullback.lift_snd]
  rw [e, ← Category.assoc, ← hloc W W' (leOfHom h), Category.assoc, pullback.lift_fst,
    Category.comp_id]

theorem homCover_w (W : (homCover hU (A := A)).I₀) :
    (hom (loc W) ≫ pullback.fst A'.X.hom W.1.ι) ≫ A'.X.hom =
      (homCover hU).f W ≫ A.X.hom := by
  have hw : hom (loc W) ≫ pullback.snd A'.X.hom W.1.ι = pullback.snd A.X.hom W.1.ι :=
    Over.w (groupHom (loc W)).hom.hom
  change _ = pullback.fst A.X.hom W.1.ι ≫ A.X.hom
  rw [Category.assoc, pullback.condition, ← Category.assoc, hw, pullback.condition]

/-- The glued morphism of underlying schemes over `S`. -/
def gluedHomOver : A.X ⟶ A'.X :=
  (homCover hU).glueMorphismsOverOfLocallyDirected
    (fun W => hom (loc W) ≫ pullback.fst A'.X.hom W.1.ι)
    (homCover_compat hU loc hloc) (homCover_w hU loc)

theorem fst_gluedHomOver_left (W : SubOpens U) :
    pullback.fst A.X.hom W.1.ι ≫ (gluedHomOver hU loc hloc).left =
      hom (loc W) ≫ pullback.fst A'.X.hom W.1.ι :=
  (homCover hU).map_glueMorphismsOverOfLocallyDirected_left _ (homCover_compat hU loc hloc)
    (homCover_w hU loc) W

theorem gluedHomOver_unit : η[A.X] ≫ gluedHomOver hU loc hloc = η[A'.X] := by
  apply Over.OverMorphism.ext
  apply (subCover hU).hom_ext
  intro W
  change W.1.ι ≫ η[A.X].left ≫ (gluedHomOver hU loc hloc).left = W.1.ι ≫ η[A'.X].left
  rw [← unitSection_eq_one_left, ← unitSection_eq_one_left, ← Category.assoc,
    ← unitSection_baseChange_fst, Category.assoc, fst_gluedHomOver_left, ← Category.assoc,
    unitSection_hom, unitSection_baseChange_fst]

/-- The glued homomorphism of abelian schemes. -/
def gluedHom : A ⟶ A' :=
  have := A'.smooth
  have := A'.proper
  have : IsMonHom (gluedHomOver hU loc hloc) := pointedMorphismRigidity S A.toGrp A'.toGrp
    (AbelianScheme.isAbelian A) inferInstance inferInstance inferInstance _
    (gluedHomOver_unit hU loc hloc)
  Additive.ofMul (Grp.homMk (gluedHomOver hU loc hloc))

theorem hom_gluedHom : hom (gluedHom hU loc hloc) = (gluedHomOver hU loc hloc).left := rfl

/-- The glued homomorphism restricts to the given local homomorphisms. -/
theorem baseChange_map_gluedHom (W : SubOpens U) :
    hom ((baseChange W.1.ι).map (gluedHom hU loc hloc)) = hom (loc W) := by
  apply pullback.hom_ext
  · rw [hom_baseChange_map_fst, hom_gluedHom, fst_gluedHomOver_left]
  · have hw : hom (loc W) ≫ pullback.snd A'.X.hom W.1.ι = pullback.snd A.X.hom W.1.ι :=
      Over.w (groupHom (loc W)).hom.hom
    have hw' : hom ((baseChange W.1.ι).map (gluedHom hU loc hloc)) ≫
        pullback.snd A'.X.hom W.1.ι = pullback.snd A.X.hom W.1.ι :=
      Over.w (groupHom ((baseChange W.1.ι).map (gluedHom hU loc hloc))).hom.hom
    rw [hw, hw']

end Langlands.AbelianScheme.PolarizedFiniteLevel.ZariskiGluing
