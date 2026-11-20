import Langlands.AbelianScheme.PolarizedFiniteLevel.ZariskiGluingCover
import Langlands.AbelianScheme.PolarizedFiniteLevel.LevelCoherence
import Langlands.AbelianScheme.KernelBaseChange

/-! # Gluing ordered torsion sections along the cover by small opens -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.AbelianScheme.PolarizedFiniteLevel.ZariskiGluing

open GroupScheme.Tate

variable {S : Scheme.{u}} {J : Type*} {U : J → S.Opens} (hU : iSup U = ⊤)
  {A : AbelianScheme S} {g n : ℕ}
  (w : ∀ W : SubOpens U, SectionTuple ((baseChange W.1.ι).obj A) g n)
  (hw : ∀ (W W' : SubOpens U) (h : W.1 ≤ W'.1) (i : Fin (2 * g)),
    (Additive.toMul (w W i)).val.left ≫ pullback.fst A.X.hom W.1.ι =
      S.homOfLE h ≫ (Additive.toMul (w W' i)).val.left ≫ pullback.fst A.X.hom W'.1.ι)

include hw in
theorem levelSection_compat (i : Fin (2 * g)) {W W' : (subCover hU).I₀} (h : W ⟶ W') :
    (subCover hU).trans h ≫ ((Additive.toMul (w W' i)).val.left ≫
        pullback.fst A.X.hom W'.1.ι) =
      (Additive.toMul (w W i)).val.left ≫ pullback.fst A.X.hom W.1.ι := by
  rw [subCover_trans]
  exact (hw W W' (leOfHom h) i).symm

/-- The glued underlying section. -/
def gluedTorsionSection (i : Fin (2 * g)) : S ⟶ A.X.left :=
  (subCover hU).glueMorphismsOfLocallyDirected
    (fun W => (Additive.toMul (w W i)).val.left ≫ pullback.fst A.X.hom W.1.ι)
    (levelSection_compat hU w hw i)

theorem gluedTorsionSection_restrict (i : Fin (2 * g)) (W : SubOpens U) :
    W.1.ι ≫ gluedTorsionSection hU w hw i =
      (Additive.toMul (w W i)).val.left ≫ pullback.fst A.X.hom W.1.ι :=
  (subCover hU).map_glueMorphismsOfLocallyDirected _ (levelSection_compat hU w hw i) W

theorem gluedTorsionSection_hom (i : Fin (2 * g)) : gluedTorsionSection hU w hw i ≫ A.X.hom = 𝟙 S := by
  apply (subCover hU).hom_ext
  intro W
  change W.1.ι ≫ _ = W.1.ι ≫ _
  have hs : (Additive.toMul (w W i)).val.left ≫ pullback.snd A.X.hom W.1.ι = 𝟙 _ :=
    (Additive.toMul (w W i)).val.w
  rw [← Category.assoc, gluedTorsionSection_restrict, Category.assoc, pullback.condition,
    ← Category.assoc, hs]
  exact (Category.id_comp _).trans (Category.comp_id _).symm

/-- The glued point of `A` over `S`. -/
def gluedPoint (i : Fin (2 * g)) : Over.mk (𝟙 S) ⟶ A.X :=
  Over.homMk (gluedTorsionSection hU w hw i) (gluedTorsionSection_hom hU w hw i)

/-- The inclusion of a small open, as a map of test schemes over `S`. -/
abbrev smallOpenPoint (W : SubOpens U) :
    (Over.map W.1.ι).obj (Over.mk (𝟙 W.1.toScheme)) ⟶ Over.mk (𝟙 S) :=
  Over.homMk W.1.ι (by simp)

theorem smallOpenPoint_gluedPoint (i : Fin (2 * g)) (W : SubOpens U) :
    smallOpenPoint W ≫ gluedPoint hU w hw i =
      GroupScheme.baseChangePointsEquiv W.1.ι A.toGrp (Over.mk (𝟙 W.1.toScheme))
        (Additive.toMul (w W i)).val := by
  apply Over.OverMorphism.ext
  rw [GroupScheme.baseChangePointsEquiv_left]
  exact gluedTorsionSection_restrict hU w hw i W

theorem gluedPoint_pow (i : Fin (2 * g)) : gluedPoint hU w hw i ^ n = 1 := by
  apply Over.OverMorphism.ext
  apply (subCover hU).hom_ext
  intro W
  change W.1.ι ≫ _ = W.1.ι ≫ _
  have h1 : (smallOpenPoint W ≫ gluedPoint hU w hw i ^ n).left =
      (smallOpenPoint W ≫ (1 : Over.mk (𝟙 S) ⟶ A.X)).left := by
    rw [MonObj.comp_pow, smallOpenPoint_gluedPoint, ← map_pow, MonObj.comp_one]
    have hy : (Additive.toMul (w W i)).val ^ n = 1 :=
      (mem_levelGroup _ _ n _).mp (Additive.toMul (w W i)).property
    rw [hy, map_one]
  exact h1

/-- The glued torsion point. -/
def gluedLevel (i : Fin (2 * g)) : Level A.toGrp (Over.mk (𝟙 S)) n :=
  Additive.ofMul ⟨gluedPoint hU w hw i, (mem_levelGroup _ _ n _).mpr (gluedPoint_pow hU w hw i)⟩

/-- The glued ordered tuple of torsion sections. -/
def gluedTuple : SectionTuple A g n := fun i => gluedLevel hU w hw i

/-- The glued tuple restricts to the given local tuples. -/
theorem pullbackTuple_gluedTuple (W : SubOpens U) :
    pullbackTuple W.1.ι (gluedTuple hU w hw) = w W := by
  funext i
  apply toSection_injective _ (Over.mk (𝟙 W.1.toScheme)) n
  change Additive.ofMul (Additive.toMul (pullbackTuple W.1.ι (gluedTuple hU w hw) i)).val =
    Additive.ofMul (Additive.toMul (w W i)).val
  congr 1
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · rw [pullbackTuple_fst]
    exact gluedTorsionSection_restrict hU w hw i W
  · have h1 : (Additive.toMul (pullbackTuple W.1.ι (gluedTuple hU w hw) i)).val.left ≫
        pullback.snd A.X.hom W.1.ι = 𝟙 _ :=
      (Additive.toMul (pullbackTuple W.1.ι (gluedTuple hU w hw) i)).val.w
    have h2 : (Additive.toMul (w W i)).val.left ≫ pullback.snd A.X.hom W.1.ι = 𝟙 _ :=
      (Additive.toMul (w W i)).val.w
    rw [h1, h2]

end Langlands.AbelianScheme.PolarizedFiniteLevel.ZariskiGluing
