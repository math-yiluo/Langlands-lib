import Langlands.AlgebraicGeometry.AlgebraicSpace.Basic
import Langlands.AlgebraicGeometry.PointTopology.AffineChartWeilRestrictionProduct
import Mathlib.CategoryTheory.Sites.Sheaf
import Mathlib.CategoryTheory.Limits.Shapes.DisjointCoproduct

/-!
# Sections over the factors of a finite product base

An fppf sheaf evaluates a scheme coproduct as a product. In particular,
sections on a scheme over a finite product ring are exactly the sections
on its pullbacks to the factors.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open _root_.AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

set_option backward.isDefEq.respectTransparency false

namespace FppfCoproduct

variable {S : Scheme.{u}} (F : FppfSheaf S)

/-- Sections on an empty test scheme form a subsingleton. -/
theorem subsingleton_sections (W : Over S) [IsEmpty W.left] :
    Subsingleton (F.obj.obj (op W)) := by
  have hb : (⊥ : Sieve W) ∈ fppfTopology S W := by
    rw [GrothendieckTopology.mem_over_iff, (Sieve.overEquiv W).map_bot]
    exact (Precoverage.toGrothendieck_mono
      Scheme.zariskiPrecoverage_le_fppfPrecoverage) _ W.left.bot_mem_grothendieckTopology
  let := Types.isTerminalEquivUnique _ (F.isTerminalOfBotCover W hb)
  infer_instance

variable {ι : Type u} (V : ι → Over S) (T : Over S) (j : ∀ i, V i ⟶ T)
  (hc : IsColimit (Cofan.mk T.left (fun i => (j i).left)))

include hc in
/-- Any actual scheme coproduct supplies an fppf covering family over the base. -/
theorem covering :
    Sieve.ofArrows V j ∈ fppfTopology S T := by
  have : IsIso (Sigma.desc (fun i => (j i).left)) :=
    (Cofan.nonempty_isColimit_iff_isIso_sigmaDesc _).mp ⟨hc⟩
  have hi : ∀ i, _root_.AlgebraicGeometry.IsOpenImmersion (j i).left := by
    intro i
    rw [← Sigma.ι_comp_desc (fun i => (j i).left) i]
    infer_instance
  let 𝒰 := Scheme.Cover.mkOfCovers
    (P := @_root_.AlgebraicGeometry.IsOpenImmersion.{u}) ι
    (fun i => (V i).left) (fun i => (j i).left) (fun x => by
      obtain ⟨y, hy⟩ := (asIso (Sigma.desc (fun i => (j i).left))).hom.homeomorph.surjective x
      obtain ⟨⟨i, z⟩, hz⟩ := (sigmaMk (fun i => (V i).left)).surjective y
      refine ⟨i, z, ?_⟩
      rw [← Sigma.ι_comp_desc (fun i => (j i).left) i, Scheme.Hom.comp_apply,
        ← sigmaMk_mk, hz]
      exact hy)
  rw [GrothendieckTopology.mem_over_iff, Sieve.overEquiv_ofArrows]
  exact (Precoverage.toGrothendieck_mono
    Scheme.zariskiPrecoverage_le_fppfPrecoverage) _ 𝒰.mem_grothendieckTopology

include hc in
/-- Every family of sections on the components of a scheme coproduct glues
uniquely. The fppf sheaf condition handles the empty overlaps. -/
theorem sections_bijective :
    Function.Bijective (fun x : F.obj.obj (op T) => fun i => F.obj.map (j i).op x) := by
  have hsh := (isSheaf_iff_isSheaf_of_type (fppfTopology S) F.obj).mp F.property
  have ha := (Presieve.isSheafFor_arrows_iff F.obj j).mp
    ((Presieve.isSheafFor_iff_generate (P := F.obj) (Presieve.ofArrows V j)).mpr
      (hsh _ (covering V T j hc)))
  rw [Function.bijective_iff_existsUnique]
  intro xs
  obtain ⟨x, hx, hu⟩ := ha xs (by
    intro i k W a b hab
    by_cases hik : i = k
    · subst k
      have hm : Mono ((Over.forget S).map (j i)) :=
        Mono.of_coproductDisjoint hc i
      have : Mono (j i) := (Over.forget S).mono_of_mono_map hm
      rw [(cancel_mono (j i)).mp hab]
    · have hinit : IsInitial W.left :=
        .ofCoproductDisjointOfCommSq hik hc a.left b.left
          (congrArg CommaMorphism.left hab)
      have : IsEmpty W.left := isInitial_iff_isEmpty.mp ⟨hinit⟩
      let := subsingleton_sections F W
      exact Subsingleton.elim _ _)
  exact ⟨x, funext hx, fun y hy => hu y (congrFun hy)⟩

/-- Evaluation of an fppf sheaf on an actual scheme coproduct. -/
def sectionsEquiv :
    F.obj.obj (op T) ≃ (∀ i, F.obj.obj (op (V i))) :=
  Equiv.ofBijective _ (sections_bijective F V T j hc)

end FppfCoproduct

namespace FiniteProductSections

open Langlands.AlgebraicGeometry.PointTopology

variable {ι : Type u} [Finite ι] (B : ι → Type u) [∀ i, CommRing (B i)]
  (T : Over (Spec (CommRingCat.of (∀ i, B i))))

/-- The pullback factor test, regarded again over the product base. -/
abbrev factor (i : ι) : Over (Spec (CommRingCat.of (∀ i, B i))) :=
  (Over.map (finiteProductSpecProjection B i)).obj
    ((Over.pullback (finiteProductSpecProjection B i)).obj T)

/-- The factor inclusion has the ordinary first pullback projection. -/
def inclusion (i : ι) : factor B T i ⟶ T :=
  Over.homMk (pullback.fst T.hom (finiteProductSpecProjection B i))
    pullback.condition

/-- Sections of an fppf sheaf over the product-base test are exactly its
sections over all factor tests. -/
def equiv (F : FppfSheaf (Spec (CommRingCat.of (∀ i, B i)))) :
    F.obj.obj (op T) ≃ (∀ i, F.obj.obj (op (factor B T i))) :=
  FppfCoproduct.sectionsEquiv F (factor B T) T (inclusion B T)
    (finiteProductPullbackCofanIsColimit B T)

@[simp]
theorem equiv_apply (F : FppfSheaf (Spec (CommRingCat.of (∀ i, B i))))
    (x : F.obj.obj (op T)) (i : ι) :
    equiv B T F x i = F.obj.map (inclusion B T i).op x :=
  rfl

omit [Finite ι] in
/-- The inclusions commute with every morphism of tests over the product base. -/
theorem inclusion_natural
    {U : Over (Spec (CommRingCat.of (∀ i, B i)))} (a : T ⟶ U) (i : ι) :
    (Over.map (finiteProductSpecProjection B i)).map
        ((Over.pullback (finiteProductSpecProjection B i)).map a) ≫ inclusion B U i =
      inclusion B T i ≫ a := by
  apply Over.OverMorphism.ext
  simp [inclusion, Over.pullback_map_left]

end FiniteProductSections

end Langlands.AlgebraicGeometry.AlgebraicSpace
