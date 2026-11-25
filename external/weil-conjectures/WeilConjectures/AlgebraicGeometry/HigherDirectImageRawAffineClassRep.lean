/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.AbelianHigherDirectImageNaturalComparison
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Coherence
import WeilConjectures.AlgebraicGeometry.EtaleComplexClassDescent
import WeilConjectures.AlgebraicGeometry.HigherDirectImageRawAffineComplexPresentation

/-! # Raw affine cohomology classes descend to a stage

Source: Stacks Project, Tags 09Z1 and 0EZM.
(blueprint: lem-sbc-higher-direct-image-raw-affine-class-rep).
-/

@[expose] public section

universe v
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale

namespace AlgebraicGeometry.Etale

/-- Every raw restricted-cohomology class over an affine etale object is a
pullback of a raw class at one stage. This assertion concerns derived Hom only;
no higher-direct-image sheaf or choice of sheafification comparison occurs.
Source: Stacks Project, Tag 09Z1, the displayed cohomology colimit in the proof;
Tag 0EZM, specialized to degree-zero complexes with common lower bound zero.
(blueprint: lem-sbc-higher-direct-image-raw-affine-class-rep).

Proof: Fix the affine etale U over S. Base change the underlying scheme diagram
and its limiting cone along U.hom. Each stage U times_S X_i is qcqs because its
map to the affine scheme U is the base change of the qcqs structure map X_i → S.
The transition maps are affine by base change. The base-changed cone is limiting
by the universal property of pullbacks. Pull back F_i and the transition maps to
these schemes. The identity and composition conditions transport along the
pullback composition isomorphisms. At the limit, composition of inverse images
identifies the pulled-back H diagram with the pullbacks of these stage sheaves;
hH gives its transition equations. Since inverse image is a left adjoint it
preserves the colimit, so its colimit is the restriction of colimit H.
Put this system of sheaves into single complexes in degree zero. Exact inverse
image commutes with single complexes, and their common lower bound is zero.
Apply nonempty_isColimit_etale_complex_cohomology to this system. Its
cohomology cocone is a filtered colimit; the forgetful functor from abelian groups
preserves it, so every class has a representative at one stage. Identify the
cohomology of U times_S X_i with derived Hom from the inverse image of the free
abelian sheaf of U, and likewise at the limit. This identification follows from
the free-sheaf sections adjunction and etale restriction (restriction has an
exact left adjoint, so preserves injectives). In D⁺ the Hom groups of the single
complexes compute the same cohomology as in the unbounded derived category.
Naturality identifies the cocone leg with pullback of the class followed by
its shifted coefficient map. The factors are precisely the composition,
single-functor, and shift comparisons in abelianHigherDirectImageRawPullback.
Transport the stage representative through these identifications to obtain t.
This proves the asserted equality without any sheafification or gluing. -/
theorem exists_higherDirectImage_raw_affine_class_rep {S : Scheme.{v}}
    {I : Type v} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
    (D : Iᵒᵖ ⥤ Over S)
    [∀ {i j : Iᵒᵖ} (f : i ⟶ j), IsAffineHom (D.map f).left]
    [∀ i : Iᵒᵖ, QuasiCompact (D.obj i).hom]
    [∀ i : Iᵒᵖ, QuasiSeparated (D.obj i).hom]
    (c : Cone D) (hc : IsLimit ((Over.forget S).mapCone c))
    [QuasiCompact c.pt.hom] [QuasiSeparated c.pt.hom]
    (F : ∀ i : I, Sheaf (D.obj (op i)).left.smallEtaleTopology AddCommGrpCat.{v + 1})
    (φ : ∀ {i j : I} (f : i ⟶ j),
      (((D.map f.op).left)^*[AddCommGrpCat.{v + 1}]).obj (F i) ⟶ F j)
    (hφid : ∀ i : I, HEq (φ (𝟙 i))
      ((upperStarId AddCommGrpCat.{v + 1} (D.obj (op i)).left).hom.app (F i)))
    (hφcomp : ∀ {i j k : I} (f : i ⟶ j) (g : j ⟶ k), HEq (φ (f ≫ g))
      ((upperStarComp AddCommGrpCat.{v + 1} (D.map g.op).left
          (D.map f.op).left).hom.app (F i) ≫
        (((D.map g.op).left)^*[AddCommGrpCat.{v + 1}]).map (φ f) ≫ φ g))
    (H : I ⥤ Sheaf c.pt.left.smallEtaleTopology AddCommGrpCat.{v + 1})
    (eH : ∀ i : I, H.obj i ≅
      (((c.π.app (op i)).left)^*[AddCommGrpCat.{v + 1}]).obj (F i))
    (hH : ∀ {i j : I} (f : i ⟶ j), H.map f =
      (eH i).hom ≫
        (upperStarComp AddCommGrpCat.{v + 1} (c.π.app (op j)).left (D.map f.op).left
          (c.π.app (op i)).left
          (congrArg (fun t => t.left) (c.w f.op)).symm).hom.app (F i) ≫
        (((c.π.app (op j)).left)^*[AddCommGrpCat.{v + 1}]).map (φ f) ≫ (eH j).inv)
    [HasColimit H] (p : ℕ) :
    ∀ (U : S.Etale) [IsAffine U.left]
      (z : (abelianHigherDirectImageRawPresheaf c.pt.hom p (colimit H)).obj (op U)),
      ∃ (i : I)
        (t : (abelianHigherDirectImageRawPresheaf (D.obj (op i)).hom p (F i)).obj (op U)),
        abelianHigherDirectImageRawPullback (c.π.app (op i)).left
          (D.obj (op i)).hom c.pt.hom (Over.w (c.π.app (op i))) p (F i)
          (colimit H) ((eH i).inv ≫ colimit.ι H i) U t = z := by
  classical
  intro U _ z
  obtain ⟨D', c', hc', compact, quasiSeparated, affine, F', φ', hid, hcomp, a,
      hbelow, G, eG, hG, P, hP, K, eK, hK, L, hL, B, eB, hB, stageIso, limitIso,
      compatibility⟩ := exists_raw_affine_complex_presentation
    D c hc F φ hφid hφcomp H eH hH p U
  have : ∀ i, CompactSpace (D'.obj i) := compact
  have : ∀ i, QuasiSeparatedSpace (D'.obj i) := quasiSeparated
  have : ∀ (i j : Iᵒᵖ) (f : i ⟶ j), IsAffineHom (D'.map f) := affine
  obtain ⟨i, y, hy⟩ := exists_etale_complex_class_rep
    D' c' hc' F' φ' hid hcomp a hbelow
    G eG hG (p : ℤ) P hP K eK hK L hL B eB hB (limitIso.hom z)
  let t := (stageIso (op i)).inv y
  refine ⟨i.unop, t, ?_⟩
  have ht : (stageIso (op i)).hom t = y := by
    exact ConcreteCategory.congr_hom (stageIso (op i)).inv_hom_id y
  have hz := compatibility (op i) t
  rw [ht] at hz
  have he : limitIso.hom
      (abelianHigherDirectImageRawPullback (c.π.app (op i.unop)).left
        (D.obj (op i.unop)).hom c.pt.hom (Over.w (c.π.app (op i.unop))) p
        (F i.unop) (colimit H)
        ((eH i.unop).inv ≫ colimit.ι H i.unop) U t) = limitIso.hom z :=
    hz.symm.trans hy
  exact (ConcreteCategory.bijective_of_isIso limitIso.hom).1 he

end AlgebraicGeometry.Etale
