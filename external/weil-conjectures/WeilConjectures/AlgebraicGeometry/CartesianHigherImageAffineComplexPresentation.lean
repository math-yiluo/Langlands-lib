/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.CartesianHigherImageTransitions
public import WeilConjectures.AlgebraicGeometry.AbelianHigherDirectImageClassCompatibility
public import WeilConjectures.AlgebraicGeometry.EtaleComplexCohomologyPresentationData
import WeilConjectures.AlgebraicGeometry.CofilteredAffineEtaleModel
import WeilConjectures.AlgebraicGeometry.CartesianHigherImageChartComparison
import WeilConjectures.AlgebraicGeometry.RestrictedOverAbelianCohomologyPresentation

/-! # Affine derived classes for cartesian higher images

Source: Stacks Project, Tag 0EYM, second proof, left vertical arrow.
-/

@[expose] public section

set_option backward.defeqAttrib.useBackward true

universe u

open CategoryTheory Limits Opposite
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale

namespace AlgebraicGeometry.Etale

noncomputable local instance localInst_CartesianHigherImageAffineComplexPresentation_1
    (T : Scheme.{u}) :
    HasShift (DerivedCategory.Plus (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1})) ℤ :=
  inferInstance

/-- Present affine cartesian derived classes by a qcqs scheme system and its
abelian complex cohomology cocone. The presentation has canonical transition and
leg equations, and contains no cohomology continuity or representative assertion.
Source: Stacks Project, Tag 0EYM, second proof, the square preceding part (1);
Tags 0EYL, 03Q8 and 09YQ.
(blueprint: lem-sc-cartesian-higher-image-affine-complex-presentation).

Proof: Descend U to an affine etale model V over a stage i using the cofiltered
model theorem. The actual over-category Over i is cofiltered. Pull the diagram
and cone back to X times_k S_i. The chart-system theorem supplies its limiting
cone, affine transitions and qcqs structure maps. Pull F to X times_k S_i and
apply the restricted-over abelian cohomology presentation, obtaining H, B and
canonical comparison and cone-leg equations. The chart comparison identifies
its apex cohomology with the limit derived Hom and gives compatible stage lifts.
Use J = Over i and a(j) = j.left, compose the apex isomorphisms, and combine the
chart comparison equation with the presentation's cone-leg equation. This is
an explicit assembly before invoking cohomology continuity.
No arbitrary witness or unproved existence theorem is used to define a sheaf,
functor, object or map. Empty test schemes and q=0 use the same constructions. -/
theorem exists_cartesianHigherImage_affine_complex_presentation
    {k : Type u} [Field k]
    {I : Type u} [SmallCategory I] [IsCofiltered I]
    (D : I ⥤ Over (Spec (.of k)))
    [∀ i, QuasiCompact (D.obj i).hom] [∀ i, QuasiSeparated (D.obj i).hom]
    [∀ {i j : I} (a : i ⟶ j), IsAffineHom (D.map a).left]
    (c : Cone D) (hc : IsLimit ((Over.forget _).mapCone c))
    [QuasiCompact c.pt.hom] [QuasiSeparated c.pt.hom]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [QuasiCompact f] [QuasiSeparated f]
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (q : ℕ) (U : c.pt.left.Etale) [IsAffine U.left]
    : ∃ (J : Type u) (_ : SmallCategory J) (_ : IsCofiltered J)
        (H : Jᵒᵖ ⥤ AddCommGrpCat.{u + 1}) (B : Cocone H)
        (a : J → I)
        (lift : ∀ j : J, H.obj (op j) →
          ((DerivedCategory.Plus.singleFunctor _ 0).obj
            ((abelianComparisonFree c.pt.left).obj U) ⟶
              ((D+(((c.π.app (a j)).left)^*[AddCommGrpCat.{u + 1}])).obj
                (cartesianDerivedImage f (D.obj (a j)).hom
                  ((DerivedCategory.Plus.singleFunctor _ 0).obj F)))⟦(q : ℤ)⟧))
        (e : B.pt ≅ AddCommGrpCat.of
          ((DerivedCategory.Plus.singleFunctor _ 0).obj
            ((abelianComparisonFree c.pt.left).obj U) ⟶
              (cartesianDerivedImage f c.pt.hom
                ((DerivedCategory.Plus.singleFunctor _ 0).obj F))⟦(q : ℤ)⟧)),
        EtaleComplexCohomologyPresentationData H B ∧
        ∀ (j : J) (x : H.obj (op j)),
          lift j x ≫ (shiftFunctor _ (q : ℤ)).map
            (cartesianDerivedImageMap f (D.obj (a j)).hom c.pt.hom
              (c.π.app (a j)).left (Over.w (c.π.app (a j))).symm
                ((DerivedCategory.Plus.singleFunctor _ 0).obj F)) =
            e.hom ((B.ι.app (op j)) x) := by
  classical
  let E := D ⋙ Over.forget (Spec (.of k))
  let d := (Over.forget (Spec (.of k))).mapCone c
  let (i : I) : CompactSpace (E.obj i) :=
    QuasiCompact.compactSpace_of_compactSpace (D.obj i).hom
  let (i : I) : QuasiSeparatedSpace (E.obj i) :=
    quasiSeparatedSpace_of_quasiSeparated (D.obj i).hom
  let (i j : I) (a : i ⟶ j) : IsAffineHom (E.map a) :=
    inferInstanceAs (IsAffineHom (D.map a).left)
  obtain ⟨i, V, hV, r, hr⟩ := Scheme.exists_affineEtale_model_of_cofiltered E d hc U
  let h := pullback.snd f (D.obj i).hom
  let Fᵢ := (upperStar AddCommGrpCat.{u + 1} (pullback.fst f (D.obj i).hom)).obj F
  let D' := cartesianChartDiagram f D i
  let c' := cartesianChartCone f D c i
  obtain ⟨⟨hc'⟩, ha, hqc, hqs, hqc₀, hqs₀⟩ := cartesianChartSystem_properties f D c hc i
  let {j l : Over i} (a : j ⟶ l) : IsAffineHom (D'.map a).left := ha a
  let (j : Over i) : QuasiCompact ((D'.obj j).hom ≫ h) := hqc j
  let (j : Over i) : QuasiSeparated ((D'.obj j).hom ≫ h) := hqs j
  let : QuasiCompact (c'.pt.hom ≫ h) := hqc₀
  let : QuasiSeparated (c'.pt.hom ≫ h) := hqs₀
  obtain ⟨H, B, eH, e₀, hB, hH, hleg⟩ :=
    exists_restrictedOverAbelian_cohomology_presentation h Fᵢ (q : ℤ) D' c' hc' V
  obtain ⟨e, lift, hcompat⟩ :=
    exists_cartesianChart_cohomology_comparison f D c F q i V U r hr
  refine ⟨Over i, inferInstance, inferInstance, H, B, fun j ↦ j.left,
    fun j x ↦ lift j ((eH j).hom x), e₀ ≪≫ e, hB, ?_⟩
  intro j x
  exact (hcompat j ((eH j).hom x)).trans
    (congrArg (fun z ↦ e.hom z) (ConcreteCategory.congr_hom (hleg j) x).symm)

end AlgebraicGeometry.Etale
