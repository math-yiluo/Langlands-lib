/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.GrothendieckHypercoverCohomology
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import WeilConjectures.AlgebraicGeometry.GrothendieckHypercoverStageMaps
import WeilConjectures.AlgebraicGeometry.GrothendieckHypercoverSectionColimit
import WeilConjectures.AlgebraicGeometry.FiniteSplitHypercoverSkeletonDescent
import WeilConjectures.CategoryTheory.DerivedCategory.DegreewiseLimits

/-! # Finite cochain descent generates limit hypercover cohomology -/

@[expose] public section

universe u' u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.FiniteSplitEtaleHypercover

variable (A : Type u') [Category.{u + 1} A] [Abelian A]
  [IsGrothendieckAbelian.{u + 1} A]

private theorem filteredShortComplex_hom_ext
    {J : Type u} [SmallCategory J] [IsFiltered J]
    (K : J ⥤ ShortComplex A) (s : Cocone K)
    (h₁ : IsColimit (ShortComplex.π₁.mapCocone s))
    (h₂ : IsColimit (ShortComplex.π₂.mapCocone s))
    (h₃ : IsColimit (ShortComplex.π₃.mapCocone s))
    {B : A} (f g : s.pt.homology ⟶ B)
    (h : ∀ j, ShortComplex.homologyMap (s.ι.app j) ≫ f =
      ShortComplex.homologyMap (s.ι.app j) ≫ g) : f = g := by
  let : HasColimitsOfSize.{u, u} A :=
    hasColimitsOfSizeShrink.{u, u, u + 1, u + 1} A
  let : AB5OfSize.{u, u} A := AB5OfSize_of_univLE A
  have hs : IsColimit s := ShortComplex.isColimitOfIsColimitπ s h₁ h₂ h₃
  exact (isColimitOfPreserves (ShortComplex.homologyFunctor A) hs).hom_ext h


/-- Stage hypercover cohomology objects jointly generate the limit object.
This statement concerns alternating cochain complexes and their colimits only;
it makes no reference to injective resolutions or derived sections.
Source: blueprint corollary-cohomology-pro-etale-affine and the finite-cochain
argument of corollary-cohomology-pro-etale-affine, steps 2–4.
(auxiliary; not a blueprint node).

Proof: pull a finite split hypercover at a stage to the limit. Base change preserves
its splitting, finite coproduct decomposition and matching covers. The inverse-image
unit gives a map of its section complexes and hence a map from stage hypercover
cohomology to limit hypercover cohomology, compatible with refinements. For a fixed
q, the cohomology of a hypercover section complex depends only on degrees through
q + 1. Descend that finite truncation to a stage using finite hypercover descent;
extend its truncation there by successively choosing finite covers of matching
objects. Sections of an inverse-image sheaf on a descended qcqs etale object are
the filtered colimit of the stage section objects. This is the coherent-site
inverse-image formula: choose finite covers, express the sheaf condition by finite
equalizers, and commute those equalizers with filtered colimits using AB5. The
formula applies to the finitely many terms and differentials of the truncation.
AB5 again identifies their cohomology with the filtered colimit of the cohomologies.
Consequently the canonical stage-to-limit maps are jointly epic on every summand
of the hypercover colimit. The colimit injections are jointly epic, so these maps
are jointly epic on the whole limit object, proving the claimed cancellation.
This works also at q = 0; cofilteredness supplies a stage, and the empty scheme has
zero section objects. -/
theorem hypercoverCohomology_limit_hom_ext
    {S : Scheme.{u}} (F : Sheaf S.smallEtaleTopology A)
    {I : Type u} [SmallCategory I] [IsCofiltered I] (D : I ⥤ Over S)
    [∀ i, CompactSpace (D.obj i).left]
    [∀ i, QuasiSeparatedSpace (D.obj i).left]
    [∀ {i j} (g : i ⟶ j), IsAffineHom (D.map g).left]
    (c : Cone D) [CompactSpace c.pt.left] [QuasiSeparatedSpace c.pt.left]
    (hc : IsLimit ((Over.forget S).mapCone c)) (q : ℕ)
    (B : A)
    (f g : hypercoverCohomology A ((Etale.upperStar A c.pt.hom).obj F) q ⟶ B)
    (h : ∀ i : I,
      coneHypercoverMap A D c F q i ≫ f = coneHypercoverMap A D c F q i ≫ g) :
    f = g := by
  let : HasColimitsOfSize.{u, u + 1} A :=
    hasColimitsOfSizeShrink.{u, u + 1, u + 1, u + 1} A
  have hstage (i : I) (V : FiniteSplitEtaleHypercover (D.obj i).left) :
      hypercoverCohomologyι A ((Etale.upperStar A c.pt.hom).obj F) q
          (V.baseChange (coneProjection D c i)) ≫ f =
        hypercoverCohomologyι A ((Etale.upperStar A c.pt.hom).obj F) q
          (V.baseChange (coneProjection D c i)) ≫ g := by
    obtain ⟨K, e, ν, hν, ⟨h₁⟩, ⟨h₂⟩, ⟨h₃⟩⟩ :=
      exists_tail_section_shortComplex_colimit A F D c hc q i V
    apply filteredShortComplex_hom_ext A K (Cocone.mk _ ν) h₁ h₂ h₃
    intro j
    have hleg : ShortComplex.homologyMap (ν.app j) ≫
        hypercoverCohomologyι A ((Etale.upperStar A c.pt.hom).obj F) q
          (V.baseChange (coneProjection D c i)) =
        ShortComplex.homologyMap (e j).hom ≫
          hypercoverCohomologyι A ((Etale.upperStar A (D.obj j.unop.left).hom).obj F) q
            (tailHypercover D i V j.unop) ≫
          coneHypercoverMap A D c F q j.unop.left := by
      rw [hν, ShortComplex.homologyMap_comp, Category.assoc,
        tailCochainMap_homology_comp_ι]
    simpa only [← Category.assoc, hleg] using
      congrArg (fun t ↦ ShortComplex.homologyMap (e j).hom ≫
        hypercoverCohomologyι A ((Etale.upperStar A (D.obj j.unop.left).hom).obj F) q
          (tailHypercover D i V j.unop) ≫ t)
        (h j.unop.left)
  apply colimit.hom_ext
  intro U
  let E := (opOpEquivalence I).functor
  let D' := E ⋙ D ⋙ Over.forget S
  let c' := ((Over.forget S).mapCone c).whisker E
  have hc' : IsLimit c' := (Functor.Initial.isLimitWhiskerEquiv E _).symm hc
  have : ∀ j, CompactSpace (D'.obj j) := fun j ↦
    inferInstanceAs (CompactSpace (D.obj j.unop.unop).left)
  have : ∀ j, QuasiSeparatedSpace (D'.obj j) := fun j ↦
    inferInstanceAs (QuasiSeparatedSpace (D.obj j.unop.unop).left)
  have : ∀ {j k} (a : j ⟶ k), IsAffineHom (D'.map a) := fun a ↦
    inferInstanceAs (IsAffineHom (D.map a.unop.unop).left)
  have : CompactSpace c'.pt := inferInstanceAs (CompactSpace c.pt.left)
  have : QuasiSeparatedSpace c'.pt := inferInstanceAs (QuasiSeparatedSpace c.pt.left)
  obtain ⟨i, V, ⟨e⟩⟩ := exists_stage_hypercover_truncation D' c' hc' (q + 1) U.as.unop
  change hypercoverCohomologyι A ((Etale.upperStar A c.pt.hom).obj F) q U.as.unop ≫ f =
    hypercoverCohomologyι A ((Etale.upperStar A c.pt.hom).obj F) q U.as.unop ≫ g
  rw [← finiteRefinement_homology_comp_ι A ((Etale.upperStar A c.pt.hom).obj F)
    (V.baseChange (coneProjection D c i.unop.unop)) U.as.unop q e.hom]
  simp only [Category.assoc]
  rw [hstage i.unop.unop V]

end AlgebraicGeometry.FiniteSplitEtaleHypercover
