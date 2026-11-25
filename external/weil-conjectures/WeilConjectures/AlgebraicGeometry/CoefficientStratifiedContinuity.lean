/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.ClassicalContinuityMap
public import WeilConjectures.AlgebraicGeometry.CoefficientAffineConstructibleProEtaleModules
import WeilConjectures.AlgebraicGeometry.CoefficientComparisonContinuity
import WeilConjectures.AlgebraicGeometry.CoefficientFpLocalSystemOrigin
import WeilConjectures.AlgebraicGeometry.CoefficientStratifiedEssentialImage
/-! # Continuity for modules with one finite constructible stratification
Source: the classicality detail of blueprint constructible comparison; Stacks 09AK.
-/
@[expose] public noncomputable section
set_option autoImplicit false
universe u v
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.ProEtale
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall in
/-- Finite local systems on one finite constructible partition give continuity.
Source: blueprint sk-thm-pe-constructible-comparison-classical, Stacks Tag 09AK
(auxiliary; not a blueprint node).

Proof: constant-scalar restriction keeps the additive sheaf, and its scalar action
extends uniquely back across the locally bijective constant-ring sheafification
unit. Over a Noetherian ring each finite local model is finitely presented. The
finite-presentation local-system comparison makes its restriction to each stratum
an etale inverse image. Localize first on affine open subsets; restriction pulls
back the same finite partition and its models. On each affine, induct on the
finite constructible partition, using affine
shrinking to expose a nonempty open stratum. The open-closed exact sequence has
etale antecedents for extension by zero and closed direct image, by comparison
with these two operations. The classical subcategory is closed under extensions,
so the remaining closed partition and the open stratum give an etale antecedent
for the restricted module. Etale origin is Zariski local, so these local
antecedents descend to the entire module. Empty strata can first be removed, and the empty partition
on the empty scheme gives the zero sheaf. On an affine presentation, etale sections
of an inverse image form the prescribed filtered colimit by finite-presentation
factorization of maps into etale schemes. This identifies the canonical
continuity map, including its A-action, with a colimit comparison isomorphism.
All this takes place on the equivalent coefficient-sized sites: an object and a
cover retain their underlying scheme, and AsSmall sends every projection to that
same projection. Hence it gives exactly the map displayed below. -/
theorem coefficientStratified_continuity (X : Scheme.{u})
    (A : Type (max v (u + 1))) [CommRing A] [IsNoetherianRing A]
    (F : ConstantCompletion.Mod (ConstantCompletion.constant
      (Scheme.coefficientProEtaleModelTopology.{u, v} X) A))
    (S : Scheme.Stratification X)
    (hS : ∀ a : Fin S.n, IsCoefficientModelLocallyConstantFinite
      (Scheme.coefficientProEtaleModelTopology.{u, v} (S.domain a)) A
      ((Scheme.coefficientProEtaleFixedModulePullback.{u, v} (S.immersion a) A).obj
        ((coefficientModelFixedScalars _ A).obj F))) :
    ∀ {I : Type (u + 1)} [SmallCategory I] [IsCofiltered I]
      (P : AffinePresentation X I),
      IsIso (continuityMap P
        ((AsSmall.up : X.ProEt ⥤ Scheme.coefficientProEtaleSiteModel.{u, v} X).op ⋙
          ((coefficientModelFixedScalars _ A).obj F).obj)) := by
  let E := (coefficientModelFixedScalars _ A).obj F
  have horigin := coefficientFixed_essImage_of_stratification X A S E (fun k ↦ by
    apply coefficientFpLocalSystem_essImage (S.domain k) A
    intro V
    obtain ⟨T, hT, ht⟩ := hS k V
    refine ⟨T, hT, ?_⟩
    intro U f hf
    obtain ⟨M, hM, e⟩ := ht U f hf
    have := hM
    exact ⟨M, Module.finitePresentation_of_finite A M, e⟩)
  obtain ⟨G, ⟨e⟩⟩ := horigin
  intro I _ _ P
  let H := (AsSmall.up : X.ProEt ⥤ Scheme.coefficientProEtaleSiteModel.{u, v} X).op
  let t : H ⋙ ((Functor.sheafPullbackConstruction.sheafPullback
      (Scheme.smallModelComparisonInclusion.{u, v} X) (ModuleCat.{max v (u + 1)} A)
      (Scheme.smallModelComparisonEtaleTopology.{u, v} X)
      (Scheme.coefficientProEtaleModelTopology.{u, v} X)).obj G).obj ≅ H ⋙ E.obj :=
    Functor.isoWhiskerLeft H ((sheafToPresheaf _ _).mapIso e)
  change IsIso (continuityMap P (H ⋙ E.obj))
  obtain ⟨hcolim⟩ := coefficientFixedComparison_isColimit X A G P
  have hi : IsIso (continuityMap P (H ⋙
      ((Functor.sheafPullbackConstruction.sheafPullback
        (Scheme.smallModelComparisonInclusion.{u, v} X) (ModuleCat.{max v (u + 1)} A)
        (Scheme.smallModelComparisonEtaleTopology.{u, v} X)
        (Scheme.coefficientProEtaleModelTopology.{u, v} X)).obj G).obj)) := by
    exact ((colimit.isColimit _).nonempty_isColimit_iff_isIso_desc).mp ⟨hcolim⟩
  have heq := continuityMap_natural P t.hom
  have : IsIso (colimMap (Functor.whiskerLeft P.diagram.op t.hom)) := by
    change IsIso ((colim : (Iᵒᵖ ⥤ ModuleCat.{max v (u + 1)} A) ⥤ _).map
      (Functor.isoWhiskerLeft P.diagram.op t).hom)
    infer_instance
  apply (isIso_comp_left_iff
    (colimMap (Functor.whiskerLeft P.diagram.op t.hom)) _).mp
  rw [heq]
  infer_instance
end AlgebraicGeometry.ProEtale
