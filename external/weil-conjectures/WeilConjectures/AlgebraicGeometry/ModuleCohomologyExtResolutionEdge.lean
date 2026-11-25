/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.ModuleCohomologyExtResolutionNaturality


public import WeilConjectures.AlgebraicGeometry.Cohomology.FlatCohomologyComparison
public import WeilConjectures.AlgebraicGeometry.ModuleCohomologyExtResolutionNaturalityExtension
public import WeilConjectures.AlgebraicGeometry.ModuleCohomologyFMap
import WeilConjectures.AlgebraicGeometry.ModuleCohomologyExtSectionDiagram

/-! # Edge compatibility for the resolution-normalized comparison

Source: Stacks Project, Tags 03FD, 01FB and 01F7.
(blueprint: new-module-cohomology-ext-resolution-edge)
-/

@[expose] public section
universe u
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits Opposite
noncomputable section
namespace AlgebraicGeometry.Scheme.Modules

private theorem common_section_diagram_cancel
    {A B C D E K : AddCommGrpCat.{u}}
    (aX : A ≅ B) (aY : C ≅ D) (bX : E ≅ B)
    (eX : A ⟶ E) (eY : C ⟶ K) (bY : K ≅ D)
    {L : AddCommGrpCat.{u}} (β : D ⟶ L) (μ : B ⟶ L) [IsIso μ]
    (hX : eX ≫ bX.hom = aX.hom) (hY : eY ≫ bY.hom = aY.hom)
    (edge : K ⟶ E) (h : bY.hom ≫ β = edge ≫ bX.hom ≫ μ) :
    (aY.hom ≫ β ≫ inv μ ≫ aX.inv) ≫ eX = eY ≫ edge := by
  rw [← cancel_mono bX.hom, Category.assoc, hX]
  rw [← cancel_mono μ]
  simp only [Category.assoc, Iso.inv_hom_id_assoc, IsIso.inv_hom_id,
    Category.comp_id]
  rw [← h, ← Category.assoc, hY]

/-- The concrete resolution comparison intertwines the direct-image edge map.
This asserts an equality for the constructed `moduleCohomologyExtResolutionEquiv`,
not for arbitrary natural equivalences.
Source: Stacks Project, Tag 03FD, Lemma 21.12.4; Tag 01FB, Remark 20.14.2;
Tag 01F7, Section 20.14.
(blueprint: new-module-cohomology-ext-resolution-edge)

Proof: Let D be the choices defining moduleCohomologyFMap f (identity).
Its resolutions I of F and J of f_*F, injective replacement K of f_*I,
and augmentation lift beta give the section diagram in 01FB. The canonical
restriction at f inverse(Y)=X is D.a, fixed by D.sections. The vertical map
mu=D.a followed by sections(lambda) induces an isomorphism by D.invertible.
Forgotten injective module terms are acyclic on every open by 03FD, hence
compute the same derived abelian direct image and its global sections.
The comparison used in moduleCohomologyExtResolutionEquiv is the inverse of
the augmentation-preserving acyclic-resolution comparison, so it may be
computed on I and J instead of the standard resolutions: lift identities
between these resolutions and apply homotopy invariance and acyclic-comparison
naturality. Thus the section diagram also computes Ext cohomology after
forgetting modules. Under the free-abelian-terminal-source isomorphism,
evaluation at the identity generator becomes evaluation at 1. Exact abelian
inverse image and its counit therefore calculate that same diagram: applying
inverse image to an Ext class and then postcomposing with coeff(f,identity)
is the canonical abelian cohomology map of the identity f-map. Its section map
is restriction at f inverse(Y)=X, with precisely the constant-sheaf comparison
constIso(f).symm. Both maps compose with H(mu) to H(sections(beta)); cancel the
invertible H(mu). Transport back using the resolution isomorphisms. Independence
of augmentation lifts follows from homotopy invariance. This uses neither
exact module pullback nor acyclicity of f_*F; in degree zero it is the same
section identity, including empty schemes and zero coefficients. -/
theorem moduleCohomologyExtResolutionEquiv_edge
    {X Y : Scheme.{u}} (f : X ⟶ Y) (F : X.Modules) (p : ℕ)
    (x : (RingedSpace.moduleCohomology Y.toRingedSpace p).obj
      ((pushforward f).obj F)) :
    moduleCohomologyExtResolutionEquiv X F p (moduleCohomologyEdgeMap f F p x) =
      Sheaf.H.map (coeff f (𝟙 ((pushforward f).obj F))) p
        (Sheaf.H.mapFunctor (invImage f) (constIso f).symm
          ((SheafOfModules.toSheaf Y.ringCatSheaf).obj ((pushforward f).obj F)) p
          (moduleCohomologyExtResolutionEquiv Y ((pushforward f).obj F) p x)) := by
  let D := Classical.choice
    (moduleCohomologyFMapData_nonempty f ((pushforward f).obj F) F
      (𝟙 ((pushforward f).obj F)))
  let aX := ExtEdgeResolution.moduleResolutionIso X D.I p
  let aY := ExtEdgeResolution.moduleResolutionIso Y D.J p
  let bX := ExtEdgeResolution.abelianResolutionIso X D.I p
  let bY := ExtEdgeResolution.abelianResolutionIso Y D.J p
  let eX := AddCommGrpCat.ofHom
    (moduleCohomologyExtResolutionEquiv X F p).toAddMonoidHom
  let eY := AddCommGrpCat.ofHom
    (moduleCohomologyExtResolutionEquiv Y ((pushforward f).obj F) p).toAddMonoidHom
  let β := (HomologicalComplex.homologyFunctor AddCommGrpCat.{u}
    (ComplexShape.up ℕ) p).map
      (((ExtEdgeResolution.moduleSections Y).mapHomologicalComplex
        (ComplexShape.up ℕ)).map D.β)
  let μ := (HomologicalComplex.homologyFunctor AddCommGrpCat.{u}
    (ComplexShape.up ℕ) p).map (D.a.hom ≫
      ((ExtEdgeResolution.moduleSections Y).mapHomologicalComplex
        (ComplexShape.up ℕ)).map D.lambda)
  have : IsIso μ := D.invertible p
  have hX : eX ≫ bX.hom = aX.hom := by
    ext z
    exact ExtEdgeResolution.moduleCohomologyExtResolutionEquiv_normalization X D.I p z
  have hY : eY ≫ bY.hom = aY.hom := by
    ext z
    exact ExtEdgeResolution.moduleCohomologyExtResolutionEquiv_normalization Y D.J p z
  have h := common_section_diagram_cancel aX aY bX eX eY bY β μ hX hY
    (ExtEdgeResolution.abelianEdgeHom f F p)
    (ExtEdgeResolution.abelianEdge_section_diagram f F D p)
  have hm : D.map p = aY.hom ≫ β ≫ inv μ ≫ aX.inv := by
    simp only [ModuleCohomologyFMapData.map, aX, aY,
      ExtEdgeResolution.moduleResolutionIso, Iso.trans_hom, Iso.trans_inv,
      Iso.symm_hom, Iso.symm_inv, CategoryTheory.Functor.mapIso_hom,
      CategoryTheory.Functor.mapIso_inv,
      Category.assoc, β, μ]
  rw [← hm] at h
  exact congrArg (fun k ↦ k x) h

end AlgebraicGeometry.Scheme.Modules
