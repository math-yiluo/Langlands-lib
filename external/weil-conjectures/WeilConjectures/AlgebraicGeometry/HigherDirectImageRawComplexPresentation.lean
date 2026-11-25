/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.HigherDirectImageRawDiagram
public import WeilConjectures.AlgebraicGeometry.EtaleComplexCohomologyPresentationData
import WeilConjectures.AlgebraicGeometry.RawModuleRestrictedAbelianNaturalIso
import WeilConjectures.AlgebraicGeometry.EtaleComplexCohomologyLimit

/-! # Presenting raw module cohomology by abelian etale complexes

Source: Stacks Project, Tags 09Z1, 0EZM and 03FD.
(blueprint: lem-sbc-higher-image-raw-complex-presentation).
-/

@[expose] public section

universe u
open CategoryTheory Limits Opposite
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale
namespace AlgebraicGeometry.Etale

set_option backward.isDefEq.respectTransparency true in
/-- The precise hypotheses of complex continuity, as an existential proposition.
No object or map is chosen by this definition, and no continuity conclusion is a field.
Source: Stacks Project, Tag 0EZM, lemma-colimit-variant-complexes.
(blueprint: def-sbc-etale-complex-cohomology-presentation). -/
abbrev EtaleComplexCohomologyPresentation
    {I : Type u} [SmallCategory I] [IsCofiltered I]
    (H : Iᵒᵖ ⥤ AddCommGrpCat.{u + 1}) (B : Cocone H) : Prop :=
  EtaleComplexCohomologyPresentationData H B

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency true in
/-- Complex continuity applied to a presentation. The witnesses are eliminated only
inside this proof; no library definition selects data from an existence statement. 
(blueprint: def-sbc-etale-complex-cohomology-presentation)
-/
theorem EtaleComplexCohomologyPresentation.isColimit
    {I : Type u} [SmallCategory I] [IsCofiltered I]
    {H : Iᵒᵖ ⥤ AddCommGrpCat.{u + 1}} {B : Cocone H}
    (s : EtaleComplexCohomologyPresentation H B) : Nonempty (IsColimit B) := by
  rcases s with ⟨D, c, hc, compact, quasiSeparated, affine, F, φ,
    hidentity, hcomposition, a, hbelow, G,
    eG, hG, p, P, hP, eH, hH, L, hL, eB, hB, _⟩
  exact @nonempty_isColimit_etale_complex_cohomology I _ _ D c hc compact
    quasiSeparated affine F @φ hidentity hcomposition a hbelow G eG hG
    p @P @hP H eH hH L hL B eB hB

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency true in
/-- Raw module derived-Hom cohomology, including its fixed transition maps, has a
presentation by abelian etale complexes on the base-changed inverse system.
This theorem identifies the input to continuity; it does not assert cohomology
continuity or any eventual equality of classes.
Source: Stacks Project, Tag 09Z1 (lemma-relative-colimit, the affine-object reduction),
Tag 0EZM (lemma-colimit-variant-complexes, the coefficient system), and Tag 03FD
(lemma-cohomology-modules-abelian, comparison after forgetting scalars).
(blueprint: lem-sbc-higher-image-raw-complex-presentation).

Proof: Use the diagram of schemes D(i) times_S U and the cone c.pt times_S U, obtained
by applying Over.map k, Over.pullback U.hom, and Over.forget U.left. Pullback preserves
this limiting cone. Its transition maps are affine by base change. Each stage is qcqs:
its map to affine U is qcqs by base change of D(i).hom followed by k, and composing with
the structure map of affine U gives compactness and quasi-separatedness of the stage.
Take F(i) to be the single complex in degree zero of the underlying abelian sheaf of
the pullback of G along D(i) times_S U -> W. Take phi from the inverse-image composition
isomorphism, so identity and composition hold by its unit and associativity coherence.
The lower bound is zero. On the limit, take the constant diagram G' with value the
single complex of the underlying abelian pullback of G. Inverse-image composition and
forgetting scalars supply eG and its map equation hG. The identity cocone of this constant
diagram is colimiting, since I opposite is nonempty and connected; this is L and hL.
Take p=q and P to be exactly the derived-adjunction map displayed in hP.
For eH and eB, free-module-sheaf adjunction identifies raw derived Hom out of the free
sheaf of U with derived sections on the corresponding fibre product. An injective
module resolution computes those sections after forgetting scalars, by the all-object
abelian acyclicity in 03FD. It gives additive isomorphisms to the abelian cohomology of
the degree-zero complexes. Derived adjunction is natural in the scheme morphism:
expanding its unit and the pullback-composition, single-complex and shift comparisons
gives the five factors of the fixed raw pullback. Hence hH and hB concern these exact
maps, not an unspecified comparison. These explicit data supply the existential presentation.
For negative q the same identification applies, with both degree-zero-complex
cohomology groups zero. No continuity theorem is used to construct the presentation. -/
theorem nonempty_higherDirectImageRaw_complex_presentation
    (Λ : Type (u + 1)) [CommRing Λ] {W S : Scheme.{u}} (k : W ⟶ S)
    (G : Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℤ)
    {I : Type u} [Category.{u} I] [IsCofiltered I] (D : I ⥤ Over W)
    [∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f).left]
    [∀ i, QuasiCompact ((D.obj i).hom ≫ k)]
    [∀ i, QuasiSeparated ((D.obj i).hom ≫ k)]
    (c : Cone D) (hc : IsLimit ((Over.forget W).mapCone c))
    [QuasiCompact (c.pt.hom ≫ k)] [QuasiSeparated (c.pt.hom ≫ k)]
    (U : S.Etale) [IsAffine U.left] :
    EtaleComplexCohomologyPresentation
      (higherDirectImageRawDiagram Λ k G q D U)
      (higherDirectImageRawCocone Λ k G q D c U) := by
  obtain ⟨e, he⟩ := exists_rawModule_restrictedAbelian_natural_iso Λ k G q U
  let F₀ := (sheafCompose W.smallEtaleTopology
    (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj G
  unfold EtaleComplexCohomologyPresentation
  refine restrictedOverAbelianCocone_complex_data k F₀ q D c hc U
    (higherDirectImageRawDiagram Λ k G q D U)
    (higherDirectImageRawCocone Λ k G q D c U)
    (fun i ↦ e (D.obj i)) (e c.pt) ?_ ?_
  · intro i j f
    dsimp only [higherDirectImageRawDiagram, Functor.comp_map, Functor.op_map]
    exact he _ _ (D.map f)
  · intro i
    dsimp only [higherDirectImageRawCocone, Functor.mapCocone, Cone.op,
      Functor.op_obj, NatTrans.op_app, Functor.mapCocone_ι_app]
    exact he _ _ (c.π.app i)

end AlgebraicGeometry.Etale
