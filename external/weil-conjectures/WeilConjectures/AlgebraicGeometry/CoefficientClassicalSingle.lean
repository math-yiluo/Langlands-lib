/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.CoefficientBoundedClassicalDescent
/-! # Classical modules in degree zero
Source: Stacks Tags 05RU and 099T, degree-zero embedding and continuity.
-/
@[expose] public noncomputable section
set_option autoImplicit false
universe u v w
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.ProEtale
/-- The ordinary degree-n embedding into the standard derived localization.
Source: Stacks Tag 05RU (auxiliary; not a blueprint node). -/
@[irreducible] def coefficientModelSingle {C : Type w} [SmallCategory C]
    {J : GrothendieckTopology C} (R : Sheaf J CommRingCat.{w}) (n : ℤ) :
    ConstantCompletion.Mod R ⥤ ConstantCompletion.D R :=
  @DerivedCategory.singleFunctor _ _ _ (HasDerivedCategory.standard _) n

instance coefficientModelSingle_full {C : Type w} [SmallCategory C]
    {J : GrothendieckTopology C} (R : Sheaf J CommRingCat.{w}) (n : ℤ) :
    (coefficientModelSingle R n).Full := by
  let := HasDerivedCategory.standard (ConstantCompletion.Mod R)
  unfold coefficientModelSingle
  infer_instance

instance coefficientModelSingle_faithful {C : Type w} [SmallCategory C]
    {J : GrothendieckTopology C} (R : Sheaf J CommRingCat.{w}) (n : ℤ) :
    (coefficientModelSingle R n).Faithful := by
  let := HasDerivedCategory.standard (ConstantCompletion.Mod R)
  unfold coefficientModelSingle
  infer_instance

/-- A degree-zero module has cohomology only in the ordered interval [0,0].
Source: Stacks Tag 05RU (auxiliary; not a blueprint node).
Proof: the standard single complex is both at least and at most degree zero;
the homology vanishing lemmas give the two tails. -/
theorem coefficientSingle_bounded {C : Type w} [SmallCategory C]
    {J : GrothendieckTopology C} (R : Sheaf J CommRingCat.{w})
    (M : ConstantCompletion.Mod R) :
    coefficientCohomologyBounded R ((coefficientModelSingle R 0).obj M) := by
  let := HasDerivedCategory.standard (ConstantCompletion.Mod R)
  unfold coefficientModelSingle
  refine ⟨0, 0, le_rfl, ?_⟩
  intro q hq
  rcases hq with hq | hq
  · exact ((DerivedCategory.singleFunctor _ 0).obj M).isZero_of_isGE 0 q hq
  · exact ((DerivedCategory.singleFunctor _ 0).obj M).isZero_of_isLE 0 q hq

/-- Degree-zero cohomology of a module in degree zero is that same module.
Source: Stacks Tag 05RU (auxiliary; not a blueprint node). -/
def coefficientSingle_homologyIso {C : Type w} [SmallCategory C]
    {J : GrothendieckTopology C} (R : Sheaf J CommRingCat.{w})
    (M : ConstantCompletion.Mod R) :
    (coefficientModelCohomology R 0).obj ((coefficientModelSingle R 0).obj M) ≅ M := by
  letI := HasDerivedCategory.standard (ConstantCompletion.Mod R)
  unfold coefficientModelSingle
  exact (DerivedCategory.singleFunctorCompHomologyFunctorIso _ 0).app M

private theorem singleHZero {C : Type w} [SmallCategory C]
    {J : GrothendieckTopology C} (R : Sheaf J CommRingCat.{w})
    (M : ConstantCompletion.Mod R) (q : ℤ) (hq : q ≠ 0) :
    IsZero ((coefficientModelCohomology R q).obj ((coefficientModelSingle R 0).obj M)) := by
  let := HasDerivedCategory.standard (ConstantCompletion.Mod R)
  unfold coefficientModelSingle
  rcases lt_or_gt_of_ne hq with hq | hq
  · exact ((DerivedCategory.singleFunctor _ 0).obj M).isZero_of_isGE 0 q hq
  · exact ((DerivedCategory.singleFunctor _ 0).obj M).isZero_of_isLE 0 q hq

/-- Cancel degree-zero embeddings to recover full faithfulness of a module functor.
Source: Stacks Tags 05RU and 09AL (auxiliary; not a blueprint node).
Proof: the embeddings are fully faithful and their images are bounded. Apply the
morphism bijection in that image, transfer it through the given natural isomorphism,
and cancel the target embedding. -/
theorem coefficientSingle_full_faithful {C B : Type w} [SmallCategory C] [SmallCategory B]
    {J : GrothendieckTopology C} {K : GrothendieckTopology B}
    (R : Sheaf J CommRingCat.{w}) (S : Sheaf K CommRingCat.{w})
    (F : ConstantCompletion.Mod R ⥤ ConstantCompletion.Mod S)
    (D : ConstantCompletion.D R ⥤ ConstantCompletion.D S)
    (hff : ∀ M N, coefficientCohomologyBounded R M → coefficientCohomologyBounded R N →
      Function.Bijective (D.map : (M ⟶ N) → (D.obj M ⟶ D.obj N)))
    (hS : coefficientModelSingle R 0 ⋙ D ≅ F ⋙ coefficientModelSingle S 0) :
    F.Full ∧ F.Faithful := by
  let E := coefficientModelSingle R 0
  let P := coefficientModelSingle S 0
  have : (E ⋙ D).Faithful := by
    constructor
    intro M N f g h
    apply E.map_injective
    exact (hff _ _ (coefficientSingle_bounded R M)
      (coefficientSingle_bounded R N)).injective h
  have : (E ⋙ D).Full := by
    constructor
    intro M N f
    obtain ⟨g, hg⟩ := (hff _ _ (coefficientSingle_bounded R M)
      (coefficientSingle_bounded R N)).surjective f
    obtain ⟨k, hk⟩ := E.map_surjective g
    exact ⟨k, by change D.map (E.map k) = f; rw [hk, hg]⟩
  have : (F ⋙ P).Full := Functor.Full.of_iso hS
  have : (F ⋙ P).Faithful := Functor.Faithful.of_iso hS
  exact ⟨Functor.Full.of_comp_faithful F P, Functor.Faithful.of_comp F P⟩

private theorem continuousIso (X : Scheme.{u})
    (A : Type (max v (u + 1))) [CommRing A]
    {F G : X.ProEtᵒᵖ ⥤ ModuleCat.{max v (u + 1)} A} (e : F ≅ G)
    (hF : ∀ {I : Type (u + 1)} [SmallCategory I] [IsCofiltered I]
      (P : AffinePresentation X I), IsIso (continuityMap P F)) :
    ∀ {I : Type (u + 1)} [SmallCategory I] [IsCofiltered I]
      (P : AffinePresentation X I), IsIso (continuityMap P G) := by
  intro I _ _ P
  have := hF P
  have hn := continuityMap_natural P e.hom
  have : IsIso (Functor.whiskerLeft P.diagram.op e.hom) := by
    change IsIso (Functor.isoWhiskerLeft P.diagram.op e).hom
    infer_instance
  apply (isIso_comp_left_iff
    (colimMap (Functor.whiskerLeft P.diagram.op e.hom)) _).mp
  rw [hn]
  infer_instance

private theorem continuousZero (X : Scheme.{u})
    (A : Type (max v (u + 1))) [CommRing A]
    (F : ConstantCompletion.Mod (ConstantCompletion.constant
      (Scheme.coefficientProEtaleModelTopology.{u, v} X) A)) (hF : IsZero F) :
    ∀ {I : Type (u + 1)} [SmallCategory I] [IsCofiltered I]
      (P : AffinePresentation X I), IsIso (continuityMap P
        ((AsSmall.up : X.ProEt ⥤ Scheme.coefficientProEtaleSiteModel.{u, v} X).op ⋙
          ((coefficientModelFixedScalars _ A).obj F).obj)) := by
  let J := Scheme.coefficientProEtaleModelTopology.{u, v} X
  have : (coefficientModelFixedScalars J A).Additive :=
    { map_add := by intro M N f g; ext U x; rfl }
  have hz := (coefficientModelFixedScalars J A).map_isZero hF
  have hp := (sheafToPresheaf J (ModuleCat A)).map_isZero hz
  intro I _ _ P
  let E := (AsSmall.up : X.ProEt ⥤ Scheme.coefficientProEtaleSiteModel.{u, v} X).op ⋙
    ((coefficientModelFixedScalars _ A).obj F).obj
  have hd : IsZero (sectionDiagram P E) :=
    Functor.isZero _ (fun i ↦ hp.obj _)
  exact ((colimit.isColimit (sectionDiagram P E)).isZero_pt hd).isIso
    (hp.obj _) _

/-- A continuous module, placed in degree zero, has continuous cohomology in all degrees.
Source: Stacks Tags 05RU and 099T (auxiliary; not a blueprint node).
Proof: degree zero cohomology is naturally the original module, so naturality of the
continuity map transports its isomorphism. Every other cohomology object is zero;
the constant-scalar restriction is additive, hence has zero sections there, and the
colimit of the resulting zero diagram is zero. Its continuity map is an isomorphism. -/
theorem coefficientSingle_classical (X : Scheme.{u})
    (A : Type (max v (u + 1))) [CommRing A]
    (F : ConstantCompletion.Mod (ConstantCompletion.constant
      (Scheme.coefficientProEtaleModelTopology.{u, v} X) A))
    (hF : ∀ {I : Type (u + 1)} [SmallCategory I] [IsCofiltered I]
      (P : AffinePresentation X I), IsIso (continuityMap P
        ((AsSmall.up : X.ProEt ⥤ Scheme.coefficientProEtaleSiteModel.{u, v} X).op ⋙
          ((coefficientModelFixedScalars _ A).obj F).obj))) :
    ∀ q : ℤ, ∀ {I : Type (u + 1)} [SmallCategory I] [IsCofiltered I]
      (P : AffinePresentation X I), IsIso (continuityMap P
        ((AsSmall.up : X.ProEt ⥤ Scheme.coefficientProEtaleSiteModel.{u, v} X).op ⋙
          ((coefficientModelFixedScalars _ A).obj ((coefficientModelCohomology _ q).obj
            ((coefficientModelSingle _ 0).obj F))).obj)) := by
  intro q
  by_cases hq : q = 0
  · subst q
    let e := (coefficientSingle_homologyIso _ F).symm
    exact continuousIso X A
      (Functor.isoWhiskerLeft AsSmall.up.op
        ((sheafToPresheaf _ (ModuleCat A)).mapIso
          ((coefficientModelFixedScalars _ A).mapIso e))) hF
  · exact continuousZero X A _ (singleHZero _ F q hq)
end AlgebraicGeometry.ProEtale
