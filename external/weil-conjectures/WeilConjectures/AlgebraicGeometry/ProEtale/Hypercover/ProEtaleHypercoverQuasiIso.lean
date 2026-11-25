/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.Hypercover.ProEtaleHypercoverTotal
public import Mathlib.Algebra.Homology.CochainComplexPlus
public import Mathlib.Algebra.Category.ModuleCat.Abelian
import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleWeaklyContractibleEvaluationExact
import WeilConjectures.Algebra.Homology.BoundedBelowTotalComparison
import Mathlib.Algebra.Homology.TotalComplex
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.Algebra.Homology.TotalComplexSymmetry
import WeilConjectures.FromJoel.Algebra.Homology.BicomplexColumns
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor

/-!
# Hypercover totalization preserves bounded-below quasi-isomorphisms

## References

* Stacks Project, Tag 09A2, second proof paragraph, and Tag 0946 (1)
* Stacks Project, Tags 09A2 and 0946 (1)
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial

namespace AlgebraicGeometry.Scheme.ProEt

variable (X : Scheme.{u}) (R : Sheaf (topology X) CommRingCat.{u + 1})
  (W : X.ProEt) (U : SimplicialObject (Over W))

attribute [local instance] hypercoverSections_additive hypercoverSectionRows_additive

private instance sectionEvaluation_additive (p : ℕ) :
    (hypercoverSections X R W U ⋙ (CategoryTheory.evaluation _ _).obj ⦋p⦌).Additive where
  map_add {_I _J} {f g} := congr_app
    ((hypercoverSections X R W U).map_add (f := f) (g := g)) ⦋p⦌

private instance moduleEvaluation_additive (V : X.ProEt) :
    (SheafOfModules.evaluation.{u + 1}
      ((sheafCompose (topology X)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R) (op V)).Additive := by
  dsimp [SheafOfModules.evaluation]
  infer_instance

private theorem sectionsEvaluation_preservesHomology (p : ℕ)
    (hweak : ∀ (F G : Sheaf (topology X) (Type (u + 1))) (f : F ⟶ G),
      Epi f → Function.Surjective (f.hom.app (op (U _⦋p⦌).left))) :
    (hypercoverSections X R W U ⋙
      (CategoryTheory.evaluation _ _).obj ⦋p⦌).PreservesHomology := by
  let : CommRing (((sheafCompose (topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R).obj.obj (op W)) :=
    inferInstanceAs (CommRing (R.obj.obj (op W)))
  let : CommRing (((sheafCompose (topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R).obj.obj
        (op (U _⦋p⦌).left)) :=
    inferInstanceAs (CommRing (R.obj.obj (op (U _⦋p⦌).left)))
  have := weaklyContractible_evaluation_preservesHomology X R (U _⦋p⦌).left hweak
  have : PreservesFiniteLimits (SheafOfModules.evaluation.{u + 1}
      ((sheafCompose (topology X)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R) (op (U _⦋p⦌).left)) :=
    Functor.preservesFiniteLimits_of_preservesHomology _
  have : PreservesFiniteColimits (SheafOfModules.evaluation.{u + 1}
      ((sheafCompose (topology X)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R) (op (U _⦋p⦌).left)) :=
    Functor.preservesFiniteColimits_of_preservesHomology _
  change (SheafOfModules.evaluation.{u + 1}
    ((sheafCompose (topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R) (op (U _⦋p⦌).left) ⋙
        ModuleCat.restrictScalars
          (((sheafCompose (topology X)
            (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R).obj.map
              (Over.mkIdTerminal.from (U _⦋p⦌)).left.op).hom).PreservesHomology
  infer_instance

private theorem hypercover_extendMap_naturality
    {C : Type*} [Category C] [HasZeroObject C] [HasZeroMorphisms C]
    {A B : CochainComplex C ℕ} (f : A ⟶ B) (p : ℕ) :
    (HomologicalComplex.extendMap f ComplexShape.embeddingUpNat).f (p : ℤ) ≫
        (B.extendXIso ComplexShape.embeddingUpNat (i := p) rfl).hom =
      (A.extendXIso ComplexShape.embeddingUpNat (i := p) rfl).hom ≫ f.f p := by
  change ((ComplexShape.embeddingUpNat.extendFunctor _).map f).f (p : ℤ) ≫ _ = _
  erw [HomologicalComplex.extendMap_f _ ComplexShape.embeddingUpNat (i := p) rfl]
  simp

set_option backward.isDefEq.respectTransparency false in
private noncomputable def sectionColumnIso
    (E : CochainComplex (ringedSiteModules.{u + 1}
      ((sheafCompose (topology X)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R)) ℤ) (p : ℕ) :
    (HomologicalComplex₂.flip
      (((hypercoverSectionRows X R W U).mapHomologicalComplex (.up ℤ)).obj E)).X (p : ℤ) ≅
      (((hypercoverSections X R W U ⋙ (CategoryTheory.evaluation _ _).obj ⦋p⦌).mapHomologicalComplex
        (.up ℤ)).obj E) := by
  refine HomologicalComplex.Hom.isoOfComponents (fun q ↦
    (((AlgebraicTopology.alternatingCofaceMapComplex _).obj
      ((hypercoverSections X R W U).obj (E.X q))).extendXIso
        ComplexShape.embeddingUpNat (i := p) rfl)) ?_
  intro q r h
  symm
  change ((ComplexShape.embeddingUpNat.extendFunctor _).map
    ((AlgebraicTopology.alternatingCofaceMapComplex _).map
      ((hypercoverSections X R W U).map (E.d q r)))).f (p : ℤ) ≫ _ = _
  erw [HomologicalComplex.extendMap_f _ ComplexShape.embeddingUpNat (i := p) rfl]
  simp

private theorem sectionBicomplex_zero
    (E : CochainComplex (ringedSiteModules.{u + 1}
      ((sheafCompose (topology X)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R)) ℤ)
    (N : ℤ) [E.IsStrictlyGE N] (p q : ℤ) (h : p < 0 ∨ q < N) :
    IsZero (((HomologicalComplex₂.flip
      (((hypercoverSectionRows X R W U).mapHomologicalComplex (.up ℤ)).obj E)).X p).X q) := by
  change IsZero (((hypercoverSectionRows X R W U).obj (E.X q)).X p)
  rcases h with hp | hq
  · exact HomologicalComplex.isZero_extend_X _ ComplexShape.embeddingUpNat p (by
      intro i hi
      change (i : ℤ) = p at hi
      omega)
  · exact (HomologicalComplex.eval _ _ p).map_isZero
      ((hypercoverSectionRows X R W U).map_isZero (E.isZero_of_isStrictlyGE N q hq))

set_option backward.isDefEq.respectTransparency false in
/-- Weakly contractible terms suffice for bounded-below quasi-isomorphism invariance;
no covering or matching-map hypotheses are needed for this comparison. -/
theorem hypercoverTotal_map_quasiIso_of_weaklyContractible
    (hweak : ∀ (p : ℕ) (F G : Sheaf (topology X) (Type (u + 1))) (f : F ⟶ G),
      Epi f → Function.Surjective (f.hom.app (op (U _⦋p⦌).left)))
    (E F : CochainComplex.Plus (ringedSiteModules.{u + 1}
      ((sheafCompose (topology X)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R)))
    (f : E ⟶ F) (hf : QuasiIso f.hom) :
    QuasiIso ((hypercoverTotal X R W U).map f.hom) := by
  obtain ⟨NE, hE⟩ := E.property
  obtain ⟨NF, hF⟩ := F.property
  let N := min NE NF
  have := hE
  have := hF
  have := E.obj.isStrictlyGE_of_ge N NE (min_le_left _ _)
  have := F.obj.isStrictlyGE_of_ge N NF (min_le_right _ _)
  let g := (HomologicalComplex₂.flipFunctor _ (.up ℤ) (.up ℤ)).map
    (((hypercoverSectionRows X R W U).mapHomologicalComplex (.up ℤ)).map f.hom)
  apply HomologicalComplex₂.quasiIso_totalMap_of_boundedBelow_columns g 0 N
    (sectionBicomplex_zero X R W U E.obj N) (sectionBicomplex_zero X R W U F.obj N)
  intro p
  by_cases hp : 0 ≤ p
  · obtain ⟨p, rfl⟩ := Int.eq_ofNat_of_zero_le hp
    let ev := hypercoverSections X R W U ⋙ (CategoryTheory.evaluation _ _).obj ⦋p⦌
    have : ev.PreservesHomology := sectionsEvaluation_preservesHomology X R W U p (hweak p)
    have : QuasiIso ((ev.mapHomologicalComplex (.up ℤ)).map f.hom) := inferInstance
    apply (quasiIso_iff_of_arrow_mk_iso (g.f (p : ℤ)) _
      (Arrow.isoMk (sectionColumnIso X R W U E.obj p)
        (sectionColumnIso X R W U F.obj p) ?_)).mpr this
    apply HomologicalComplex.hom_ext
    intro q
    dsimp only [HomologicalComplex.comp_f, HomologicalComplex.Hom.isoOfComponents_hom_f]
    symm
    exact hypercover_extendMap_naturality
      ((AlgebraicTopology.alternatingCofaceMapComplex _).map
        ((hypercoverSections X R W U).map (f.hom.f q))) p
  · have hzero (A : CochainComplex.Plus (ringedSiteModules.{u + 1}
        ((sheafCompose (topology X)
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R))) :
        IsZero ((HomologicalComplex₂.flip
          (((hypercoverSectionRows X R W U).mapHomologicalComplex (.up ℤ)).obj A.obj)).X p) := by
      rw [IsZero.iff_id_eq_zero]
      apply HomologicalComplex.hom_ext
      intro q
      change (𝟙 (((hypercoverSectionRows X R W U).obj (A.obj.X q)).X p)) = 0
      exact (HomologicalComplex.isZero_extend_X _ ComplexShape.embeddingUpNat p (by
        intro i hi
        change (i : ℤ) = p at hi
        omega)).eq_of_src _ _
    have : IsIso (g.f p) := (hzero E).isIso (hzero F) _
    infer_instance

end AlgebraicGeometry.Scheme.ProEt
