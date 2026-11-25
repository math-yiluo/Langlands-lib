/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtaleAbelianHypercoverTotal
public import Mathlib.Algebra.Homology.CochainComplexPlus
import WeilConjectures.AlgebraicGeometry.ProEtaleAbelianEvaluationColimits
import WeilConjectures.Algebra.Homology.BoundedBelowTotalComparison
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor

/-!
# Hypercover totalization preserves bounded-below quasi-isomorphisms

Source: Stacks Project, Tag 09A2, second proof paragraph, and Tag 0946 (1).
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial

namespace AlgebraicGeometry.Scheme.ProEt

variable (X : Scheme.{u})
  (W : X.ProEt) (U : SimplicialObject (Over W))

private instance sectionEvaluation_additive (p : ℕ) :
    (abelianHypercoverSections X W U ⋙ (CategoryTheory.evaluation _ _).obj ⦋p⦌).Additive where
  map_add {_I _J} {f g} := congr_app
    ((abelianHypercoverSections X W U).map_add (f := f) (g := g)) ⦋p⦌

private theorem sectionsEvaluation_preservesHomology (p : ℕ)
    (haff : IsAffine (U _⦋p⦌).left.left)
    (hweak : ∀ (F G : Sheaf (topology X) (Type (u + 1))) (f : F ⟶ G),
      Epi f → Function.Surjective (f.hom.app (op (U _⦋p⦌).left))) :
    (abelianHypercoverSections X W U ⋙
      (CategoryTheory.evaluation _ _).obj ⦋p⦌).PreservesHomology := by
  let : IsAffine (U _⦋p⦌).left.left := haff
  exact (affine_weaklyContractible_abelian_evaluation_colimits X (U _⦋p⦌).left hweak).1

set_option backward.isDefEq.respectTransparency false in
private noncomputable def sectionColumnIso
    (E : CochainComplex (Sheaf (topology X) AddCommGrpCat.{u + 1}) ℤ) (p : ℕ) :
    (HomologicalComplex₂.flip
      (((abelianHypercoverRows X W U).mapHomologicalComplex (.up ℤ)).obj E)).X (p : ℤ) ≅
      (((abelianHypercoverSections X W U ⋙
        (CategoryTheory.evaluation _ _).obj ⦋p⦌).mapHomologicalComplex
        (.up ℤ)).obj E) := by
  refine HomologicalComplex.Hom.isoOfComponents (fun q ↦
    (((AlgebraicTopology.alternatingCofaceMapComplex _).obj
      ((abelianHypercoverSections X W U).obj (E.X q))).extendXIso
        ComplexShape.embeddingUpNat (i := p) rfl)) ?_
  intro q r h
  symm
  change ((ComplexShape.embeddingUpNat.extendFunctor _).map
    ((AlgebraicTopology.alternatingCofaceMapComplex _).map
      ((abelianHypercoverSections X W U).map (E.d q r)))).f (p : ℤ) ≫ _ = _
  erw [HomologicalComplex.extendMap_f _ ComplexShape.embeddingUpNat (i := p) rfl]
  simp

private theorem sectionBicomplex_zero
    (E : CochainComplex (Sheaf (topology X) AddCommGrpCat.{u + 1}) ℤ)
    (N : ℤ) [E.IsStrictlyGE N] (p q : ℤ) (h : p < 0 ∨ q < N) :
    IsZero (((HomologicalComplex₂.flip
      (((abelianHypercoverRows X W U).mapHomologicalComplex (.up ℤ)).obj E)).X p).X q) := by
  change IsZero (((abelianHypercoverRows X W U).obj (E.X q)).X p)
  rcases h with hp | hq
  · exact HomologicalComplex.isZero_extend_X _ ComplexShape.embeddingUpNat p (by
      intro i hi
      change (i : ℤ) = p at hi
      omega)
  · exact (HomologicalComplex.eval _ _ p).map_isZero
      ((abelianHypercoverRows X W U).map_isZero (E.isZero_of_isStrictlyGE N q hq))

-- Comparing section-column maps unfolds the section and extension functor compositions.
set_option backward.isDefEq.respectTransparency false in
/-- Weakly contractible terms suffice for bounded-below quasi-isomorphism invariance;
no covering or matching-map hypotheses are needed for this comparison.
Source: Stacks Project, Tags 09A2 and 0946 (1).
(auxiliary; not a blueprint node).

Proof: choose a common lower bound N. In each nonnegative simplicial degree p,
evaluation at U_p preserves homology by weak contractibility. Thus the vertical
complex map is a quasi-isomorphism.
The extension-by-zero column isomorphisms identify these vertical maps with the
columns of the section bicomplex map. Negative columns are zero. Both bicomplexes
vanish for p<0 or q<N, so bounded-below total-column comparison applies. -/
theorem abelianHypercoverTotal_map_quasiIso_of_weaklyContractible
    (haff : ∀ p : ℕ, IsAffine (U _⦋p⦌).left.left)
    (hweak : ∀ (p : ℕ) (F G : Sheaf (topology X) (Type (u + 1))) (f : F ⟶ G),
      Epi f → Function.Surjective (f.hom.app (op (U _⦋p⦌).left)))
    (E F : CochainComplex.Plus (Sheaf (topology X) AddCommGrpCat.{u + 1}))
    (f : E ⟶ F) (hf : QuasiIso f.hom) :
    QuasiIso ((abelianHypercoverTotal X W U).map f.hom) := by
  have : QuasiIso f.hom := hf
  obtain ⟨NE, hE⟩ := E.property
  obtain ⟨NF, hF⟩ := F.property
  let N := min NE NF
  have := hE
  have := hF
  have := E.obj.isStrictlyGE_of_ge N NE (min_le_left _ _)
  have := F.obj.isStrictlyGE_of_ge N NF (min_le_right _ _)
  let g := (HomologicalComplex₂.flipFunctor _ (.up ℤ) (.up ℤ)).map
    (((abelianHypercoverRows X W U).mapHomologicalComplex (.up ℤ)).map f.hom)
  apply HomologicalComplex₂.quasiIso_totalMap_of_boundedBelow_columns g 0 N
    (sectionBicomplex_zero X W U E.obj N) (sectionBicomplex_zero X W U F.obj N)
  intro p
  by_cases hp : 0 ≤ p
  · obtain ⟨p, rfl⟩ := Int.eq_ofNat_of_zero_le hp
    let ev := abelianHypercoverSections X W U ⋙ (CategoryTheory.evaluation _ _).obj ⦋p⦌
    have : ev.PreservesHomology := sectionsEvaluation_preservesHomology X W U p (haff p) (hweak p)
    have : QuasiIso ((ev.mapHomologicalComplex (.up ℤ)).map f.hom) := inferInstance
    apply (quasiIso_iff_of_arrow_mk_iso (g.f (p : ℤ)) _
      (Arrow.isoMk (sectionColumnIso X W U E.obj p)
        (sectionColumnIso X W U F.obj p) ?_)).mpr this
    apply HomologicalComplex.hom_ext
    intro q
    dsimp only [HomologicalComplex.comp_f, HomologicalComplex.Hom.isoOfComponents_hom_f]
    symm
    change ((ComplexShape.embeddingUpNat.extendFunctor _).map
      ((AlgebraicTopology.alternatingCofaceMapComplex _).map
        ((abelianHypercoverSections X W U).map (f.hom.f q)))).f (p : ℤ) ≫ _ = _
    erw [HomologicalComplex.extendMap_f _ ComplexShape.embeddingUpNat (i := p) rfl]
    simp [sectionColumnIso]
    rfl
  · have hzero (A : CochainComplex.Plus (Sheaf (topology X) AddCommGrpCat.{u + 1})) :
        IsZero ((HomologicalComplex₂.flip
          (((abelianHypercoverRows X W U).mapHomologicalComplex (.up ℤ)).obj A.obj)).X p) := by
      rw [IsZero.iff_id_eq_zero]
      apply HomologicalComplex.hom_ext
      intro q
      change (𝟙 (((abelianHypercoverRows X W U).obj (A.obj.X q)).X p)) = 0
      exact (HomologicalComplex.isZero_extend_X _ ComplexShape.embeddingUpNat p (by
        intro i hi
        change (i : ℤ) = p at hi
        omega)).eq_of_src _ _
    have : IsIso (g.f p) := (hzero E).isIso (hzero F) _
    infer_instance

end AlgebraicGeometry.Scheme.ProEt
