/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtaleAbelianHypercoverAugmentation
public import Mathlib.Algebra.Homology.CochainComplexPlus
import WeilConjectures.Algebra.Homology.BoundedBelowAugmentation

/-! # From injective row descent to bounded-below injective descent
Source: Stacks Project, Tag 09A2, comparison with a bounded-below injective complex.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial

namespace AlgebraicGeometry.Scheme.ProEt

variable (X : Scheme.{u})
  (W : X.ProEt) (U : SimplicialObject (Over W))

-- The comparison expands the evaluation, single-complex and section functors.
set_option backward.isDefEq.respectTransparency false in
/-- Exact augmented section rows imply descent for a bounded-below complex.
Source: Stacks Project, Tags 09A2 and 01GE.
(auxiliary; not a blueprint node).
Proof: use the canonical restriction as a chain augmentation into the zeroth
simplicial column. Naturality makes it a map of complexes. Its transposed column
in coefficient degree n is precisely the single-sheaf row augmentation, hence is
quasi-isomorphic by hypothesis. The bicomplex vanishes below simplicial degree zero
and below a lower bound for J. Apply bounded-below row augmentation comparison. -/
theorem abelianHypercoverAugmentation_quasiIso_of_rows
    (J : CochainComplex.Plus (Sheaf (topology X) AddCommGrpCat.{u + 1}))
    (hrows : ∀ n : ℤ,
      QuasiIso (abelianHypercoverRowAugmentationComplex X W U (J.obj.X n))) :
    QuasiIso ((abelianHypercoverAugmentation X W U).app J.obj) := by
  let K := HomologicalComplex₂.flip
    (((abelianHypercoverRows X W U).mapHomologicalComplex (.up ℤ)).obj J.obj)
  let A : CochainComplex _ ℤ :=
    (((sheafSections (topology X) AddCommGrpCat.{u + 1}).obj
      (op W)).mapHomologicalComplex (.up ℤ)).obj J.obj
  let a : A ⟶ K.X 0 :=
    { f := fun n ↦ abelianHypercoverRowAugmentation X W U (J.obj.X n)
      comm' := fun n m _ ↦
        (abelianHypercoverRowAugmentation_naturality X W U (J.obj.d n m)).symm }
  have ha : ∀ p, (ComplexShape.up ℤ).Rel 0 p → a ≫ K.d 0 p = 0 := by
    intro p hp
    obtain rfl : p = 1 := by simpa using hp.symm
    apply HomologicalComplex.hom_ext
    intro n
    exact abelianHypercoverRowAugmentation_d X W U (J.obj.X n)
  obtain ⟨N, hN⟩ := J.property
  have := hN
  have : A.IsStrictlyGE N := by
    apply (CochainComplex.isStrictlyGE_iff A N).mpr
    intro n hn
    exact ((sheafSections (topology X) AddCommGrpCat.{u + 1}).obj (op W)).map_isZero
      (J.obj.isZero_of_isStrictlyGE N n hn)
  refine HomologicalComplex₂.quasiIso_of_boundedBelow_row_augmentation K A N ?_ a ha
    ((abelianHypercoverAugmentation X W U).app J.obj) (fun _ ↦ rfl) ?_
  · intro p q h
    change IsZero (((abelianHypercoverRows X W U).obj (J.obj.X q)).X p)
    rcases h with hp | hq
    · exact HomologicalComplex.isZero_extend_X _ ComplexShape.embeddingUpNat p (by
        intro i hi
        change (i : ℤ) = p at hi
        omega)
    · exact (HomologicalComplex.eval _ _ p).map_isZero
        ((abelianHypercoverRows X W U).map_isZero
          (J.obj.isZero_of_isStrictlyGE N q hq))
  · intro n
    apply (quasiIso_iff_of_arrow_mk_iso _ _
      (Arrow.isoMk
        ((HomologicalComplex.singleMapHomologicalComplex
          (HomologicalComplex.eval _ (.up ℤ) n) (.up ℤ) 0).app A)
        (Iso.refl _) ?_)).mpr (hrows n)
    apply HomologicalComplex.hom_ext
    intro p
    by_cases hp : p = 0
    · subst p
      dsimp only [HomologicalComplex.comp_f, Arrow.mk_hom,
        Iso.refl_hom, HomologicalComplex.id_f, Category.comp_id]
      erw [HomologicalComplex.singleMapHomologicalComplex_hom_app_self]
      dsimp only [abelianHypercoverRowAugmentationComplex]
      rw [HomologicalComplex.mkHomFromSingle_f]
      change ((HomologicalComplex.singleObjXSelf (.up ℤ) 0 A).hom.f n ≫
        (HomologicalComplex.singleObjXSelf (.up ℤ) 0 (A.X n)).inv) ≫
          (HomologicalComplex.singleObjXSelf (.up ℤ) 0 (A.X n)).hom ≫ _ = _
      simp only [Category.assoc, Iso.inv_hom_id_assoc, Category.comp_id]
      change _ = ((HomologicalComplex.mkHomFromSingle a ha).f 0).f n
      rw [HomologicalComplex.mkHomFromSingle_f]
      rfl
    · exact ((HomologicalComplex.eval _ (.up ℤ) n).map_isZero
        (HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 A p hp)).eq_of_src _ _

end AlgebraicGeometry.Scheme.ProEt
