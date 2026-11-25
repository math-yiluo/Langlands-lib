/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.Hypercover.ProEtaleHypercoverAugmentation
public import Mathlib.Algebra.Homology.CochainComplexPlus
import WeilConjectures.Algebra.Homology.BoundedBelowAugmentation
import Mathlib.Algebra.Homology.TotalComplex
import Mathlib.Algebra.Homology.Embedding.CochainComplex
import WeilConjectures.Algebra.Homology.BoundedBelowTotalComparison
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.Algebra.Homology.TotalComplexSymmetry
import WeilConjectures.FromJoel.Algebra.Homology.BicomplexColumns

/-! # From injective row descent to bounded-below injective descent

## References

* Stacks Project, Tag 09A2, comparison with a bounded-below injective complex
* Stacks Project, Tags 09A2 and 01GE
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial

namespace AlgebraicGeometry.Scheme.ProEt

variable (X : Scheme.{u}) (R : Sheaf (topology X) CommRingCat.{u + 1})
  (W : X.ProEt) (U : SimplicialObject (Over W))

-- The comparison expands the evaluation, single-complex and section functors.
set_option backward.isDefEq.respectTransparency false in
/-- Exact descent for individual injective sheaves implies descent for a
bounded-below complex of injective sheaves. -/
theorem hypercoverAugmentation_quasiIso_of_injective_rows
    (hrows : ∀ (I : ringedSiteModules.{u + 1}
        ((sheafCompose (topology X)
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R)), Injective I →
      QuasiIso (hypercoverRowAugmentationComplex X R W U I))
    (J : CochainComplex.Plus (ringedSiteModules.{u + 1}
      ((sheafCompose (topology X)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R)))
    (hJ : ∀ n : ℤ, Injective (J.obj.X n)) :
    QuasiIso ((hypercoverAugmentation X R W U).app J.obj) := by
  let K := HomologicalComplex₂.flip
    (((hypercoverSectionRows X R W U).mapHomologicalComplex (.up ℤ)).obj J.obj)
  let A : CochainComplex _ ℤ :=
    ((SheafOfModules.evaluation _ (op W)).mapHomologicalComplex (.up ℤ)).obj J.obj
  let a : A ⟶ K.X 0 :=
    { f := fun n ↦ hypercoverRowAugmentation X R W U (J.obj.X n)
      comm' := fun n m _ ↦
        (hypercoverRowAugmentation_naturality X R W U (J.obj.d n m)).symm }
  have ha : ∀ p, (ComplexShape.up ℤ).Rel 0 p → a ≫ K.d 0 p = 0 := by
    intro p hp
    obtain rfl : p = 1 := by simpa using hp.symm
    apply HomologicalComplex.hom_ext
    intro n
    exact hypercoverRowAugmentation_d X R W U (J.obj.X n)
  obtain ⟨N, hN⟩ := J.property
  have := hN
  have : A.IsStrictlyGE N := by
    apply (CochainComplex.isStrictlyGE_iff A N).mpr
    intro n hn
    exact (SheafOfModules.evaluation _ (op W)).map_isZero
      (J.obj.isZero_of_isStrictlyGE N n hn)
  refine HomologicalComplex₂.quasiIso_of_boundedBelow_row_augmentation K A N ?_ a ha
    ((hypercoverAugmentation X R W U).app J.obj) (fun _ ↦ rfl) ?_
  · intro p q h
    change IsZero (((hypercoverSectionRows X R W U).obj (J.obj.X q)).X p)
    rcases h with hp | hq
    · exact HomologicalComplex.isZero_extend_X _ ComplexShape.embeddingUpNat p (by
        intro i hi
        change (i : ℤ) = p at hi
        omega)
    · exact (HomologicalComplex.eval _ _ p).map_isZero
        ((hypercoverSectionRows X R W U).map_isZero
          (J.obj.isZero_of_isStrictlyGE N q hq))
  · intro n
    apply (quasiIso_iff_of_arrow_mk_iso _ _
      (Arrow.isoMk
        ((HomologicalComplex.singleMapHomologicalComplex
          (HomologicalComplex.eval _ (.up ℤ) n) (.up ℤ) 0).app A)
        (Iso.refl _) ?_)).mpr (hrows (J.obj.X n) (hJ n))
    apply HomologicalComplex.hom_ext
    intro p
    by_cases hp : p = 0
    · subst p
      dsimp only [HomologicalComplex.comp_f, Arrow.mk_hom,
        Iso.refl_hom, HomologicalComplex.id_f, Category.comp_id]
      simp only [Iso.app_hom, HomologicalComplex.singleMapHomologicalComplex_hom_app_self]
      dsimp only [hypercoverRowAugmentationComplex]
      simp only [HomologicalComplex.mkHomFromSingle_f]
      change ((HomologicalComplex.singleObjXSelf (.up ℤ) 0 A).hom.f n ≫
        (HomologicalComplex.singleObjXSelf (.up ℤ) 0 (A.X n)).inv) ≫
          (HomologicalComplex.singleObjXSelf (.up ℤ) 0 (A.X n)).hom ≫ _ = _
      simp only [Category.assoc, Iso.inv_hom_id_assoc, Category.comp_id]
      change _ = ((HomologicalComplex.mkHomFromSingle a ha).f 0).f n
      simp only [HomologicalComplex.mkHomFromSingle_f]
      rfl
    · exact ((HomologicalComplex.eval _ (.up ℤ) n).map_isZero
        (HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 A p hp)).eq_of_src _ _

end AlgebraicGeometry.Scheme.ProEt
