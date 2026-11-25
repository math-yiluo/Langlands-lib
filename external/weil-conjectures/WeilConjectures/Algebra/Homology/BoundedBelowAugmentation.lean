/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Homology.TotalComplex
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
import WeilConjectures.Algebra.Homology.BoundedBelowTotalComparison
import WeilConjectures.FromJoel.Algebra.Homology.BicomplexColumns

/-! # Bounded-below row augmentation comparison
Source: Stacks Project, Tags 0133 and 01EQ.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open ComplexShape HomologicalComplex

namespace HomologicalComplex₂

variable {C : Type*} [Category* C] [Abelian C] [HasCoproducts.{0} C]

set_option backward.isDefEq.respectTransparency false in
/-- A rowwise quasi-isomorphic augmentation of a bounded-below bicomplex is
quasi-isomorphic on totals.
Source: Stacks Project, Tags 0133 and 01EQ.
(auxiliary; not a blueprint node).
Proof: regard the augmentation as a map from the single column in degree zero.
Its row maps are quasi-isomorphisms by hypothesis. Both bicomplexes have common
lower bounds, so row comparison makes the total map a quasi-isomorphism. The
single-column total is isomorphic degreewise to the augmenting complex. Its
inverse followed by the total map has the stated components, hence equals b. -/
theorem quasiIso_of_boundedBelow_row_augmentation
    (K : HomologicalComplex₂ C (up ℤ) (up ℤ)) (A : CochainComplex C ℤ) (N : ℤ)
    [A.IsStrictlyGE N]
    (hK : ∀ p q : ℤ, p < 0 ∨ q < N → IsZero ((K.X p).X q))
    (a : A ⟶ K.X 0) (ha : ∀ p, (up ℤ).Rel 0 p → a ≫ K.d 0 p = 0)
    (b : A ⟶ K.total (up ℤ))
    (hb : ∀ n : ℤ, b.f n = a.f n ≫ K.ιTotal (up ℤ) 0 n n (by simp))
    (hrow : ∀ n : ℤ, QuasiIso
      (((flipFunctor C (up ℤ) (up ℤ)).map (mkHomFromSingle a ha)).f n)) :
    QuasiIso b := by
  let S := (singleColumn C (up ℤ) (up ℤ) 0).obj A
  let f : S ⟶ K := mkHomFromSingle a ha
  have ht : QuasiIso (total.map f (up ℤ)) := by
    apply quasiIso_totalMap_of_boundedBelow_rows f 0 N ?_ hK hrow
    intro p q h
    rcases h with hp | hq
    · exact isZero_singleColumn_X_X (up ℤ) A 0 p (by omega) q
    · by_cases hp : p = 0
      · subst p
        exact IsZero.of_iso (A.isZero_of_isStrictlyGE N q hq)
          (singleColumnXXIso (up ℤ) A 0 q)
      · exact isZero_singleColumn_X_X (up ℤ) A 0 p hp q
  let e : A ⟶ S.total (up ℤ) :=
    { f := fun n ↦ (singleColumnObjTotalXIso A 0 n n (by simp)).inv
      comm' := by
        intro n m h
        dsimp only [S]
        simp only [singleColumnObjTotalXIso_inv, total_d, Preadditive.comp_add,
          Category.assoc, ι_D₁, singleColumn_d₁, comp_zero, ι_D₂, zero_add]
        rw [singleColumn_d₂ _ _ _ _ _ _ _ m h m (by simp)]
        simp only [ε₂_def, ε_zero, one_smul, Iso.inv_hom_id_assoc] }
  have he : IsIso e := by
    apply HomologicalComplex.Hom.isIso_of_components
  have heq : e ≫ total.map f (up ℤ) = b := by
    apply HomologicalComplex.hom_ext
    intro n
    dsimp only [HomologicalComplex.comp_f, e]
    rw [singleColumnObjTotalXIso_inv, Category.assoc, ιTotal_map, hb]
    dsimp only [f]
    rw [mkHomFromSingle_f]
    simp [singleColumnXXIso, singleColumnXIso, ← Category.assoc,
      ← HomologicalComplex.comp_f]
  rw [← heq]
  infer_instance

end HomologicalComplex₂
