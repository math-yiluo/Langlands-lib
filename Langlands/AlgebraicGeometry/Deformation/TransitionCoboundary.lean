import Langlands.AlgebraicGeometry.Deformation.TransitionCorrection

/-! # Lifted transition maps with a coboundary obstruction can be corrected to a cocycle -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing Opposite TopologicalSpace

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.AlgebraicGeometry.Deformation.TransitionObstruction

open SquareZeroAffinePairs ElementaryIdealCoefficients ElementaryMorphismLifts ElementaryLiftCech
open AffineOpenQuotientSections Langlands.Cohomology
open Langlands.AlgebraicGeometry.TwistedOpenGluing
open Langlands.AlgebraicGeometry.Modules.CechResolution.AllSeq

variable {R : Type u} [CommRing R] [IsLocalRing R]

omit [IsLocalRing R] in
theorem res_congr_index {X : Scheme.{u}} {ι : Type u} {U : ι → X.Opens} {p : ℕ}
    (z : Cech.C (Cech.ab X.presheaf) U p) {σ σ' : Fin (p + 1) → ι} (e : σ = σ')
    {W : X.Opens} (h : W ≤ Cech.inter U σ) (h' : W ≤ Cech.inter U σ') :
    Cech.res (P := Cech.ab X.presheaf) h (z σ) = Cech.res (P := Cech.ab X.presheaf) h' (z σ') := by
  subst e
  rfl

omit [IsLocalRing R] in
theorem alternating_three {G : Type*} [AddCommGroup G] {a b c o : G} (h : a + -b + c = o) :
    o = c + a - b := by
  rw [← h]
  abel

section Coboundary

variable {Y : Over (Spec (CommRingCat.of R))} [IsSeparated Y.hom] [Smooth Y.hom]
  {Z : Target R} {I : Ideal R} [Fact (maximalIdeal R * I = ⊥)] (b : Z.Coordinates I)
  (F : Reduction Y (maximalIdeal R))

namespace Family

variable (D : Family Y)

omit [IsSeparated Y.hom] [Smooth Y.hom] in
theorem le_inter_two (l m : D.L) :
    F.toOriginal ⁻¹ᵁ (D.V l ⊓ D.V m) ≤ Cech.inter (D.cover F) ![l, m] :=
  le_iInf fun i ↦ by
    fin_cases i
    · exact F.toOriginal.preimage_mono inf_le_left
    · exact F.toOriginal.preimage_mono inf_le_right

omit [IsSeparated Y.hom] [Smooth Y.hom] in
theorem le_inter_three (l m n : D.L) :
    F.toOriginal ⁻¹ᵁ (D.V l ⊓ D.V m ⊓ D.V n) ≤ Cech.inter (D.cover F) ![l, m, n] :=
  le_iInf fun i ↦ by
    fin_cases i
    · exact F.toOriginal.preimage_mono (inf_le_left.trans inf_le_left)
    · exact F.toOriginal.preimage_mono (inf_le_left.trans inf_le_right)
    · exact F.toOriginal.preimage_mono inf_le_right

/-- The values of a Čech `1`-cochain on the pairwise overlaps. -/
def pairValues (y : Fin b.cotangentRank × Fin b.idealRank →
      cochain F.obj.hom (D.cover F) (unitModule F.obj.left) 1)
    (l m : D.L) (j : Fin b.cotangentRank × Fin b.idealRank) :
    Γ(F.obj.left, F.toOriginal ⁻¹ᵁ (D.V l ⊓ D.V m)) :=
  Cech.res (P := Cech.ab F.obj.left.presheaf) (D.le_inter_two F l m)
    ((y j : Cech.C (Cech.ab F.obj.left.presheaf) (D.cover F) 1) ![l, m])

variable (hD : D.Agrees I) (π : Y ⟶ Z.X)
  (y : Fin b.cotangentRank × Fin b.idealRank →
    cochain F.obj.hom (D.cover F) (unitModule F.obj.left) 1)
  (hy : ∀ j, dCochain F.obj.hom (D.cover F) (unitModule F.obj.left) 1 (y j) =
    (D.cocycle b F hD π j : cochain F.obj.hom (D.cover F) (unitModule F.obj.left) 2))

include hy in
/-- If the obstruction is the coboundary of `y`, it is the alternating sum of the values of `y`
on the faces of each triple overlap. -/
theorem obstruction_eq_of_coboundary (l m n : D.L) (j : Fin b.cotangentRank × Fin b.idealRank) :
    D.obstruction b F hD π l m n j =
      (F.obj.left.presheaf.map (homOfLE (F.toOriginal.preimage_mono
          (inf_le_left : D.V l ⊓ D.V m ⊓ D.V n ≤ _))).op).hom (D.pairValues b F y l m j) +
        (F.obj.left.presheaf.map (homOfLE (F.toOriginal.preimage_mono
          (inf₃_le_bc (D.V l) (D.V m) (D.V n)))).op).hom (D.pairValues b F y m n j) -
        (F.obj.left.presheaf.map (homOfLE (F.toOriginal.preimage_mono
          (inf₃_le_ac (D.V l) (D.V m) (D.V n)))).op).hom (D.pairValues b F y l n j) := by
  have h1 := congrFun (dCochain_unit F.obj.hom (D.cover F) 1 (y j)) ![l, m, n]
  rw [hy j, Cech.d_apply, Fin.sum_univ_three] at h1
  have h2 := congrArg (Cech.res (P := Cech.ab F.obj.left.presheaf) (D.le_inter_three F l m n)) h1
  simp only [map_add, map_zsmul, Cech.res_res] at h2
  have e0 : (![l, m, n] ∘ (0 : Fin 3).succAbove) = ![m, n] := by
    funext i; fin_cases i <;> rfl
  have e1 : (![l, m, n] ∘ (1 : Fin 3).succAbove) = ![l, n] := by
    funext i; fin_cases i <;> rfl
  have e2 : (![l, m, n] ∘ (2 : Fin 3).succAbove) = ![l, m] := by
    funext i; fin_cases i <;> rfl
  rw [res_congr_index _ e0 _ ((F.toOriginal.preimage_mono (inf₃_le_bc (D.V l) (D.V m) (D.V n))).trans
      (D.le_inter_two F m n)),
    res_congr_index _ e1 _ ((F.toOriginal.preimage_mono (inf₃_le_ac (D.V l) (D.V m) (D.V n))).trans
      (D.le_inter_two F l n)),
    res_congr_index _ e2 _ ((F.toOriginal.preimage_mono
      (inf_le_left : D.V l ⊓ D.V m ⊓ D.V n ≤ _)).trans (D.le_inter_two F l m))] at h2
  simp only [Fin.val_zero, Fin.val_one, Fin.val_two, pow_zero, pow_one, neg_one_sq, one_zsmul,
    neg_one_zsmul] at h2
  have hs := Cech.res_self (P := Cech.ab F.obj.left.presheaf)
    (V := F.toOriginal ⁻¹ᵁ (D.V l ⊓ D.V m ⊓ D.V n))
    ((D.le_inter_three F l m n).trans (D.inter_le_three F ![l, m, n]))
    (D.obstruction b F hD π l m n j)
  rw [cocycle_apply, map_eq_res, Cech.res_res] at h2
  simp only [map_eq_res, pairValues, Cech.res_res]
  exact alternating_three (hs.symm.trans h2).symm

end Family

end Coboundary

omit [IsLocalRing R] in
/-- Restriction between equal opens is injective. -/
theorem map_homOfLE_injective {X : Scheme.{u}} {U V : X.Opens} (h : V ≤ U) (h' : U ≤ V) :
    Function.Injective (X.presheaf.map (homOfLE h).op).hom := by
  obtain rfl : V = U := le_antisymm h h'
  rw [show homOfLE h = 𝟙 V from Subsingleton.elim _ _, op_id, X.presheaf.map_id]
  exact fun _ _ e ↦ e

section Self

variable {Y : Over (Spec (CommRingCat.of R))} [IsSeparated Y.hom] [Smooth Y.hom]
  {Z : Target R} {I : Ideal R} [Fact (maximalIdeal R * I = ⊥)] (b : Z.Coordinates I)
  (F : Reduction Y (maximalIdeal R))

namespace Family

variable (D : Family Y)

omit [IsSeparated Y.hom] [Smooth Y.hom] in
theorem comp_eq_direct_self (l : D.L) (h : D.θ l l = (D.V l ⊓ D.V l).ι) :
    D.comp l l l = D.direct l l l := by
  rw [comp, direct, h, lift₃_ι, h, Scheme.homOfLE_ι]

variable (hD : D.Agrees I) (π : Y ⟶ Z.X)

theorem obstruction_self (l : D.L) (h : D.θ l l = (D.V l ⊓ D.V l).ι)
    (j : Fin b.cotangentRank × Fin b.idealRank) :
    D.obstruction b F hD π l l l j = 0 := by
  unfold obstruction
  rw [openDifference_pt_congr b F (D.affine₃ l l l) (congrArg (· ≫ π.left)
    (D.comp_eq_direct_self l h)) rfl _ _ (D.direct_π_over π l l l) (D.direct_π_over π l l l) _
    rfl j]
  exact openDifference_same b F _ _ j

variable (y : Fin b.cotangentRank × Fin b.idealRank →
    cochain F.obj.hom (D.cover F) (unitModule F.obj.left) 1)
  (hy : ∀ j, dCochain F.obj.hom (D.cover F) (unitModule F.obj.left) 1 (y j) =
    (D.cocycle b F hD π j : cochain F.obj.hom (D.cover F) (unitModule F.obj.left) 2))

include hy in
/-- A cochain whose coboundary is the obstruction vanishes on the diagonal when the diagonal
transitions are the inclusions. -/
theorem pairValues_self (l : D.L) (h : D.θ l l = (D.V l ⊓ D.V l).ι)
    (j : Fin b.cotangentRank × Fin b.idealRank) : D.pairValues b F y l l j = 0 := by
  have e := D.obstruction_eq_of_coboundary b F hD π y hy l l l j
  rw [D.obstruction_self b F hD π l h j, add_sub_cancel_right] at e
  apply map_homOfLE_injective (X := F.obj.left)
    (F.toOriginal.preimage_mono (inf_le_left : D.V l ⊓ D.V l ⊓ D.V l ≤ _))
    (F.toOriginal.preimage_mono (le_inf le_rfl inf_le_left))
  rw [← e, map_zero]

end Family

end Self

section Exact

variable {Z : Target R} [IsSeparated Z.X.hom] [Smooth Z.X.hom] {I : Ideal R}
  [Fact (maximalIdeal R * I = ⊥)] (hI : I ≤ maximalIdeal R) (b : Z.Coordinates I)
  (F : Reduction Z.X (maximalIdeal R))

namespace Family

variable (D : Family Z.X) (hD : D.Agrees I)
  (y : Fin b.cotangentRank × Fin b.idealRank →
    cochain F.obj.hom (D.cover F) (unitModule F.obj.left) 1)
  (hy : ∀ j, dCochain F.obj.hom (D.cover F) (unitModule F.obj.left) 1 (y j) =
    (D.cocycle b F hD (𝟙 Z.X) j : cochain F.obj.hom (D.cover F) (unitModule F.obj.left) 2))

/-- The family corrected by the pairwise values of a supplied Čech `1`-cochain `y`. The
vanishing and exactness theorems below assume that the coboundary of `y` is the obstruction
(`hy`). -/
abbrev exactFamily : Family Z.X := D.correctedFamily hI b F (D.pairValues b F y)

include hD in
theorem agrees_exactFamily : (D.exactFamily hI b F y).Agrees I :=
  D.agrees_replace _ _ _ _ (D.agree_corrected b F (D.pairValues b F y)) hD

include hy in
theorem obstruction_exactFamily (l m n : D.L) (j : Fin b.cotangentRank × Fin b.idealRank) :
    (D.exactFamily hI b F y).obstruction b F (D.agrees_exactFamily hI b F hD y) (𝟙 Z.X)
      l m n j = 0 := by
  rw [D.obstruction_replace b F _ _ _ _ (D.agree_corrected b F (D.pairValues b F y)) (𝟙 Z.X)
    hD l m n j]
  simp only [D.diff_corrected hI b F (D.pairValues b F y)]
  rw [D.obstruction_eq_of_coboundary b F hD (𝟙 Z.X) y hy l m n j]
  abel

include hy in
/-- The corrected transitions satisfy the cocycle identity exactly. -/
theorem exactFamily_comp (l m n : D.L) :
    (D.exactFamily hI b F y).comp l m n = (D.exactFamily hI b F y).direct l m n := by
  have h := eq_of_openDifference_eq_zero b F ((D.exactFamily hI b F y).affine₃ l m n)
    (pt _ ((D.exactFamily hI b F y).comp l m n ≫ (𝟙 Z.X : Z.X ⟶ Z.X).left)
      ((D.exactFamily hI b F y).comp_π_over (𝟙 Z.X) l m n))
    (pt _ ((D.exactFamily hI b F y).direct l m n ≫ (𝟙 Z.X : Z.X ⟶ Z.X).left)
      ((D.exactFamily hI b F y).direct_π_over (𝟙 Z.X) l m n))
    (agree_pt_of _ _ (((D.agrees_exactFamily hI b F hD y) l m n).comp _))
    (D.obstruction_exactFamily hI b F hD y hy l m n)
  have h' := eq_of_pt_eq _ _ _ h
  simpa only [Over.id_left, Category.comp_id] using h'

include hy in
/-- The corrected transitions are the inclusions on the diagonal if the original ones are. -/
theorem exactFamily_self (hself : ∀ l, D.θ l l = (D.V l ⊓ D.V l).ι) (l : D.L) :
    (D.exactFamily hI b F y).θ l l = (D.V l ⊓ D.V l).ι := by
  have h := eq_of_openDifference_eq_zero b F (D.affine₂ l l) (D.tpt l l)
    (pt _ ((D.exactFamily hI b F y).θ l l ≫ (𝟙 Z.X : Z.X ⟶ Z.X).left)
      ((D.exactFamily hI b F y).θ_π_over (𝟙 Z.X) l l))
    (agree_pt_of _ _ ((D.agree_corrected b F (D.pairValues b F y) l l).comp _))
    (fun j ↦ (D.diff_corrected hI b F (D.pairValues b F y) l l j).trans
      (D.pairValues_self b F hD (𝟙 Z.X) y hy l (hself l) j))
  have h' := eq_of_pt_eq _ _ _ h
  simp only [Over.id_left, Category.comp_id] at h'
  change D.corrected b F (D.pairValues b F y) l l = _
  rw [← h', hself l]

end Family

end Exact


end Langlands.AlgebraicGeometry.Deformation.TransitionObstruction
