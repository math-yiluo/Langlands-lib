import Langlands.GroupScheme.Rational.CocharacterWeightSums
import Langlands.GroupScheme.Absolute.Borel
import Langlands.GroupScheme.Torus.WeightDecomposition

/-! # Weights of a cocharacter on the actual Lie algebra through a split torus -/

set_option backward.isDefEq.respectTransparency false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

section Ring

variable {R : CommRingCat.{u}} {T T' : CommGroupScheme (Spec R)} {G : GroupScheme (Spec R)}
  [IsAffineHom G.X.hom]

end Ring

section Field

variable {k : Type u} [Field k] {T T' : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]

omit [LocallyOfFiniteType G.X.hom] in
/-- The weight spaces for `j` of the characters `χ` with `f ≫ χ = ψ` lie in the weight space of
`ψ` for `f ≫ j`. -/
theorem iSup_weightSpace_le_weightSpace_comp (f : T' ⟶ T) (j : T.toGrp ⟶ G)
    (ψ : characterLattice T') :
    (⨆ (χ : characterLattice T) (_ : f ≫ χ = ψ), weightSpace j χ) ≤
      weightSpace (CommGroupScheme.groupHom f ≫ j) ψ := by
  refine iSup₂_le fun χ hχ => ?_
  rw [← hχ]
  exact weightSpace_le_comp f j χ

/-- Grouping the weight spaces of a split torus `T` by their restriction along `f : T' ⟶ T`
still spans the whole actual Lie algebra. -/
theorem iSup_iSup_weightSpace_eq_top (hT : IsSplitTorus T.toGrp) (f : T' ⟶ T)
    (j : T.toGrp ⟶ G) :
    (⨆ (ψ : characterLattice T') (χ : characterLattice T) (_ : f ≫ χ = ψ),
      weightSpace j χ) = ⊤ := by
  classical
  rw [iSup_comm]
  simp only [iSup_iSup_eq_right]
  exact (isInternal_weightSpace_of_isSplitTorus k G T hT j).submodule_iSup_eq_top

theorem weightSpace_comp_eq_iSup_fiber (hT : IsSplitTorus T.toGrp) (hT' : IsSplitTorus T'.toGrp)
    (f : T' ⟶ T) (j : T.toGrp ⟶ G) (ψ : characterLattice T') :
    weightSpace (CommGroupScheme.groupHom f ≫ j) ψ =
      ⨆ (χ : characterLattice T) (_ : f ≫ χ = ψ), weightSpace j χ := by
  classical
  have hind := (isInternal_weightSpace_of_isSplitTorus k G T' hT'
    (CommGroupScheme.groupHom f ≫ j)).submodule_iSupIndep
  exact (congrFun ((hind.le_iff_eq_of_iSup_eq_top (iSup_iSup_weightSpace_eq_top hT f j)).mp
    (fun ψ' => iSup_weightSpace_le_weightSpace_comp f j ψ')) ψ).symm

omit [LocallyOfFiniteType G.X.hom] in
/-- The nonnegative weight span of a cocharacter `ν` for `j : T ⟶ G`: the sum of the weight
spaces for `j` of the characters `χ` of `T` with `⟨χ, ν⟩ ≥ 0`. -/
def nonnegativeWeightSpan (j : T.toGrp ⟶ G) (ν : cocharacterLattice T) :=
  ⨆ (χ : characterLattice T) (_ : 0 ≤ latticePairing T χ ν), weightSpace j χ

omit [LocallyOfFiniteType G.X.hom] in
theorem nonnegativeWeightSpan_def (j : T.toGrp ⟶ G) (ν : cocharacterLattice T) :
    nonnegativeWeightSpan j ν =
      ⨆ (χ : characterLattice T) (_ : 0 ≤ latticePairing T χ ν), weightSpace j χ :=
  rfl

/-- The sum of the nonnegative weight spaces of `𝔾_m` acting through `ν ≫ j` is the sum of the
weight spaces for `j` of the characters `χ` with `⟨χ, ν⟩ ≥ 0`. -/
theorem iSup_nat_weightSpace_cocharacter (hT : IsSplitTorus T.toGrp)
    (ν : cocharacterLattice T) (j : T.toGrp ⟶ G) :
    (⨆ n : ℕ, weightSpace (CommGroupScheme.groupHom ν ≫ j) (Gm.powerHom _ n)) =
      ⨆ (χ : characterLattice T) (_ : 0 ≤ latticePairing T χ ν), weightSpace j χ := by
  simp only [weightSpace_cocharacter_eq_iSup hT j ν]
  rw [iSup_comm]
  refine iSup_congr fun χ => le_antisymm ?_ ?_
  · refine iSup₂_le fun n hn => le_iSup_of_le (hn ▸ Int.natCast_nonneg n) le_rfl
  · exact iSup_le fun h => le_iSup₂_of_le (latticePairing T χ ν).toNat
      (Int.toNat_of_nonneg h).symm le_rfl

/-- The sum of the positive weight spaces of `𝔾_m` acting through `ν ≫ j` is the sum of the
weight spaces for `j` of the characters `χ` with `⟨χ, ν⟩ > 0`. -/
theorem iSup_nat_succ_weightSpace_cocharacter (hT : IsSplitTorus T.toGrp)
    (ν : cocharacterLattice T) (j : T.toGrp ⟶ G) :
    (⨆ n : ℕ, weightSpace (CommGroupScheme.groupHom ν ≫ j) (Gm.powerHom _ (n + 1))) =
      ⨆ (χ : characterLattice T) (_ : 0 < latticePairing T χ ν), weightSpace j χ := by
  simp only [weightSpace_cocharacter_eq_iSup hT j ν]
  rw [iSup_comm]
  refine iSup_congr fun χ => le_antisymm ?_ ?_
  · refine iSup₂_le fun n hn => le_iSup_of_le (by omega) le_rfl
  · exact iSup_le fun h => le_iSup₂_of_le ((latticePairing T χ ν).toNat - 1)
      (by omega) le_rfl

omit [LocallyOfFiniteType G.X.hom] in
/-- A weight vector of `χ` for `j` is a weight vector of `t ↦ t ^ ⟨χ, ν⟩` for `ν ≫ j`. -/
theorem weightSpace_le_weightSpace_cocharacter (ν : cocharacterLattice T) (j : T.toGrp ⟶ G)
    (χ : characterLattice T) :
    weightSpace j χ ≤
      weightSpace (CommGroupScheme.groupHom ν ≫ j) (Gm.powerHom _ (latticePairing T χ ν)) := by
  have h : ν ≫ χ = Gm.powerHom _ (latticePairing T χ ν) := by
    rw [Gm.powerHom_apply, latticePairing_apply, ← eq_gmEndEquiv_zsmul]
  rw [← h]
  exact weightSpace_le_comp ν j χ

/-- Weight spaces of distinct characters of a split torus are disjoint. -/
theorem weightSpace_disjoint (hT : IsSplitTorus T.toGrp) (j : T.toGrp ⟶ G)
    {χ χ' : characterLattice T} (h : χ ≠ χ') :
    Disjoint (weightSpace j χ) (weightSpace j χ') := by
  classical
  exact (isInternal_weightSpace_of_isSplitTorus k G T hT j).submodule_iSupIndep.pairwiseDisjoint h

/-- The weight space of a character outside a set of characters of a split torus is disjoint
from the sum of the weight spaces of that set. -/
theorem weightSpace_disjoint_iSup (hT : IsSplitTorus T.toGrp) (j : T.toGrp ⟶ G)
    {p : characterLattice T → Prop} {χ : characterLattice T} (h : ¬ p χ) :
    Disjoint (weightSpace j χ) (⨆ (χ' : characterLattice T) (_ : p χ'), weightSpace j χ') := by
  classical
  exact (isInternal_weightSpace_of_isSplitTorus k G T hT j).submodule_iSupIndep.disjoint_biSup
    (y := {χ' | p χ'}) h

/-- For a regular cocharacter `ν`, the weight-zero space of `𝔾_m` acting through `ν ≫ j` is the
weight space of the trivial character of `T`. -/
theorem weightSpace_cocharacter_zero_of_isRegular (hT : IsSplitTorus T.toGrp)
    {j : T.toGrp ⟶ G} {ν : cocharacterLattice T} (hν : IsRegularCocharacter j ν) :
    weightSpace (CommGroupScheme.groupHom ν ≫ j) (Gm.powerHom _ 0) = weightSpace j 0 := by
  rw [weightSpace_cocharacter_eq_iSup hT j ν]
  refine le_antisymm (iSup₂_le fun χ hχ => ?_) (le_iSup₂_of_le 0 (by simp) le_rfl)
  by_cases h0 : χ = 0
  · rw [h0]
  by_cases hb : weightSpace j χ = ⊥
  · rw [hb]
    exact bot_le
  exact absurd hχ (hν χ ⟨h0, hb⟩)

omit [LocallyOfFiniteType G.X.hom] in
/-- If every root positive on a regular `ν` is positive on `ν'`, the characters nonnegative on
`ν` span no more than those nonnegative on `ν'`. -/
theorem iSup_nonneg_weightSpace_le_of_isRegular {j : T.toGrp ⟶ G}
    {ν ν' : cocharacterLattice T} (hν : IsRegularCocharacter j ν)
    (h : ∀ α ∈ roots j, 0 < latticePairing T α ν → 0 < latticePairing T α ν') :
    (⨆ (χ : characterLattice T) (_ : 0 ≤ latticePairing T χ ν), weightSpace j χ) ≤
      ⨆ (χ : characterLattice T) (_ : 0 ≤ latticePairing T χ ν'), weightSpace j χ := by
  refine iSup₂_le fun χ hχ => ?_
  by_cases h0 : χ = 0
  · exact le_iSup₂_of_le χ (by simp [h0]) le_rfl
  by_cases hb : weightSpace j χ = ⊥
  · rw [hb]
    exact bot_le
  have hpos : 0 < latticePairing T χ ν := lt_of_le_of_ne hχ (hν χ ⟨h0, hb⟩).symm
  exact le_iSup₂_of_le χ (h χ ⟨h0, hb⟩ hpos).le le_rfl

/-- If the characters nonnegative on `ν` span no more than those nonnegative on a regular `ν'`,
every root positive on `ν` is positive on `ν'`. -/
theorem pos_of_iSup_nonneg_weightSpace_le (hT : IsSplitTorus T.toGrp) {j : T.toGrp ⟶ G}
    {ν ν' : cocharacterLattice T} (hν' : IsRegularCocharacter j ν')
    (hle : (⨆ (χ : characterLattice T) (_ : 0 ≤ latticePairing T χ ν), weightSpace j χ) ≤
      ⨆ (χ : characterLattice T) (_ : 0 ≤ latticePairing T χ ν'), weightSpace j χ)
    {α : characterLattice T} (hα : α ∈ roots j) (h : 0 < latticePairing T α ν) :
    0 < latticePairing T α ν' := by
  by_contra hn
  have hneg : ¬ 0 ≤ latticePairing T α ν' := fun h' =>
    hn (lt_of_le_of_ne h' (hν' α hα).symm)
  have hle' : weightSpace j α ≤
      ⨆ (χ : characterLattice T) (_ : 0 ≤ latticePairing T χ ν'), weightSpace j χ :=
    (le_iSup₂_of_le α h.le le_rfl).trans hle
  exact hα.2 ((weightSpace_disjoint_iSup hT j hneg).eq_bot_of_le hle')

/-- For regular `ν` and `ν'`, the characters nonnegative on `ν` and those nonnegative on `ν'`
span the same subspace exactly when every root has the same sign on `ν` and `ν'`. -/
theorem iSup_nonneg_weightSpace_eq_iff (hT : IsSplitTorus T.toGrp) {j : T.toGrp ⟶ G}
    {ν ν' : cocharacterLattice T} (hν : IsRegularCocharacter j ν)
    (hν' : IsRegularCocharacter j ν') :
    (⨆ (χ : characterLattice T) (_ : 0 ≤ latticePairing T χ ν), weightSpace j χ) =
        (⨆ (χ : characterLattice T) (_ : 0 ≤ latticePairing T χ ν'), weightSpace j χ) ↔
      ∀ α ∈ roots j, (0 < latticePairing T α ν ↔ 0 < latticePairing T α ν') := by
  constructor
  · intro heq α hα
    exact ⟨pos_of_iSup_nonneg_weightSpace_le hT hν' heq.le hα,
      pos_of_iSup_nonneg_weightSpace_le hT hν heq.ge hα⟩
  · intro h
    exact le_antisymm (iSup_nonneg_weightSpace_le_of_isRegular hν fun α hα => (h α hα).mp)
      (iSup_nonneg_weightSpace_le_of_isRegular hν' fun α hα => (h α hα).mpr)

/-- For regular `ν` and `ν'`, the sums of the nonnegative weight spaces of `𝔾_m` acting through
`ν ≫ j` and through `ν' ≫ j` agree exactly when every root has the same sign on `ν` and
`ν'`. -/
theorem iSup_nat_weightSpace_cocharacter_eq_iff (hT : IsSplitTorus T.toGrp)
    {j : T.toGrp ⟶ G} {ν ν' : cocharacterLattice T} (hν : IsRegularCocharacter j ν)
    (hν' : IsRegularCocharacter j ν') :
    (⨆ n : ℕ, weightSpace (CommGroupScheme.groupHom ν ≫ j) (Gm.powerHom _ n)) =
        (⨆ n : ℕ, weightSpace (CommGroupScheme.groupHom ν' ≫ j) (Gm.powerHom _ n)) ↔
      ∀ α ∈ roots j, (0 < latticePairing T α ν ↔ 0 < latticePairing T α ν') := by
  rw [iSup_nat_weightSpace_cocharacter hT ν j, iSup_nat_weightSpace_cocharacter hT ν' j]
  exact iSup_nonneg_weightSpace_eq_iff hT hν hν'

omit [LocallyOfFiniteType G.X.hom] in
/-- The characters positive on `ν` span the same subspace as the roots positive on `ν`. -/
theorem iSup_pos_weightSpace_eq_iSup_roots (j : T.toGrp ⟶ G) (ν : cocharacterLattice T) :
    (⨆ (χ : characterLattice T) (_ : 0 < latticePairing T χ ν), weightSpace j χ) =
      ⨆ (α : characterLattice T) (_ : α ∈ roots j) (_ : 0 < latticePairing T α ν),
        weightSpace j α := by
  refine le_antisymm (iSup₂_le fun χ hχ => ?_)
    (iSup_le fun α => iSup_le fun _ => iSup_le fun h => le_iSup₂_of_le α h le_rfl)
  by_cases hb : weightSpace j χ = ⊥
  · rw [hb]
    exact bot_le
  have h0 : χ ≠ 0 := by
    rintro rfl
    simp at hχ
  exact le_iSup_of_le χ (le_iSup_of_le ⟨h0, hb⟩ (le_iSup_of_le hχ le_rfl))

omit [LocallyOfFiniteType G.X.hom] in
/-- For a regular `ν`, the characters nonnegative on `ν` span the weight space of the trivial
character together with the weight spaces of the characters positive on `ν`. -/
theorem iSup_nonneg_weightSpace_eq_of_isRegular {j : T.toGrp ⟶ G} {ν : cocharacterLattice T}
    (hν : IsRegularCocharacter j ν) :
    (⨆ (χ : characterLattice T) (_ : 0 ≤ latticePairing T χ ν), weightSpace j χ) =
      weightSpace j 0 ⊔ ⨆ (χ : characterLattice T) (_ : 0 < latticePairing T χ ν),
        weightSpace j χ := by
  refine le_antisymm (iSup₂_le fun χ hχ => ?_)
    (sup_le (le_iSup₂_of_le 0 (by simp) le_rfl)
      (iSup₂_le fun χ hχ => le_iSup₂_of_le χ hχ.le le_rfl))
  by_cases h0 : χ = 0
  · rw [h0]
    exact le_sup_left
  by_cases hb : weightSpace j χ = ⊥
  · rw [hb]
    exact bot_le
  exact le_sup_of_le_right
    (le_iSup₂_of_le χ (lt_of_le_of_ne hχ (hν χ ⟨h0, hb⟩).symm) le_rfl)

/-- The sum of the weight spaces of `t ↦ t ^ n`, `n ≥ 0`, for `ν ≫ j` is the nonnegative weight
span of `ν`. -/
theorem iSup_nat_weightSpace_cocharacter_eq_nonnegativeWeightSpan (hT : IsSplitTorus T.toGrp)
    (ν : cocharacterLattice T) (j : T.toGrp ⟶ G) :
    (⨆ n : ℕ, weightSpace (CommGroupScheme.groupHom ν ≫ j) (Gm.powerHom _ n)) =
      nonnegativeWeightSpan j ν :=
  iSup_nat_weightSpace_cocharacter hT ν j

omit [LocallyOfFiniteType G.X.hom] in
/-- For a regular `ν`, the nonnegative weight span is the weight space of the trivial character
together with the weight spaces of the roots positive on `ν`. -/
theorem nonnegativeWeightSpan_eq_of_isRegular {j : T.toGrp ⟶ G} {ν : cocharacterLattice T}
    (hν : IsRegularCocharacter j ν) :
    nonnegativeWeightSpan j ν =
      weightSpace j 0 ⊔ ⨆ (α : characterLattice T) (_ : α ∈ roots j ∧ 0 < latticePairing T α ν),
        weightSpace j α := by
  rw [nonnegativeWeightSpan_def, iSup_nonneg_weightSpace_eq_of_isRegular hν,
    iSup_pos_weightSpace_eq_iSup_roots j ν]
  simp only [iSup_and]

/-- For regular `ν` and `ν'`, the nonnegative weight spans agree exactly when every root has the
same sign on `ν` and `ν'`. -/
theorem nonnegativeWeightSpan_eq_iff (hT : IsSplitTorus T.toGrp) {j : T.toGrp ⟶ G}
    {ν ν' : cocharacterLattice T} (hν : IsRegularCocharacter j ν)
    (hν' : IsRegularCocharacter j ν') :
    nonnegativeWeightSpan j ν = nonnegativeWeightSpan j ν' ↔
      ∀ α ∈ roots j, (0 < latticePairing T α ν ↔ 0 < latticePairing T α ν') :=
  iSup_nonneg_weightSpace_eq_iff hT hν hν'

end Field

end Langlands.GroupScheme
