import Langlands.Cohomology.HyperextConvergence.HalfBoundedStatement
import Langlands.Cohomology.HyperextConvergence.Proof

/-!
# Convergence of the hyperext spectral sequence in Cartan–Eilenberg's Case 1: proof

This module proves `HyperextHalfBoundedConvergenceStatements` of
`Langlands.Cohomology.HyperextConvergence.HalfBoundedStatement`
(`hyperextHalfBoundedConvergenceStatements_proof`). Let `X` be the hyperext spectral object of
`K` and `B`, with `K` in degrees `≤ b` and `B` in degrees `≥ c`.

* `H^n(i ⟶ j)` vanishes when `n - c < i`, because the truncation of `op K` in degrees `[i, j)`
  lies in degrees `≤ -i` for `t` (`isZero_H_of_isGE`). Hence every page vanishes in the columns
  `p < c` (`isZero_page_X_of_lt_left`).
* A differential of page `r` leaving `(p, q)` ends in the row `q + 1 - r < -b`, and one entering
  `(p, q)` starts in the column `p - r < c`; both pages vanish there
  (`hyperextHalfBoundedDifferential`).
* The object in position `(p, q)` of page `r` is `E^{p+q}(q - r + 2 ≤ q ≤ q + 1 ≤ q + r - 1)`;
  the lower index becomes `⊥` because `H^{p+q+1}(⊥ ⟶ q - r + 2)` vanishes, the upper index
  becomes `⊤` because `H^{p+q-1}(q + r - 1 ⟶ ⊤)` vanishes, and `eAddEquiv` identifies
  `E^{p+q}(⊥ ≤ q ≤ q + 1 ≤ ⊤)` with `gr^p` (`halfBoundedStablePageIso`).
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
  CategoryTheory.Pretriangulated.Opposite CategoryTheory.Triangulated Opposite
  ComposableArrows

namespace Langlands.Cohomology

namespace HyperextConvergence

universe v u

open HyperextSpectralSequence HyperextAbutment Abelian.SpectralObject

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C] [IsTriangulated C]

/-- If `B` lies in degrees `≥ c`, then `H^n(i ⟶ j)` vanishes when `n - c < m` and `m ≤ i`: the
truncation of `op K` in degrees `[i, j)`, read in `C`, lies in degrees `≤ -m`, and `B⟦n⟧` lies
in degrees `≥ c - n > -m`. -/
lemma isZero_H_of_isGE (t : TStructure C) (K B : C) (c : ℤ) [t.IsGE B c] (n m : ℤ)
    (D : ComposableArrows EInt 1) (hD : (m : EInt) ≤ D.obj 0) (hm : n - c < m) :
    IsZero (((hyperextSpectralObject t K B).H n).obj D) := by
  have h₁ : (opTStructure t).IsGE (((opTStructure t).ω₁.obj D).obj (op K)) m :=
    (opTStructure t).isGE_eTruncGE_obj_obj m (D.obj 0) hD
      (((opTStructure t).eTruncLT.obj (D.obj 1)).obj (op K))
  have h₂ : t.IsLE (((opTStructure t).ω₁.obj D).obj (op K)).unop (-m) :=
    (opTStructure_isGE_iff t _ m).1 h₁
  have h₃ : t.IsGE (B⟦n⟧) (c - n) := t.isGE_shift B c n (c - n)
  refine @AddCommGrpCat.isZero_of_subsingleton _ ⟨fun x y => ?_⟩
  exact (t.zero (X := (((opTStructure t).ω₁.obj D).obj (op K)).unop) (Y := B⟦n⟧) x
    (-m) (c - n)).trans (t.zero (X := (((opTStructure t).ω₁.obj D).obj (op K)).unop)
      (Y := B⟦n⟧) y (-m) (c - n)).symm

/-- If `B` lies in degrees `≥ c`, then every page vanishes in the columns `p < c`. -/
lemma isZero_page_X_of_lt_left (t : TStructure C) (K B : C) (c : ℤ) [t.IsGE B c] (r : ℤ)
    (hr : 2 ≤ r) (p q : ℤ) (hp : p < c) :
    IsZero (((hyperextSpectralSequence t K B).page r hr).X ⟨p, q⟩) :=
  (hyperextSpectralObject t K B).isZero_spectralSequence_page_X_of_isZero_H'
    coreE₂Cohomological r hr ⟨p, q⟩
    (isZero_H_of_isGE t K B c (p + q) q _ le_rfl (by lia))

/-- Vanishing of the differentials at stable positions: the differential of page `r` leaving
`(p, q)` ends in the row `q + 1 - r < -b`, and the one entering `(p, q)` starts in the column
`p - r < c`. -/
theorem hyperextHalfBoundedDifferential :
    HyperextHalfBoundedDifferentialStatement.{v, u} C := by
  intro t K B b c _ _ r hr p q hp hq pq
  constructor
  · by_cases h : (ComplexShape.up' (⟨r, 1 - r⟩ : ℤ × ℤ)).Rel ⟨p, q⟩ pq
    · obtain ⟨p', q'⟩ := pq
      have h' : q + (1 - r) = q' := congrArg Prod.snd h
      exact (isZero_page_X_of_lt t K B b r hr p' q' (by lia)).eq_of_tgt _ _
    · exact HomologicalComplex.shape _ _ _ h
  · by_cases h : (ComplexShape.up' (⟨r, 1 - r⟩ : ℤ × ℤ)).Rel pq ⟨p, q⟩
    · obtain ⟨p', q'⟩ := pq
      have h' : p' + r = p := congrArg Prod.fst h
      exact (isZero_page_X_of_lt_left t K B c r hr p' q' (by lia)).eq_of_src _ _
    · exact HomologicalComplex.shape _ _ _ h

/-- The object in position `(p, q)` on a page `r` with `r ≥ 2`, `r ≥ p - c + 1` and
`r ≥ q + b + 2` is the graded piece `gr^p` of the abutment filtration in total degree
`p + q`. -/
def halfBoundedStablePageIso (t : TStructure C) (K B : C) (b c : ℤ) [t.IsLE K b] [t.IsGE B c]
    (r : ℤ) (hr : 2 ≤ r) (p q : ℤ) (hp : p - c + 1 ≤ r) (hq : q + b + 2 ≤ r) :
    ((hyperextSpectralSequence t K B).page r hr).X ⟨p, q⟩ ≅
      AddCommGrpCat.of (graded t K B (p + q) p) :=
  (hyperextSpectralObject t K B).spectralSequencePageXIso coreE₂Cohomological r hr ⟨p, q⟩
      ((q - r + 2 : ℤ) : EInt) (q : EInt) ((q + 1 : ℤ) : EInt) ((q + r - 1 : ℤ) : EInt)
      rfl rfl rfl rfl (p + q - 1) (p + q) (p + q + 1) rfl ≪≫
    ((hyperextSpectralObject t K B).isoMapFourδ₁Toδ₀' ⊥ ((q - r + 2 : ℤ) : EInt) (q : EInt)
      ((q + 1 : ℤ) : EInt) ((q + r - 1 : ℤ) : EInt) bot_le
      (WithBotTop.coe_le_coe.2 (by lia)) (WithBotTop.coe_le_coe.2 (by lia))
      (WithBotTop.coe_le_coe.2 (by lia)) (p + q - 1) (p + q) (p + q + 1)
      (isZero_H_bot t K B b _ _ (WithBotTop.coe_le_coe.2 (by lia)))).symm ≪≫
    (hyperextSpectralObject t K B).isoMapFourδ₄Toδ₃' ⊥ (q : EInt) ((q + 1 : ℤ) : EInt)
      ((q + r - 1 : ℤ) : EInt) ⊤ bot_le (WithBotTop.coe_le_coe.2 (by lia))
      (WithBotTop.coe_le_coe.2 (by lia)) le_top (p + q - 1) (p + q) (p + q + 1)
      (isZero_H_of_isGE t K B c (p + q - 1) (q + r - 1) _ le_rfl (by lia)) ≪≫
    AddEquiv.toAddCommGrpIso (Y := AddCommGrpCat.of (graded t K B (p + q) p))
      (eAddEquiv (hyperextSpectralObject t K B) (homOfLE (bot_le : (⊥ : EInt) ≤ (q : EInt)))
        (homOfLE (WithBotTop.coe_le_coe.2 (by lia) : (q : EInt) ≤ ((q + 1 : ℤ) : EInt)))
        (homOfLE (le_top : ((q + 1 : ℤ) : EInt) ≤ ⊤)) (homOfLE bot_le) rfl (homOfLE bot_le) rfl
        (p + q - 1) (p + q) (p + q + 1) (by lia) (by lia)
        (filtration t K B (p + q) p) (filtration t K B (p + q) (p + 1))
        (fun y => (mem_filtration_iff_exists t K B (p + q) p (q + 1) (by lia) y).trans
          (exists_congr fun x =>
            ⟨fun h => (H_map_twoδ₂Toδ₁_apply t K B (p + q) (q + 1) _ _ _ _ x).trans h,
              fun h => (H_map_twoδ₂Toδ₁_apply t K B (p + q) (q + 1) _ _ _ _ x).symm.trans h⟩))
        (fun y => (mem_filtration_iff_exists t K B (p + q) (p + 1) q (by lia) y).trans
          (exists_congr fun x =>
            ⟨fun h => (H_map_twoδ₂Toδ₁_apply t K B (p + q) q _ _ _ _ x).trans h,
              fun h => (H_map_twoδ₂Toδ₁_apply t K B (p + q) q _ _ _ _ x).symm.trans h⟩)))

/-- Identification of the stable positions with the graded pieces of the abutment. -/
theorem hyperextHalfBoundedStablePage : HyperextHalfBoundedStablePageStatement.{v, u} C := by
  intro t K B b c _ _ r hr p q hp hq
  exact ⟨halfBoundedStablePageIso t K B b c r hr p q hp hq⟩

/-- Convergence of the hyperext spectral sequence for `K` bounded above and `B` bounded below. -/
theorem hyperextHalfBoundedConvergenceStatements_proof :
    HyperextHalfBoundedConvergenceStatements.{v, u} C :=
  ⟨hyperextHalfBoundedDifferential, hyperextHalfBoundedStablePage⟩

end HyperextConvergence

end Langlands.Cohomology
