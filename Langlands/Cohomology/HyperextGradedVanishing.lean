import Langlands.Cohomology.HyperextAbutmentFiltration
import Langlands.Cohomology.HyperextSecondPage

/-!
# Vanishing of graded pieces of the hyperext abutment filtration

Let `t` be a t-structure on a pretriangulated category `C`, let `K` and `B` be objects of `C`, and
let `F^p` be the abutment filtration on `Hom(K, B⟦n⟧)` of
`Langlands.Cohomology.HyperextAbutmentFiltration`: `F^p` consists of the morphisms factoring
through `K ⟶ τ_{≥ p - n} K`. The term in position `(p, n - p)` on page 2 of the hyperext spectral
sequence is `Hom(heartPiece t K (n - p), B⟦p + (n - p)⟧)`
(`HyperextSpectralSequence.secondPageIso`). This module proves that the graded piece
`gr^p = F^p / F^{p+1}` vanishes when every morphism `heartPiece t K (n - p) ⟶ B⟦n⟧` is zero
(`filtration_le_succ`, `subsingleton_graded_of_heartPiece`). It does so directly with
distinguished triangles, without comparing `gr^p` with the pages of the spectral sequence. If
moreover `K` lies in degrees `≤ b` and the condition holds for every `p' ≥ p`, then `F^p` is zero
(`filtration_eq_bot_of_forall`).

For the canonical t-structure on the derived category of an abelian category and `B` an object
`W` placed in degree `0`, these morphism groups are `Ext^p(H^{p - n} K, W)` for `p : ℕ`
(`HyperextSpectralSequence.secondPageExtAddEquiv`). Hence `gr^p` vanishes when this `Ext` group
does (`subsingleton_derivedGraded_of_ext`). Under the hypotheses of
`HyperextDegenerationStatement` (`K` has cohomology bounded above and `Ext^i(H^k K, W)` vanishes
for every `k` and every `i > 0`), `F^p` is zero for every `p > 0`
(`derivedFiltration_eq_bot_of_ext`). Since `F^1` is the kernel of the edge map, the edge map is
injective (`edgeMap_injective_of_ext`) and identifies `Hom(K, W⟦n⟧)` with its image
(`edgeMapAddEquivRangeOfExt`). So `HyperextDegenerationStatement` follows from the
surjectivity of the edge map under the same hypotheses
(`hyperextDegenerationStatement_of_surjective`). This module does not prove that surjectivity.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
  CategoryTheory.Triangulated

namespace Langlands.Cohomology

namespace HyperextAbutment

open HyperextSpectralSequence

universe w' w v u

section TStructure

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C] {t : TStructure C}

/-- If every morphism `heartPiece t K (n - p) ⟶ B⟦n⟧` is zero, then `F^p ≤ F^{p+1}`. A morphism
`f` in `F^p` vanishes on the first object of `upperTriangle t K (n - p)`, which lies in degrees
`< p - n`, so it factors through `toUpperPiece`. The factorization vanishes on `heartPiece`, so
it factors through the third object of `heartTriangle t K (n - p)`, which lies in degrees
`≥ p + 1 - n`. Hence `f` vanishes on `τ_{< p + 1 - n} K`. -/
lemma filtration_le_succ {K B : C} {n p : ℤ}
    (hE : ∀ g : heartPiece t K (n - p) ⟶ B⟦n⟧, g = 0) :
    filtration t K B n p ≤ filtration t K B n (p + 1) := by
  intro f hf
  obtain ⟨g', rfl⟩ := (mem_filtration_iff f).1 hf
  have : t.IsLE (upperTriangle t K (n - p)).obj₁ (p - n - 1) :=
    t.isLE_of_le _ (-(n - p + 1)) (p - n - 1) (by lia)
  have hz₁ : (upperTriangle t K (n - p)).mor₁ ≫ (t.truncGEπ (p - n)).app K = 0 :=
    t.zero _ (p - n - 1) (p - n) (by lia)
  have h₁ : (upperTriangle t K (n - p)).mor₁ ≫ (t.truncGEπ (p - n)).app K ≫ g' = 0 :=
    (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ g') hz₁).trans zero_comp)
  obtain ⟨g, hg⟩ := Triangle.yoneda_exact₂ _ (upperTriangle_distinguished t K (n - p)) _ h₁
  obtain ⟨h, hh⟩ := Triangle.yoneda_exact₂ _ (heartTriangle_distinguished t K (n - p)) g (hE _)
  refine (mem_filtration_iff_truncLTι_comp_eq_zero _).2 ?_
  have : t.IsGE (heartTriangle t K (n - p)).obj₃ (p + 1 - n) :=
    t.isGE_of_ge _ (p + 1 - n) (-(n - p - 1)) (by lia)
  have hz : (t.truncLTι (p + 1 - n)).app K ≫ (upperTriangle t K (n - p)).mor₂ ≫
      (heartTriangle t K (n - p)).mor₂ = 0 :=
    t.zero _ (p + 1 - n - 1) (p + 1 - n) (by lia)
  have e : (t.truncGEπ (p - n)).app K ≫ g' =
      (upperTriangle t K (n - p)).mor₂ ≫ (heartTriangle t K (n - p)).mor₂ ≫ h :=
    hg.trans (congrArg ((upperTriangle t K (n - p)).mor₂ ≫ ·) hh)
  refine (congrArg ((t.truncLTι (p + 1 - n)).app K ≫ ·) e).trans ?_
  exact (congrArg _ (Category.assoc _ _ _).symm).trans
    ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ h) hz).trans zero_comp))

/-- If every morphism `heartPiece t K (n - p) ⟶ B⟦n⟧` is zero, then `F^{p+1} = F^p`. -/
lemma filtration_succ_eq {K B : C} {n p : ℤ}
    (hE : ∀ g : heartPiece t K (n - p) ⟶ B⟦n⟧, g = 0) :
    filtration t K B n (p + 1) = filtration t K B n p :=
  le_antisymm (filtration_le_of_le (by lia)) (filtration_le_succ hE)

/-- The graded piece `gr^p` vanishes when every morphism `heartPiece t K (n - p) ⟶ B⟦n⟧` is
zero. -/
lemma subsingleton_graded_of_heartPiece {K B : C} {n p : ℤ}
    (hE : ∀ g : heartPiece t K (n - p) ⟶ B⟦n⟧, g = 0) :
    Subsingleton (graded t K B n p) :=
  subsingleton_graded_of_le (filtration_le_succ hE)

/-- If `K` lies in degrees `≤ b` and every morphism `heartPiece t K (n - p') ⟶ B⟦n⟧` is zero
for every `p' ≥ p`, then `F^p` is zero. -/
lemma filtration_eq_bot_of_forall {K B : C} {n : ℤ} (b : ℤ) [t.IsLE K b] (p : ℤ)
    (hE : ∀ p' : ℤ, p ≤ p' → ∀ g : heartPiece t K (n - p') ⟶ B⟦n⟧, g = 0) :
    filtration t K B n p = ⊥ := by
  have key : ∀ k : ℕ, filtration t K B n (p + k) = filtration t K B n p := by
    intro k
    induction k with
    | zero => rw [Nat.cast_zero, add_zero]
    | succ k ih =>
      rw [Nat.cast_succ, ← add_assoc, filtration_succ_eq (hE _ (by lia)), ih]
  rw [← key (b - p + n + 1).toNat]
  exact filtration_eq_bot b (by lia)

end TStructure

section Derived

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]

open DerivedCategory

/-- For `p : ℕ`, every morphism `heartPiece TStructure.t K (n - p) ⟶ W⟦n⟧` is zero as soon as
`Ext^p(H^{p - n} K, W)` is zero, where `W` is placed in degree `0`. This uses the additive
equivalence `HyperextSpectralSequence.secondPageExtAddEquiv`. -/
lemma heartPiece_hom_eq_zero_of_ext [HasExt.{w'} C] (K : DerivedCategory C) (W : C) (n : ℤ)
    (p : ℕ) (h : Subsingleton (Abelian.Ext.{w'} ((homologyFunctor C ((p : ℤ) - n)).obj K) W p))
    (g : heartPiece TStructure.t K (n - p) ⟶ ((singleFunctor C 0).obj W)⟦n⟧) : g = 0 := by
  have h₁ : Subsingleton (Abelian.Ext.{w'} ((homologyFunctor C (-(n - (p : ℤ)))).obj K) W p) := by
    rw [show -(n - (p : ℤ)) = (p : ℤ) - n by lia]
    exact h
  have h₂ := (secondPageExtAddEquiv.{w'} K W p (n - p)).injective.subsingleton
  have h₃ : Subsingleton (heartPiece TStructure.t K (n - p) ⟶ ((singleFunctor C 0).obj W)⟦n⟧) := by
    rw [show (p : ℤ) + (n - p) = n by lia] at h₂
    exact h₂
  exact Subsingleton.elim _ _

/-- For `p : ℕ`, the graded piece `gr^p` of the abutment filtration on `Hom(K, W⟦n⟧)` vanishes
when `Ext^p(H^{p - n} K, W)` is zero. -/
lemma subsingleton_derivedGraded_of_ext [HasExt.{w'} C] (K : DerivedCategory C) (W : C)
    (n : ℤ) (p : ℕ)
    (h : Subsingleton (Abelian.Ext.{w'} ((homologyFunctor C ((p : ℤ) - n)).obj K) W p)) :
    Subsingleton (graded TStructure.t K ((singleFunctor C 0).obj W) n p) :=
  subsingleton_graded_of_heartPiece (heartPiece_hom_eq_zero_of_ext K W n p h)

/-- If the cohomology of `K` vanishes in degrees `> b` and `Ext^i(H^k K, W)` is zero for every
`k` and every `i > 0`, then `F^p` is zero for every `p > 0`. -/
lemma derivedFiltration_eq_bot_of_ext [HasExt.{w'} C] (K : DerivedCategory C) (b : ℤ)
    (hK : ∀ i : ℤ, b < i → IsZero ((homologyFunctor C i).obj K)) (W : C) (n p : ℤ) (hp : 0 < p)
    (hW : ∀ (k : ℤ) (i : ℕ), 0 < i →
      Subsingleton (Abelian.Ext.{w'} ((homologyFunctor C k).obj K) W i)) :
    derivedFiltration K W n p = ⊥ := by
  have : K.IsLE b := (K.isLE_iff b).2 hK
  refine filtration_eq_bot_of_forall b p fun p' hp' g => ?_
  obtain ⟨m, rfl⟩ : ∃ m : ℕ, (m : ℤ) = p' := ⟨p'.toNat, Int.toNat_of_nonneg (by lia)⟩
  exact heartPiece_hom_eq_zero_of_ext K W n m (hW _ m (by lia)) g

/-- Under the hypotheses of `HyperextDegenerationStatement`, the edge map
`Hom(K, W⟦n⟧) → Hom(H^{-n} K, W)` is injective, because its kernel `F^1` is zero. -/
lemma edgeMap_injective_of_ext [HasExt.{w'} C] (K : DerivedCategory C) (b : ℤ)
    (hK : ∀ i : ℤ, b < i → IsZero ((homologyFunctor C i).obj K)) (W : C)
    (hW : ∀ (k : ℤ) (i : ℕ), 0 < i →
      Subsingleton (Abelian.Ext.{w'} ((homologyFunctor C k).obj K) W i)) (n : ℤ) :
    Function.Injective (HyperextDegeneration.edgeMap K W n) := by
  refine (injective_iff_map_eq_zero (edgeMapAddMonoidHom K W n)).2 fun f hf => ?_
  have hf' : f ∈ derivedFiltration K W n 1 := (mem_derivedFiltration_one_iff K W n f).2 hf
  rw [derivedFiltration_eq_bot_of_ext K b hK W n 1 (by lia) hW] at hf'
  exact (AddSubgroup.mem_bot).1 hf'

/-- Under the hypotheses of `HyperextDegenerationStatement`, the edge map identifies
`Hom(K, W⟦n⟧)` with its image in `Hom(H^{-n} K, W)`. -/
def edgeMapAddEquivRangeOfExt [HasExt.{w'} C] (K : DerivedCategory C) (b : ℤ)
    (hK : ∀ i : ℤ, b < i → IsZero ((homologyFunctor C i).obj K)) (W : C)
    (hW : ∀ (k : ℤ) (i : ℕ), 0 < i →
      Subsingleton (Abelian.Ext.{w'} ((homologyFunctor C k).obj K) W i)) (n : ℤ) :
    ShiftedHom K ((singleFunctor C 0).obj W) n ≃+ (edgeMapAddMonoidHom K W n).range :=
  AddMonoidHom.ofInjective (f := edgeMapAddMonoidHom K W n)
    (edgeMap_injective_of_ext K b hK W hW n)

@[simp]
lemma edgeMapAddEquivRangeOfExt_apply_coe [HasExt.{w'} C] (K : DerivedCategory C) (b : ℤ)
    (hK : ∀ i : ℤ, b < i → IsZero ((homologyFunctor C i).obj K)) (W : C)
    (hW : ∀ (k : ℤ) (i : ℕ), 0 < i →
      Subsingleton (Abelian.Ext.{w'} ((homologyFunctor C k).obj K) W i)) (n : ℤ)
    (f : ShiftedHom K ((singleFunctor C 0).obj W) n) :
    (edgeMapAddEquivRangeOfExt K b hK W hW n f : (homologyFunctor C (-n)).obj K ⟶ W) =
      HyperextDegeneration.edgeMap K W n f :=
  rfl

/-- `HyperextDegenerationStatement` holds as soon as the edge map is surjective under its
hypotheses: injectivity is `edgeMap_injective_of_ext`. -/
lemma hyperextDegenerationStatement_of_surjective [HasExt.{w'} C]
    (h : ∀ (K : DerivedCategory C) (b : ℤ),
      (∀ i : ℤ, b < i → IsZero ((homologyFunctor C i).obj K)) → ∀ W : C,
      (∀ (k : ℤ) (i : ℕ), 0 < i →
        Subsingleton (Abelian.Ext.{w'} ((homologyFunctor C k).obj K) W i)) →
      ∀ n : ℤ, Function.Surjective (HyperextDegeneration.edgeMap K W n)) :
    HyperextDegenerationStatement.{w, w'} C :=
  fun K b hK W hW n => ⟨edgeMap_injective_of_ext K b hK W hW n, h K b hK W hW n⟩

end Derived

end HyperextAbutment

end Langlands.Cohomology
