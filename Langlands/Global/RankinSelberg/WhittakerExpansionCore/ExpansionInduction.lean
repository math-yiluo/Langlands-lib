import Langlands.Global.RankinSelberg.WhittakerExpansionCore.ExpansionGSide

/-! # The Whittaker expansion from summable Whittaker terms

Let `f` be continuous and left `GL_(r+1)(F)`-invariant, with the properties `LevelPropsB r` of
the torus column framework at the top level. Write `P_j` for the projection coefficients
(`projectionCoefficient`) and `G_j` for the partial Whittaker sums (`whittakerSum`).

* Downward from `P_r = f`, each `P_j` is the column coefficient of `P_(j+1)` at `ψ₀(b y_j)`,
  and satisfies `LevelPropsB j`.
* Upward from `P_0 = W_f = G_0`, the uniqueness lemma `eq_zero_of_colCoeffB_eq_zero` applied to
  `P_(j+1) − G_(j+1)` gives `P_(j+1) = G_(j+1)`, provided the Whittaker terms at level `j + 1`
  are absolutely summable.

At `j = r` this is the Whittaker expansion `f = Σ_q W_f(diag(q, 1) x)`. -/

noncomputable section
universe u
open CategoryTheory AlgebraicGeometry NumberField MeasureTheory
open scoped CategoryTheory.MonObj ComplexConjugate
set_option autoImplicit false

namespace Langlands.Automorphic.CuspidalWhittaker

open Langlands.Global

variable {K : Type u} [Field K] [NumberField K] {Idx : Type*} [Fintype Idx]

omit [Fintype Idx] in
theorem IsPeriodic.sub {f g : (Idx → Adeles K) → ℂ} (hf : IsPeriodic f) (hg : IsPeriodic g) :
    IsPeriodic (fun y => f y - g y) := fun y k => by
  beta_reduce
  rw [hf y k, hg y k]

/-- Fourier coefficients of a difference of continuous periodic functions. -/
theorem fourierCoeff_sub [CompactSpace (AdeleQuotient K)] {f g : (Idx → Adeles K) → ℂ}
    (hf : IsPeriodic f) (hfc : Continuous f) (hg : IsPeriodic g) (hgc : Continuous g)
    (a : Idx → K) :
    fourierCoeff (fun y => f y - g y) a = fourierCoeff f a - fourierCoeff g a := by
  unfold fourierCoeff
  simp only [sub_mul]
  exact torusIntegral_sub (hf.mul (isPeriodic_conj_pairingCharacter a))
    (hfc.mul (continuous_conj_pairingCharacter a)) (hg.mul (isPeriodic_conj_pairingCharacter a))
    (hgc.mul (continuous_conj_pairingCharacter a))

end Langlands.Automorphic.CuspidalWhittaker

namespace Langlands.Global.RankinSelbergGlobal.Unfolding

open Langlands.Global Langlands.GroupScheme Langlands.GroupScheme.GeneralLinear
  AdelicSubgroupPoints Langlands.Automorphic.CuspidalWhittaker

local instance inductionSchemeAffine (F : Type u) [Field F] (n : ℕ) :
    IsAffine (Scheme F n).X.left := GroupScheme.GeneralLinear.isAffine_groupScheme _ _
local instance inductionSchemeSmooth (F : Type u) [Field F] (n : ℕ) :
    Smooth (Scheme F n).X.hom := GroupScheme.GeneralLinear.smoothStatement _ _

variable (F : Type u) [Field F] [NumberField F]

section Base

theorem projectionWeight_zero (n : ℕ) : projectionWeight n 0 = upperUnipotentWeight n := by
  funext i
  simp only [projectionWeight, upperUnipotentWeight, Nat.sub_zero]

/-- Character coefficients along block unipotent subgroups only depend on the weights. -/
theorem subgroupCharacterCoefficient_blockUnipotent_congr {n : ℕ} {w w' : Fin n → ℤ}
    (h : w = w')
    [IsClosed (adelicPoints F (Scheme F n)
      (GroupScheme.GeneralLinear.blockUnipotent (Fin n) (CommRingCat.of F) w) :
        Set (Points F n))]
    [IsClosed (adelicPoints F (Scheme F n)
      (GroupScheme.GeneralLinear.blockUnipotent (Fin n) (CommRingCat.of F) w') :
        Set (Points F n))]
    (Φ : Points F n → ℂ) (f : Points F n → ℂ) (x : Points F n) :
    subgroupCharacterCoefficient F (Scheme F n)
        (GroupScheme.GeneralLinear.blockUnipotent (Fin n) (CommRingCat.of F) w)
        (fun y => Φ y.val) f x =
      subgroupCharacterCoefficient F (Scheme F n)
        (GroupScheme.GeneralLinear.blockUnipotent (Fin n) (CommRingCat.of F) w')
        (fun y => Φ y.val) f x := by
  subst h
  rfl

/-- `P_0 = W_f`: the coefficient along `Y_(r+1,0) = N_(r+1)` with the projection character is
the Whittaker function with all coefficients `1`. -/
theorem projectionCoefficient_zero {r : ℕ} (ψ : AddChar (Adeles F) ℂ)
    (f : Points F (r + 1) → ℂ) (x : Points F (r + 1)) :
    projectionCoefficient F r 0 ψ f x = whittaker F r ψ f x := by
  set Φ : Points F (r + 1) → ℂ := fun p =>
    ψ (∑ i : Fin r, (GeneralLinearGroupPoints.adelicEquiv F (r + 1) p) i.castSucc i.succ)
    with hΦ
  have hgen : genericCharacter F r ψ (fun _ => 1) = fun y => Φ y.val := by
    funext y
    simp only [genericCharacter, hΦ, map_one, one_mul]
  change subgroupCharacterCoefficient F (Scheme F (r + 1)) (projectionUnipotent F (r + 1) 0)
      (fun y => Φ y.val) f x =
    subgroupCharacterCoefficient F (Scheme F (r + 1)) (upperUnipotent F (r + 1))
      (genericCharacter F r ψ (fun _ => 1)) f x
  rw [hgen]
  exact subgroupCharacterCoefficient_blockUnipotent_congr F (projectionWeight_zero (r + 1)) Φ f x

end Base

variable [CompactSpace (AdeleQuotient F)]

section PSide

variable {r : ℕ} (ψ : AddChar (Adeles F) ℂ) (f : Points F (r + 1) → ℂ)

/-- The projection coefficient `P_j` as a function on the matrix group. -/
def projTilde (j : ℕ) (g : AdelicGL F (r + 1)) : ℂ :=
  projectionCoefficient F r j ψ f ((GeneralLinearGroupPoints.adelicHomeomorph F (r + 1)).symm g)

omit [CompactSpace (AdeleQuotient F)] in
theorem projTilde_top (g : AdelicGL F (r + 1)) :
    projTilde F ψ f r g = f ((GeneralLinearGroupPoints.adelicHomeomorph F (r + 1)).symm g) :=
  projectionCoefficient_top F ψ f _

omit [CompactSpace (AdeleQuotient F)] in
/-- The projection character on a column point is the column character `ψ₀(b y_j)`. -/
theorem character_colVec_colPoint {b : F}
    (hb : ∀ x, ψ x = EqualAnalytic.standardCharacter F (algebraMap F (Adeles F) b * x))
    {j : ℕ} (hj : j < r) (y : Fin (r + 1) → Adeles F) :
    ψ (colVec F hj (colPoint F (j := j) y) (Fin.castSucc ⟨j, hj⟩)) =
      pairingCharacter (Pi.single (charIdx j hj) b) y := by
  have e : truncVec (j + 1) y (Fin.castSucc ⟨j, hj⟩) = y (charIdx j hj) := by
    simp only [truncVec]
    rw [ite_eq_left (by simp)]
    rfl
  rw [colVec_colPoint F hj, e, hb, pairingCharacter_single, EqualAnalytic.standardCharacter_apply]

variable (hψ : IsStandardAdditiveCharacter F ψ) (hf : Continuous f)
  (hfΓ : ∀ k ∈ AdelicGroupPoints.rationalSubgroup F (Scheme F (r + 1)), ∀ x, f (k * x) = f x)
  {b : F} (hb : ∀ x, ψ x = EqualAnalytic.standardCharacter F (algebraMap F (Adeles F) b * x))

include hψ hf hfΓ hb

/-- **Column step for the projection coefficients.** If `P̃_(j+1)` satisfies
`LevelPropsB (j + 1)`, its column coefficient at `ψ₀(b y_j)` is `P̃_j`. -/
theorem colCoeffB_projTilde {j : ℕ} (hj : j < r)
    (hP : LevelPropsB (j + 1) (projTilde F ψ f (j + 1))) (g : AdelicGL F (r + 1)) :
    colCoeffB hj b (projTilde F ψ f (j + 1)) g = projTilde F ψ f j g := by
  set x := (GeneralLinearGroupPoints.adelicHomeomorph F (r + 1)).symm g with hx
  have hcol : ∀ y, projTilde F ψ f (j + 1) (colUnit (colIdx j hj) y * g) =
      projectionCoefficient F r (j + 1) ψ f (colPoint F (j := j) y * x) := fun y => by
    unfold projTilde
    rw [symm_colUnit_mul F hj]
  have hfun : (fun y => conj (ψ (colVec F hj (colPoint F (j := j) y) (Fin.castSucc ⟨j, hj⟩))) *
      projectionCoefficient F r (j + 1) ψ f (colPoint F (j := j) y * x)) =
      fun y => conj (pairingCharacter (Pi.single (charIdx j hj) b) y) *
        projTilde F ψ f (j + 1) (colUnit (colIdx j hj) y * g) := by
    funext y
    rw [character_colVec_colPoint F ψ hb hj, hcol y]
  have hc : Continuous (fun y => conj (ψ (colVec F hj (colPoint F (j := j) y)
      (Fin.castSucc ⟨j, hj⟩))) *
      projectionCoefficient F r (j + 1) ψ f (colPoint F (j := j) y * x)) := by
    rw [hfun]
    exact (continuous_conj_pairingCharacter _).mul (continuous_col_apply hj hP.continuous g)
  have hper : IsPeriodic (fun y => conj (ψ (colVec F hj (colPoint F (j := j) y)
      (Fin.castSucc ⟨j, hj⟩))) *
      projectionCoefficient F r (j + 1) ψ f (colPoint F (j := j) y * x)) := by
    rw [hfun]
    exact (isPeriodic_conj_pairingCharacter _).mul (isPeriodic_col hj hP.invariant g)
  have hR : projTilde F ψ f j g = projectionCoefficient F r j ψ f x := rfl
  rw [hR, projectionCoefficient_eq_column F hj ψ hψ f hf hfΓ x]
  refine Eq.symm ((normalized_setIntegral_column_eq_torusIntegral F hj
    (fun m => conj (ψ (colVec F hj m (Fin.castSucc ⟨j, hj⟩))) *
      projectionCoefficient F r (j + 1) ψ f (m * x)) hc hper).trans ?_)
  rw [hfun]
  unfold colCoeffB Langlands.Automorphic.CuspidalWhittaker.fourierCoeff
  refine torusIntegral_congr fun y => ?_
  rw [mul_comm]

/-- **Downward induction.** Every `P̃_c` satisfies `LevelPropsB c`. -/
theorem levelPropsB_projTilde
    (htop : LevelPropsB r
      (fun g => f ((GeneralLinearGroupPoints.adelicHomeomorph F (r + 1)).symm g))) :
    ∀ (d c : ℕ), c + d = r → LevelPropsB c (projTilde F ψ f c) := by
  intro d
  induction d with
  | zero =>
    intro c hc
    rw [Nat.add_zero] at hc
    subst hc
    have e : projTilde F ψ f c =
        fun g => f ((GeneralLinearGroupPoints.adelicHomeomorph F (c + 1)).symm g) :=
      funext (projTilde_top F ψ f)
    rw [e]
    exact htop
  | succ d ih =>
    intro c hc
    have hcr : c < r := by omega
    have hP := ih (c + 1) (by omega)
    have e : colCoeffB hcr b (projTilde F ψ f (c + 1)) = projTilde F ψ f c :=
      funext (colCoeffB_projTilde F ψ f hψ hf hfΓ hb hcr hP)
    rw [← e]
    exact hP.step hcr b

end PSide

section Expansion

variable {r : ℕ} (ψ : AddChar (Adeles F) ℂ) (f : Points F (r + 1) → ℂ)
  (hψ : IsStandardAdditiveCharacter F ψ) (hf : Continuous f)
  (hfΓ : ∀ k ∈ AdelicGroupPoints.rationalSubgroup F (Scheme F (r + 1)), ∀ x, f (k * x) = f x)
  (htop : LevelPropsB r
    (fun g => f ((GeneralLinearGroupPoints.adelicHomeomorph F (r + 1)).symm g)))
  (hsum : ∀ (k : ℕ) (hk : k ≤ r) (x : Points F (r + 1)),
    Summable fun q : UnipotentRationalCosets F k =>
      ‖whittaker F r ψ f (padRational F (Nat.le_succ_of_le hk) q.out * x)‖)

include hψ hf hfΓ htop hsum

/-- **Upward induction.** `P̃_j = G̃_j` for every `j ≤ r`. -/
theorem projTilde_eq_whittakerSumGL {b : F} (hb0 : b ≠ 0)
    (hb : ∀ x, ψ x = EqualAnalytic.standardCharacter F (algebraMap F (Adeles F) b * x)) :
    ∀ (j : ℕ) (hj : j ≤ r) (g : AdelicGL F (r + 1)),
      projTilde F ψ f j g = whittakerSumGL F ψ f j (Nat.le_succ_of_le hj) g := by
  intro j
  induction j with
  | zero =>
    intro _ g
    unfold projTilde whittakerSumGL
    rw [projectionCoefficient_zero, whittakerSum_zero]
  | succ j ih =>
    intro hj g
    have hjr : j < r := by omega
    have hP := levelPropsB_projTilde F ψ f hψ hf hfΓ hb htop (r - (j + 1)) (j + 1) (by omega)
    have hsum' : ∀ x : Points F (r + 1), Summable fun q : UnipotentRationalCosets F (j + 1) =>
        ‖whittaker F r ψ f (padRational F (by omega : j + 1 ≤ r + 1) q.out * x)‖ :=
      hsum (j + 1) hj
    have hGc := continuous_whittakerSumGL_col F ψ f hψ hfΓ hb hjr hsum'
    have hGp := isPeriodic_whittakerSumGL_col F ψ f hψ hfΓ hb hjr
    have hPc := continuous_col_apply hjr hP.continuous
    have hPp := isPeriodic_col hjr hP.invariant
    have key := eq_zero_of_colCoeffB_eq_zero hjr hb0
      (F := fun g => projTilde F ψ f (j + 1) g - whittakerSumGL F ψ f (j + 1) (by omega) g)
      (fun g => (hPc g).sub (hGc g)) (fun g => Langlands.Automorphic.CuspidalWhittaker.IsPeriodic.sub (hPp g) (hGp g))
      (fun β hβ g => by
        rw [hP.invariant β hβ.isMir g, whittakerSumGL_rational_mul F ψ f hψ hfΓ _ β hβ g])
      (fun g => by
        rw [fourierCoeff_sub (hPp g) (hPc g) (hGp g) (hGc g),
          fourierCoeff_zero_of_blockVanishing hjr hP.continuous hP.invariant hP.vanishing g,
          fourierCoeff_zero_whittakerSumGL_col F ψ f hψ hfΓ hb hjr hsum' hb0 g, sub_zero])
      (fun g => by
        rw [colCoeffB_sub hjr b hPc hPp hGc hGp g,
          colCoeffB_projTilde F ψ f hψ hf hfΓ hb hjr hP g,
          colCoeffB_whittakerSumGL F ψ f hψ hfΓ hb hjr hsum' hb0 g, ih (by omega) g, sub_self])
      g
    exact sub_eq_zero.mp key

/-- **The Whittaker expansion from summable Whittaker terms.** -/
theorem hasSum_whittaker_of_levelPropsB (x : Points F (r + 1)) :
    HasSum (fun q : UnipotentRationalCosets F r =>
      whittaker F r ψ f (cornerAdelicPoint F r q.out * x)) (f x) := by
  obtain ⟨b, hb0, hb⟩ := EqualAnalytic.exists_eq_standardCharacter_mul F ψ hψ
  have h := projTilde_eq_whittakerSumGL F ψ f hψ hf hfΓ htop hsum hb0 hb r le_rfl
    (GeneralLinearGroupPoints.adelicHomeomorph F (r + 1) x)
  rw [projTilde_top] at h
  unfold whittakerSumGL whittakerSum at h
  have e1 : (GeneralLinearGroupPoints.adelicHomeomorph F (r + 1)).symm
      (GeneralLinearGroupPoints.adelicHomeomorph F (r + 1) x) = x :=
    (GeneralLinearGroupPoints.adelicHomeomorph F (r + 1)).symm_apply_apply x
  rw [e1] at h
  rw [h]
  have hs := (hsum r le_rfl x).of_norm
  have e : (fun q : UnipotentRationalCosets F r =>
      whittaker F r ψ f (cornerAdelicPoint F r q.out * x)) =
      fun q => whittaker F r ψ f (padRational F (Nat.le_succ_of_le le_rfl) q.out * x) := by
    funext q
    rw [← padRational_eq_cornerAdelicPoint]
  rw [e]
  exact hs.hasSum

end Expansion

end Langlands.Global.RankinSelbergGlobal.Unfolding
