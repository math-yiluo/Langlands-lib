import Langlands.Global.RankinSelberg.RealLocalWhittakerModel
import Langlands.Global.RankinSelberg.RealPlaceWhittakerCovariance
import Langlands.Global.RankinSelberg.RealPlaceIsotypic
import Langlands.Global.RankinSelberg.UnramifiedWhittakerFactorizationProof

/-!
# Equivariance of archimedean restrictions of global Whittaker functions at a real place

For an actual cuspidal realization `T`, a real place `w`, a finite adelic point `b` and a
`(𝔤, K)`-map `A` at `w`, the functions `g ↦ W_(A f)(ι_w(g) b)` transform under right
translation by `O(r+1)` as the functions `f` of the standard module do.
-/

noncomputable section
universe u
open CategoryTheory AlgebraicGeometry NumberField
open scoped CategoryTheory.MonObj
open Langlands.LocalFactor.Archimedean
set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal

open Langlands.Global Langlands.Automorphic

local instance equivSchemeAffine (F : Type u) [Field F] (n : ℕ) :
    IsAffine (Scheme F n).X.left := GroupScheme.GeneralLinear.isAffine_groupScheme _ _
local instance equivSchemeSmooth (F : Type u) [Field F] (n : ℕ) :
    Smooth (Scheme F n).X.hom := GroupScheme.GeneralLinear.smoothStatement _ _
local instance equivRationalAddCommGroup (F : Type u) [Field F] [NumberField F] (n : ℕ) :
    AddCommGroup (RationalInvariantFunctions F n) := Submodule.addCommGroup _
local instance equivContinuousAddCommGroup (F : Type u) [Field F] [NumberField F] (n : ℕ) :
    AddCommGroup (ContinuousRationalFunctions F n) := Submodule.addCommGroup _
local instance equivSmoothAddCommGroup (F : Type u) [Field F] [NumberField F] (n : ℕ) :
    AddCommGroup (FiniteSmoothRationalFunctions F n) := Submodule.addCommGroup _
local instance equivFormsAddCommGroup (F : Type u) [Field F] [NumberField F] (n : ℕ) :
    AddCommGroup (AutomorphicForms F n) := Submodule.addCommGroup _
local instance equivStableAddCommGroup (F : Type u) [Field F] [NumberField F] (n : ℕ) :
    AddCommGroup (StableAutomorphicFunctions F n) := Submodule.addCommGroup _
local instance equivRealizationAddCommGroup {F : Type u} [Field F] [NumberField F] {n : ℕ}
    (S : OperatorRealization F n) : AddCommGroup S.Space := Submodule.addCommGroup _

section Points

variable (F : Type u) [Field F] [NumberField F] (n : ℕ)

omit [NumberField F] in
open scoped Classical in
/-- The entries at a real place of the single-place embedding. -/
theorem realPlaceGL_entry (w v : {v : InfinitePlace F // v.IsReal})
    (g : Matrix.GeneralLinearGroup (Fin n) ℝ) (i j : Fin n) :
    (((realPlaceGL F n w g : ArchimedeanGL F n) :
        Matrix (Fin n) (Fin n) (mixedEmbedding.mixedSpace F)) i j).1 v =
      (((Pi.mulSingle w g : {v : InfinitePlace F // v.IsReal} →
        Matrix.GeneralLinearGroup (Fin n) ℝ) v : Matrix.GeneralLinearGroup (Fin n) ℝ) :
          Matrix (Fin n) (Fin n) ℝ) i j := rfl

omit [NumberField F] in
/-- At a complex place the single-real-place embedding is identity. -/
theorem realPlaceGL_entry_snd (w : {v : InfinitePlace F // v.IsReal})
    (g : Matrix.GeneralLinearGroup (Fin n) ℝ) (i j : Fin n)
    (v : {v : InfinitePlace F // v.IsComplex}) :
    (((realPlaceGL F n w g : ArchimedeanGL F n) :
        Matrix (Fin n) (Fin n) (mixedEmbedding.mixedSpace F)) i j).2 v =
      (1 : Matrix (Fin n) (Fin n) ℂ) i j := rfl

/-- The adelic entries of the single-place embedding. -/
theorem realPlacePoint_entry (w : {v : InfinitePlace F // v.IsReal})
    (g : Matrix.GeneralLinearGroup (Fin n) ℝ) (i j : Fin n) :
    ((GeneralLinearGroupPoints.adelicEquiv F n (realPlacePoint F n w g) : AdelicGL F n) :
        Matrix (Fin n) (Fin n) (Adeles F)) i j =
      ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm
          (((realPlaceGL F n w g : ArchimedeanGL F n) :
            Matrix (Fin n) (Fin n) (mixedEmbedding.mixedSpace F)) i j),
        (1 : Matrix (Fin n) (Fin n) (FiniteAdeles F)) i j) := by
  rw [realPlacePoint, adelicPoint, MulEquiv.apply_symm_apply]
  rfl

omit [NumberField F] in
open scoped Classical in
/-- The superdiagonal sum is supported at the chosen real place. -/
theorem realPlaceGL_superdiag_sum {r : ℕ} (w : {v : InfinitePlace F // v.IsReal})
    (u : Matrix.GeneralLinearGroup (Fin (r + 1)) ℝ) :
    (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm
        (∑ i : Fin r, ((realPlaceGL F (r + 1) w u : ArchimedeanGL F (r + 1)) :
          Matrix (Fin (r + 1)) (Fin (r + 1)) (mixedEmbedding.mixedSpace F)) i.castSucc i.succ) =
      (Pi.single w.1 ((InfinitePlace.Completion.ringEquivRealOfIsReal w.2).symm
        (∑ i : Fin r, (u : Matrix (Fin (r + 1)) (Fin (r + 1)) ℝ) i.castSucc i.succ)) :
          InfiniteAdeleRing F) := by
  apply (InfiniteAdeleRing.ringEquiv_mixedSpace F).injective
  rw [RingEquiv.apply_symm_apply]
  refine Prod.ext (funext fun v => ?_) (funext fun v => ?_)
  · rw [Prod.fst_sum, Finset.sum_apply]
    change _ = InfinitePlace.Completion.extensionEmbeddingOfIsReal v.2
      ((Pi.single w.1 _ : InfiniteAdeleRing F) v.1)
    rw [Finset.sum_congr rfl fun i _ => realPlaceGL_entry F (r + 1) w v u i.castSucc i.succ]
    by_cases hv : v = w
    · subst hv
      simp only [Pi.mulSingle_eq_same, Pi.single_eq_same]
      rw [← InfinitePlace.Completion.ringEquivRealOfIsReal_apply v.2,
        RingEquiv.apply_symm_apply]
    · have hv' : v.1 ≠ w.1 := fun h => hv (Subtype.ext h)
      simp only [ne_eq, hv, not_false_eq_true, Pi.mulSingle_eq_of_ne]
      rw [Pi.single_eq_of_ne hv', map_zero]
      exact Finset.sum_eq_zero fun i _ =>
        Matrix.one_apply_ne (Fin.castSucc_lt_succ (i := i)).ne
  · have hv : v.1 ≠ w.1 := fun h =>
      (InfinitePlace.not_isReal_iff_isComplex.mpr v.2) (h.symm ▸ w.2)
    rw [Prod.snd_sum, Finset.sum_apply]
    change _ = InfinitePlace.Completion.extensionEmbedding v.1
      ((Pi.single w.1 _ : InfiniteAdeleRing F) v.1)
    rw [Pi.single_eq_of_ne hv, map_zero]
    exact Finset.sum_eq_zero fun i _ =>
      (realPlaceGL_entry_snd F (r + 1) w u _ _ v).trans
        (Matrix.one_apply_ne (Fin.castSucc_lt_succ (i := i)).ne)

/-- A finite sum of adeles given by their infinite and finite components. -/
theorem RealPlaceRestriction.adeles_sum_mk {J : Type*} (s : Finset J) (a : J → InfiniteAdeles F)
    (b : J → FiniteAdeles F) :
    (∑ i ∈ s, (((a i, b i) : Adeles F))) = (((∑ i ∈ s, a i), (∑ i ∈ s, b i)) : Adeles F) := by
  classical
  induction s using Finset.induction_on with
  | empty => rfl
  | insert x s hx ih =>
    rw [Finset.sum_insert hx, Finset.sum_insert hx, Finset.sum_insert hx, ih]
    rfl

open scoped Classical in
/-- The generic character of a character `χ` of `𝔸` with component `ψ_c` at `w`, at `ι_w(u)`,
is `ψ_c(∑ u_(i,i+1))`. -/
theorem genericCharacter_realPlacePoint {r : ℕ} (χ : AddChar (Adeles F) ℂ)
    (w : {v : InfinitePlace F // v.IsReal}) (c : ℝˣ)
    (hχ : ∀ y : InfinitePlace.Completion w.1,
      χ (((Pi.single w.1 y : InfiniteAdeles F), (0 : FiniteAdeles F)) : Adeles F) =
        ((realScaledCharacter c
          (InfinitePlace.Completion.ringEquivRealOfIsReal w.2 y) : Circle) : ℂ))
    {u : Matrix.GeneralLinearGroup (Fin (r + 1)) ℝ}
    (hu : u ∈ GeneralLinear.upperUnipotent (r + 1) ℝ) :
    genericCharacter F r χ (fun _ => 1)
        ⟨realPlacePoint F (r + 1) w u, realPlacePoint_mem_unipotent F (r + 1) w ⟨u, hu⟩⟩ =
      realWhittakerCharacter c u := by
  have hsum : (∑ i : Fin r, algebraMap F (Adeles F) 1 *
      ((GeneralLinearGroupPoints.adelicEquiv F (r + 1) (realPlacePoint F (r + 1) w u) :
        AdelicGL F (r + 1)) : Matrix (Fin (r + 1)) (Fin (r + 1)) (Adeles F)) i.castSucc i.succ) =
      (((Pi.single w.1 ((InfinitePlace.Completion.ringEquivRealOfIsReal w.2).symm
          (∑ i : Fin r, (u : Matrix (Fin (r + 1)) (Fin (r + 1)) ℝ) i.castSucc i.succ)) :
            InfiniteAdeles F), (0 : FiniteAdeles F)) : Adeles F) := by
    have hterm : ∀ i : Fin r, algebraMap F (Adeles F) 1 *
        ((GeneralLinearGroupPoints.adelicEquiv F (r + 1) (realPlacePoint F (r + 1) w u) :
          AdelicGL F (r + 1)) : Matrix (Fin (r + 1)) (Fin (r + 1)) (Adeles F))
            i.castSucc i.succ =
        (((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm
          (((realPlaceGL F (r + 1) w u : ArchimedeanGL F (r + 1)) :
            Matrix (Fin (r + 1)) (Fin (r + 1)) (mixedEmbedding.mixedSpace F))
              i.castSucc i.succ), (0 : FiniteAdeles F)) : Adeles F) := by
      intro i
      have h1 : algebraMap F (Adeles F) 1 = 1 := map_one _
      rw [h1, one_mul, realPlacePoint_entry,
        Matrix.one_apply_ne (Fin.castSucc_lt_succ (i := i)).ne]
    refine (Finset.sum_congr rfl fun i _ => hterm i).trans ((RealPlaceRestriction.adeles_sum_mk F _ _ _).trans ?_)
    have h2 : (∑ i : Fin r, (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm
        (((realPlaceGL F (r + 1) w u : ArchimedeanGL F (r + 1)) :
          Matrix (Fin (r + 1)) (Fin (r + 1)) (mixedEmbedding.mixedSpace F))
            i.castSucc i.succ)) =
        (Pi.single w.1 ((InfinitePlace.Completion.ringEquivRealOfIsReal w.2).symm
          (∑ i : Fin r, (u : Matrix (Fin (r + 1)) (Fin (r + 1)) ℝ) i.castSucc i.succ)) :
            InfiniteAdeleRing F) :=
      (map_sum (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm _ _).symm.trans
        (realPlaceGL_superdiag_sum F w u)
    rw [h2, Finset.sum_const_zero]
  change χ _ = _
  rw [hsum, hχ, RingEquiv.apply_symm_apply]
  rfl

end Points

section Component

variable {F : Type u} [Field F] [NumberField F]

open Langlands.Global.HeckeFunctionalEquation

open scoped Classical in
/-- If the component of `ψ` at `w` is `ψ_a`, the hypothesis of
`genericCharacter_realPlacePoint` holds for `ψ` and `a`. -/
theorem realComponent_complex (ψ : HarmonicAnalysis.UnitaryAdditiveCharacter (Adeles F))
    (w : {v : InfinitePlace F // v.IsReal}) (a : ℝˣ)
    (ha : IsRealAdditiveComponent ψ w.1 w.2 a) (y : InfinitePlace.Completion w.1) :
    ψ.complex (((Pi.single w.1 y : InfiniteAdeles F), (0 : FiniteAdeles F)) : Adeles F) =
      ((realScaledCharacter a
        (InfinitePlace.Completion.ringEquivRealOfIsReal w.2 y) : Circle) : ℂ) :=
  congrArg (fun z : Circle => (z : ℂ)) (ha y)

open scoped Classical in
/-- If the component of `ψ` at `w` is `ψ_a`, the component of `ψ⁻¹` is `ψ_(-a)`. -/
theorem realComponent_complex_inv (ψ : HarmonicAnalysis.UnitaryAdditiveCharacter (Adeles F))
    (w : {v : InfinitePlace F // v.IsReal}) (a : ℝˣ)
    (ha : IsRealAdditiveComponent ψ w.1 w.2 a) (y : InfinitePlace.Completion w.1) :
    ψ.complex⁻¹ (((Pi.single w.1 y : InfiniteAdeles F), (0 : FiniteAdeles F)) : Adeles F) =
      ((realScaledCharacter (-a)
        (InfinitePlace.Completion.ringEquivRealOfIsReal w.2 y) : Circle) : ℂ) := by
  have hneg : -(((Pi.single w.1 y : InfiniteAdeles F), (0 : FiniteAdeles F)) : Adeles F) =
      (((Pi.single w.1 (-y) : InfiniteAdeles F), (0 : FiniteAdeles F)) : Adeles F) := by
    refine Prod.ext ?_ ?_
    · exact (Pi.single_neg w.1 y).symm
    · exact neg_zero
  have hval : realScaledCharacter a
      (InfinitePlace.Completion.ringEquivRealOfIsReal w.2 (-y)) =
      realScaledCharacter (-a)
        (InfinitePlace.Completion.ringEquivRealOfIsReal w.2 y) := by
    rw [map_neg, realScaledCharacter_apply, realScaledCharacter_apply, Units.val_neg,
      mul_neg, neg_mul]
  exact ((AddChar.inv_apply _ _).trans (congrArg ψ.complex hneg)).trans
    ((realComponent_complex ψ w a ha (-y)).trans (congrArg (fun z : Circle => (z : ℂ)) hval))

end Component

section Whittaker

variable {F : Type u} [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]

/-- Compact covariance of the actual coefficient at a real place. -/
theorem cuspWhittaker_realPlaceCompact {r : ℕ} (ψ : AddChar (Adeles F) ℂ)
    (T : CuspidalOperatorRealization F r)
    (w : {v : InfinitePlace F // v.IsReal}) (l : Matrix.unitaryGroup (Fin (r + 1)) ℝ)
    (y : T.Space) (g : Points F (r + 1)) :
    cuspWhittaker F T ψ (T.realization.realPlaceCompactRepresentation w l y) g =
      cuspWhittaker F T ψ y (g * (GeneralLinearGroupPoints.adelicEquiv F (r + 1)).symm
        (AdelicGL.ofInfinite F (r + 1) (realPlaceCompactInclusion F (r + 1) w l).val)) :=
  RealPlaceWhittaker.cuspWhittaker_compact F T ψ (realPlaceCompactInclusion F (r + 1) w l) y g

/-- **`O(r+1)`-equivariance.** For a `(𝔤, K)`-map `A` at `w`, if `f'` is the right translate
of `f` by `k ∈ U(r+1)`, then `g ↦ W_(A f')(ι_w(g) b)` is the right translate by `k` of
`g ↦ W_(A f)(ι_w(g) b)`. -/
theorem realPlaceRestriction_rightTranslation {r : ℕ} (ψ : AddChar (Adeles F) ℂ)
    (T : CuspidalOperatorRealization F r) (w : {v : InfinitePlace F // v.IsReal})
    (b : FiniteAdelicGL F (r + 1)) {d : List RealBlock}
    {A : realStandardKFinite (r + 1) d →ₗ[ℂ] T.Space}
    (hA : T.realization.IsRealPlaceMap w d A)
    (k : Archimedean.unitaryCompact ℝ (r + 1)) (f f' : realStandardKFinite (r + 1) d)
    (hf' : (f' : Langlands.GeneralLinear (r + 1) ℝ → ℂ) =
      Whittaker.rightTranslation ℂ (Langlands.GeneralLinear (r + 1) ℝ)
        (k : Langlands.GeneralLinear (r + 1) ℝ) f) :
    (fun g => cuspWhittaker F T ψ (A f')
        (realPlacePoint F (r + 1) w g * finitePoint F (r + 1) b)) =
      Whittaker.rightTranslation ℂ (Langlands.GeneralLinear (r + 1) ℝ)
        (k : Langlands.GeneralLinear (r + 1) ℝ)
        (fun g => cuspWhittaker F T ψ (A f)
          (realPlacePoint F (r + 1) w g * finitePoint F (r + 1) b)) := by
  refine Exists.elim (hA.1 k f) fun hf he => ?_
  let l : Matrix.unitaryGroup (Fin (r + 1)) ℝ :=
    ⟨((k : Langlands.GeneralLinear (r + 1) ℝ) : Matrix (Fin (r + 1)) (Fin (r + 1)) ℝ), k.2⟩
  have hk : Unitary.toUnits l = (k : Langlands.GeneralLinear (r + 1) ℝ) := Units.ext rfl
  have hAf' : A f' = T.realization.realPlaceCompactRepresentation w l (A f) :=
    (congrArg A (Subtype.ext hf' : f' = ⟨_, hf⟩)).trans he
  funext g
  have hpt : realPlacePoint F (r + 1) w g * finitePoint F (r + 1) b *
      (GeneralLinearGroupPoints.adelicEquiv F (r + 1)).symm
        (AdelicGL.ofInfinite F (r + 1) (realPlaceCompactInclusion F (r + 1) w l).val) =
      realPlacePoint F (r + 1) w (g * (k : Langlands.GeneralLinear (r + 1) ℝ)) *
        finitePoint F (r + 1) b := by
    rw [← realPlacePoint_unitary, hk, realPlacePoint_mul]
    exact (mul_assoc _ _ _).trans
      ((congrArg (realPlacePoint F (r + 1) w g * ·)
        (realPlacePoint_finitePoint_commute F (r + 1) w
          (k : Langlands.GeneralLinear (r + 1) ℝ) b).eq.symm).trans (mul_assoc _ _ _).symm)
  exact (congrArg (fun y => cuspWhittaker F T ψ y
      (realPlacePoint F (r + 1) w g * finitePoint F (r + 1) b)) hAf').trans
    ((cuspWhittaker_realPlaceCompact ψ T w l (A f) _).trans
      (congrArg (cuspWhittaker F T ψ (A f)) hpt))

open scoped Classical in
/-- **`θ`-equivariance.** If `χ` is a standard character of `𝔸` with component `ψ_c` at `w`,
then for `u ∈ N_(r+1)(ℂ)`, `W_x(ι_w(u g) b) = ψ_c(∑ u_(i,i+1)) W_x(ι_w(g) b)`. -/
theorem realPlaceRestriction_mul_left {r : ℕ} (χ : AddChar (Adeles F) ℂ)
    (hχstd : IsStandardAdditiveCharacter F χ) (w : {v : InfinitePlace F // v.IsReal})
    (c : ℝˣ)
    (hχ : ∀ y : InfinitePlace.Completion w.1,
      χ (((Pi.single w.1 y : InfiniteAdeles F), (0 : FiniteAdeles F)) : Adeles F) =
        ((realScaledCharacter c
          (InfinitePlace.Completion.ringEquivRealOfIsReal w.2 y) : Circle) : ℂ))
    (T : CuspidalOperatorRealization F r) (b : FiniteAdelicGL F (r + 1)) (x : T.Space)
    {u : Matrix.GeneralLinearGroup (Fin (r + 1)) ℝ}
    (hu : u ∈ GeneralLinear.upperUnipotent (r + 1) ℝ)
    (g : Matrix.GeneralLinearGroup (Fin (r + 1)) ℝ) :
    cuspWhittaker F T χ x (realPlacePoint F (r + 1) w (u * g) * finitePoint F (r + 1) b) =
      realWhittakerCharacter c u *
        cuspWhittaker F T χ x (realPlacePoint F (r + 1) w g * finitePoint F (r + 1) b) := by
  rw [realPlacePoint_mul, mul_assoc]
  exact (Unfolding.cuspWhittaker_mul_left F T χ hχstd x
    ⟨_, realPlacePoint_mem_unipotent F (r + 1) w ⟨u, hu⟩⟩ _).trans
      (congrArg (· * _) (genericCharacter_realPlacePoint F χ w c hχ hu))

end Whittaker

end Langlands.Global.RankinSelbergGlobal
