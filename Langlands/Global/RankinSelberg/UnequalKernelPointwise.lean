import Langlands.Global.RankinSelberg.UnequalWhittakerProducts
import Langlands.Global.RankinSelberg.ArchimedeanDeterminantProducts
import Langlands.Global.RankinSelberg.RealPlaceWhittakerEquivariance

/-! # Pointwise assembly of the ordinary and dual unequal-rank kernels -/

noncomputable section
open NumberField Langlands.Automorphic
open Langlands.Global.HeckeFunctionalEquation Langlands.LocalFactor.Archimedean
open Langlands.Global.CompletionPadic Langlands.Global.FiniteAdelicGL
open Langlands.ClassField.Global.RelativeWeilGroup
open scoped Classical CategoryTheory.MonObj
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000

universe u

namespace Langlands.Global.RankinSelbergGlobal.UnequalKernelPointwise

open UnequalLocalKernels UnequalWhittakerProducts ArchimedeanWhittakerProducts UnipotentClass

local instance (F : Type u) [Field F] (n : ℕ) : AlgebraicGeometry.IsAffine (Scheme F n).X.left :=
  GroupScheme.GeneralLinear.isAffine_groupScheme _ _
local instance (F : Type u) [Field F] (n : ℕ) : AlgebraicGeometry.Smooth (Scheme F n).X.hom :=
  GroupScheme.GeneralLinear.smoothStatement _ _

variable {F : Type u} [Field F] [NumberField F]

-- The point and character calculations below are ported from
-- `ComplexPlaceWhittakerEquivariance` without importing its complex operator machinery.
section ComplexPoints

variable (F : Type u) [Field F] [NumberField F] (n : ℕ)

omit [NumberField F] in
open scoped Classical in
/-- The entries at a complex place `v` of `ι_w(g)`. -/
private theorem complexPlaceGL_entry (w v : {v : InfinitePlace F // v.IsComplex})
    (g : Matrix.GeneralLinearGroup (Fin n) ℂ) (i j : Fin n) :
    (((complexPlaceGL F n w g : ArchimedeanGL F n) :
        Matrix (Fin n) (Fin n) (mixedEmbedding.mixedSpace F)) i j).2 v =
      (((Pi.mulSingle w g : {v : InfinitePlace F // v.IsComplex} →
        Matrix.GeneralLinearGroup (Fin n) ℂ) v : Matrix.GeneralLinearGroup (Fin n) ℂ) :
          Matrix (Fin n) (Fin n) ℂ) i j := rfl
/-- `ι_w(g)` is the image of an infinite adelic element. -/
private theorem complexPlacePoint_eq_ofInfinite (w : {v : InfinitePlace F // v.IsComplex})
    (g : Matrix.GeneralLinearGroup (Fin n) ℂ) :
    complexPlacePoint F n w g = (GeneralLinearGroupPoints.adelicEquiv F n).symm
      (AdelicGL.ofInfinite F n ((archimedeanGLCoordinates F n).symm (complexPlaceGL F n w g))) :=
  rfl

/-- `g ↦ ι_w(g)` is multiplicative. -/
private theorem complexPlacePoint_mul (w : {v : InfinitePlace F // v.IsComplex})
    (g h : Matrix.GeneralLinearGroup (Fin n) ℂ) :
    complexPlacePoint F n w (g * h) = complexPlacePoint F n w g * complexPlacePoint F n w h := by
  rw [complexPlacePoint_eq_ofInfinite, complexPlacePoint_eq_ofInfinite,
    complexPlacePoint_eq_ofInfinite, map_mul, map_mul, map_mul, map_mul]

/-- The adelic entries of `ι_w(g)`. -/
private theorem complexPlacePoint_entry (w : {v : InfinitePlace F // v.IsComplex})
    (g : Matrix.GeneralLinearGroup (Fin n) ℂ) (i j : Fin n) :
    ((GeneralLinearGroupPoints.adelicEquiv F n (complexPlacePoint F n w g) : AdelicGL F n) :
        Matrix (Fin n) (Fin n) (Adeles F)) i j =
      ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm
          (((complexPlaceGL F n w g : ArchimedeanGL F n) :
            Matrix (Fin n) (Fin n) (mixedEmbedding.mixedSpace F)) i j),
        (1 : Matrix (Fin n) (Fin n) (FiniteAdeles F)) i j) := by
  rw [complexPlacePoint_eq_ofInfinite, MulEquiv.apply_symm_apply]
  rfl

omit [NumberField F] in
/-- The entries at the real places of `ι_w(g)` are those of the identity. -/
private theorem complexPlaceGL_entry_fst (w : {v : InfinitePlace F // v.IsComplex})
    (g : Matrix.GeneralLinearGroup (Fin n) ℂ) (i j : Fin n)
    (v : {v : InfinitePlace F // v.IsReal}) :
    (((complexPlaceGL F n w g : ArchimedeanGL F n) :
        Matrix (Fin n) (Fin n) (mixedEmbedding.mixedSpace F)) i j).1 v =
      (1 : Matrix (Fin n) (Fin n) ℝ) i j := rfl

omit [NumberField F] in
private theorem complexPlaceGL_entry_eq_zero (w : {v : InfinitePlace F // v.IsComplex})
    (g : Matrix.GeneralLinearGroup (Fin n) ℂ) {i j : Fin n} (hij : i ≠ j)
    (hg : (g : Matrix (Fin n) (Fin n) ℂ) i j = 0) :
    ((complexPlaceGL F n w g : ArchimedeanGL F n) :
        Matrix (Fin n) (Fin n) (mixedEmbedding.mixedSpace F)) i j = 0 := by
  refine Prod.ext (funext fun v => ?_) (funext fun v => ?_)
  · exact (complexPlaceGL_entry_fst F n w g i j v).trans (Matrix.one_apply_ne hij)
  · rw [complexPlaceGL_entry]
    by_cases hv : v = w
    · subst hv
      simp only [Pi.mulSingle_eq_same]
      exact hg
    · simp only [ne_eq, hv, not_false_eq_true, Pi.mulSingle_eq_of_ne]
      exact Matrix.one_apply_ne hij

omit [NumberField F] in
private theorem complexPlaceGL_entry_eq_one (w : {v : InfinitePlace F // v.IsComplex})
    (g : Matrix.GeneralLinearGroup (Fin n) ℂ) (i : Fin n)
    (hg : (g : Matrix (Fin n) (Fin n) ℂ) i i = 1) :
    ((complexPlaceGL F n w g : ArchimedeanGL F n) :
        Matrix (Fin n) (Fin n) (mixedEmbedding.mixedSpace F)) i i = 1 := by
  refine Prod.ext (funext fun v => ?_) (funext fun v => ?_)
  · exact (complexPlaceGL_entry_fst F n w g i i v).trans (Matrix.one_apply_eq i)
  · rw [complexPlaceGL_entry]
    by_cases hv : v = w
    · subst hv
      simp only [Pi.mulSingle_eq_same]
      exact hg
    · simp only [ne_eq, hv, not_false_eq_true, Pi.mulSingle_eq_of_ne]
      exact Matrix.one_apply_eq i

/-- `ι_w(u)` is upper unitriangular for `u ∈ N_n(ℂ)`. -/
private theorem complexPlacePoint_mem_unipotentAdelic (w : {v : InfinitePlace F // v.IsComplex})
    {u : Matrix.GeneralLinearGroup (Fin n) ℂ} (hu : u ∈ GeneralLinear.upperUnipotent n ℂ) :
    complexPlacePoint F n w u ∈ unipotentAdelic F n := by
  rw [Unfolding.mem_unipotentAdelic_iff]
  refine ⟨fun i j hji => ?_, fun i => ?_⟩
  · have hij : i ≠ j := ne_of_gt hji
    rw [complexPlacePoint_entry, complexPlaceGL_entry_eq_zero F n w u hij (hu.1 hji),
      map_zero, Matrix.one_apply_ne hij]
    rfl
  · rw [complexPlacePoint_entry, complexPlaceGL_entry_eq_one F n w u i (hu.2 i), map_one,
      Matrix.one_apply_eq]
    rfl

omit [NumberField F] in
open scoped Classical in
/-- The superdiagonal sum of the infinite adelic matrix of `ι_w(u)` is supported at `w`. -/
private theorem complexPlaceGL_superdiag_sum {r : ℕ} (w : {v : InfinitePlace F // v.IsComplex})
    (u : Matrix.GeneralLinearGroup (Fin (r + 1)) ℂ) :
    (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm
        (∑ i : Fin r, ((complexPlaceGL F (r + 1) w u : ArchimedeanGL F (r + 1)) :
          Matrix (Fin (r + 1)) (Fin (r + 1)) (mixedEmbedding.mixedSpace F)) i.castSucc i.succ) =
      (Pi.single w.1 ((InfinitePlace.Completion.ringEquivComplexOfIsComplex w.2).symm
        (∑ i : Fin r, (u : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ) i.castSucc i.succ)) :
          InfiniteAdeleRing F) := by
  apply (InfiniteAdeleRing.ringEquiv_mixedSpace F).injective
  rw [RingEquiv.apply_symm_apply]
  refine Prod.ext (funext fun v => ?_) (funext fun v => ?_)
  · have hv : v.1 ≠ w.1 := fun h =>
      (InfinitePlace.not_isReal_iff_isComplex.mpr w.2) (h ▸ v.2)
    rw [Prod.fst_sum, Finset.sum_apply]
    change _ = InfinitePlace.Completion.extensionEmbeddingOfIsReal v.2
      ((Pi.single w.1 _ : InfiniteAdeleRing F) v.1)
    rw [Pi.single_eq_of_ne hv, map_zero]
    exact Finset.sum_eq_zero fun i _ =>
      (complexPlaceGL_entry_fst F (r + 1) w u _ _ v).trans
        (Matrix.one_apply_ne (Fin.castSucc_lt_succ (i := i)).ne)
  · rw [Prod.snd_sum, Finset.sum_apply]
    change _ = InfinitePlace.Completion.extensionEmbedding v.1
      ((Pi.single w.1 _ : InfiniteAdeleRing F) v.1)
    rw [Finset.sum_congr rfl fun i _ => complexPlaceGL_entry F (r + 1) w v u i.castSucc i.succ]
    by_cases hv : v = w
    · subst hv
      simp only [Pi.mulSingle_eq_same, Pi.single_eq_same]
      rw [← InfinitePlace.Completion.ringEquivComplexOfIsComplex_apply v.2,
        RingEquiv.apply_symm_apply]
    · have hv' : v.1 ≠ w.1 := fun h => hv (Subtype.ext h)
      simp only [ne_eq, hv, not_false_eq_true, Pi.mulSingle_eq_of_ne]
      rw [Pi.single_eq_of_ne hv', map_zero]
      exact Finset.sum_eq_zero fun i _ =>
        Matrix.one_apply_ne (Fin.castSucc_lt_succ (i := i)).ne
open scoped Classical in
/-- The generic character of a character `χ` of `𝔸` with component `ψ_c` at `w`, at `ι_w(u)`,
is `ψ_c(∑ u_(i,i+1))`. -/
private theorem genericCharacter_complexPlacePoint {r : ℕ} (χ : AddChar (Adeles F) ℂ)
    (w : {v : InfinitePlace F // v.IsComplex}) (c : ℂˣ)
    (hχ : ∀ y : InfinitePlace.Completion w.1,
      χ (((Pi.single w.1 y : InfiniteAdeles F), (0 : FiniteAdeles F)) : Adeles F) =
        ((complexScaledCharacter c
          (InfinitePlace.Completion.ringEquivComplexOfIsComplex w.2 y) : Circle) : ℂ))
    {u : Matrix.GeneralLinearGroup (Fin (r + 1)) ℂ}
    (hu : u ∈ GeneralLinear.upperUnipotent (r + 1) ℂ) :
    genericCharacter F r χ (fun _ => 1)
        ⟨complexPlacePoint F (r + 1) w u, complexPlacePoint_mem_unipotentAdelic F (r + 1) w hu⟩ =
      (complexScaledCharacter c).complex (∑ i : Fin r, u.val i.castSucc i.succ) := by
  have hsum : (∑ i : Fin r, algebraMap F (Adeles F) 1 *
      ((GeneralLinearGroupPoints.adelicEquiv F (r + 1) (complexPlacePoint F (r + 1) w u) :
        AdelicGL F (r + 1)) : Matrix (Fin (r + 1)) (Fin (r + 1)) (Adeles F)) i.castSucc i.succ) =
      (((Pi.single w.1 ((InfinitePlace.Completion.ringEquivComplexOfIsComplex w.2).symm
          (∑ i : Fin r, (u : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ) i.castSucc i.succ)) :
            InfiniteAdeles F), (0 : FiniteAdeles F)) : Adeles F) := by
    have hterm : ∀ i : Fin r, algebraMap F (Adeles F) 1 *
        ((GeneralLinearGroupPoints.adelicEquiv F (r + 1) (complexPlacePoint F (r + 1) w u) :
          AdelicGL F (r + 1)) : Matrix (Fin (r + 1)) (Fin (r + 1)) (Adeles F))
            i.castSucc i.succ =
        (((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm
          (((complexPlaceGL F (r + 1) w u : ArchimedeanGL F (r + 1)) :
            Matrix (Fin (r + 1)) (Fin (r + 1)) (mixedEmbedding.mixedSpace F))
              i.castSucc i.succ), (0 : FiniteAdeles F)) : Adeles F) := by
      intro i
      have h1 : algebraMap F (Adeles F) 1 = 1 := map_one _
      rw [h1, one_mul, complexPlacePoint_entry,
        Matrix.one_apply_ne (Fin.castSucc_lt_succ (i := i)).ne]
    refine (Finset.sum_congr rfl fun i _ => hterm i).trans ((RealPlaceRestriction.adeles_sum_mk F _ _ _).trans ?_)
    have h2 : (∑ i : Fin r, (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm
        (((complexPlaceGL F (r + 1) w u : ArchimedeanGL F (r + 1)) :
          Matrix (Fin (r + 1)) (Fin (r + 1)) (mixedEmbedding.mixedSpace F))
            i.castSucc i.succ)) =
        (Pi.single w.1 ((InfinitePlace.Completion.ringEquivComplexOfIsComplex w.2).symm
          (∑ i : Fin r, (u : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ) i.castSucc i.succ)) :
            InfiniteAdeleRing F) :=
      (map_sum (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm _ _).symm.trans
        (complexPlaceGL_superdiag_sum F w u)
    rw [h2, Finset.sum_const_zero]
  change χ _ = _
  rw [hsum, hχ, RingEquiv.apply_symm_apply]
  rfl

end ComplexPoints

section Equivariance

variable [CompactSpace (AdeleQuotient F)] {n : ℕ}
variable (T : CuspidalOperatorRealization F n)
variable (ψ : HarmonicAnalysis.UnitaryAdditiveCharacter (Adeles F))
variable (hψ : IsStandardAdditiveCharacter F ψ.complex)

include hψ

/-- The standard character of an actual real-place restriction. -/
theorem real_equivariant (v : {v : InfinitePlace F // v.IsReal}) (a : ℝˣ)
    (ha : IsRealAdditiveComponent ψ v.1 v.2 a)
    {W : Langlands.GeneralLinear (n + 1) ℝ → ℂ}
    (hW : IsRealPlaceWhittaker F T ψ.complex v W) :
    IsLeftEquivariant n (realScaledCharacter a).complex W := by
  obtain ⟨x, d, rfl⟩ := hW
  intro u g
  exact realPlaceRestriction_mul_left ψ.complex hψ v a
    (fun y => congrArg (fun z : Circle => (z : ℂ)) (ha y)) T d x u.property g

/-- The reciprocal character of an actual real-place restriction for `ψ⁻¹`. -/
theorem real_inverse_equivariant (v : {v : InfinitePlace F // v.IsReal}) (a : ℝˣ)
    (ha : IsRealAdditiveComponent ψ v.1 v.2 a)
    {W : Langlands.GeneralLinear (n + 1) ℝ → ℂ}
    (hW : IsRealPlaceWhittaker F T ψ.complex⁻¹ v W) :
    IsLeftInverseEquivariant n (realScaledCharacter a).complex W := by
  obtain ⟨x, d, rfl⟩ := hW
  intro u g
  let U : unipotentAdelic F (n + 1) := ⟨realPlacePoint F (n + 1) v u.val,
    realPlacePoint_mem_unipotent F (n + 1) v u⟩
  have hU : genericCharacter F n ψ.complex (fun _ => 1) U = realWhittakerCharacter a u.val :=
    genericCharacter_realPlacePoint F ψ.complex v a
      (fun y => congrArg (fun z : Circle => (z : ℂ)) (ha y)) u.property
  have hh := Unfolding.cuspWhittaker_mul_left F T ψ.complex⁻¹
    (Unfolding.isStandardAdditiveCharacter_inv F ψ.complex hψ) x U
    (realPlacePoint F (n + 1) v g * finitePoint F (n + 1) d)
  rw [UnramifiedWhittaker.genericCharacter_inv, hU] at hh
  simp only [realPlacePoint_mul, mul_assoc]
  exact hh

/-- The standard character of an actual complex-place restriction. -/
theorem complex_equivariant (v : {v : InfinitePlace F // v.IsComplex}) (a : ℂˣ)
    (ha : IsComplexAdditiveComponent ψ v.1 v.2 a)
    {W : Langlands.GeneralLinear (n + 1) ℂ → ℂ}
    (hW : IsComplexPlaceWhittaker F T ψ.complex v W) :
    IsLeftEquivariant n (complexScaledCharacter a).complex W := by
  obtain ⟨x, d, rfl⟩ := hW
  intro u g
  let U : unipotentAdelic F (n + 1) := ⟨complexPlacePoint F (n + 1) v u.val,
    complexPlacePoint_mem_unipotentAdelic F (n + 1) v u.property⟩
  have hU : genericCharacter F n ψ.complex (fun _ => 1) U =
      (complexScaledCharacter a).complex (∑ i : Fin n, u.val i.castSucc i.succ) :=
    genericCharacter_complexPlacePoint F ψ.complex v a
      (fun y => congrArg (fun z : Circle => (z : ℂ)) (ha y)) u.property
  have hh := Unfolding.cuspWhittaker_mul_left F T ψ.complex hψ x U
    (complexPlacePoint F (n + 1) v g * finitePoint F (n + 1) d)
  rw [hU] at hh
  simp only [complexPlacePoint_mul, mul_assoc]
  exact hh

/-- The reciprocal character of an actual complex-place restriction for `ψ⁻¹`. -/
theorem complex_inverse_equivariant (v : {v : InfinitePlace F // v.IsComplex}) (a : ℂˣ)
    (ha : IsComplexAdditiveComponent ψ v.1 v.2 a)
    {W : Langlands.GeneralLinear (n + 1) ℂ → ℂ}
    (hW : IsComplexPlaceWhittaker F T ψ.complex⁻¹ v W) :
    IsLeftInverseEquivariant n (complexScaledCharacter a).complex W := by
  obtain ⟨x, d, rfl⟩ := hW
  intro u g
  let U : unipotentAdelic F (n + 1) := ⟨complexPlacePoint F (n + 1) v u.val,
    complexPlacePoint_mem_unipotentAdelic F (n + 1) v u.property⟩
  have hU : genericCharacter F n ψ.complex (fun _ => 1) U =
      (complexScaledCharacter a).complex (∑ i : Fin n, u.val i.castSucc i.succ) :=
    genericCharacter_complexPlacePoint F ψ.complex v a
      (fun y => congrArg (fun z : Circle => (z : ℂ)) (ha y)) u.property
  have hh := Unfolding.cuspWhittaker_mul_left F T ψ.complex⁻¹
    (Unfolding.isStandardAdditiveCharacter_inv F ψ.complex hψ) x U
    (complexPlacePoint F (n + 1) v g * finitePoint F (n + 1) d)
  rw [UnramifiedWhittaker.genericCharacter_inv, hU] at hh
  simp only [complexPlacePoint_mul, mul_assoc]
  exact hh

end Equivariance

/-- The retained local functions at one rank, including all infinite places. -/
structure LocalFactors (S : Finset (FinitePlace F)) (n : ℕ) where
  real : {v : InfinitePlace F // v.IsReal} → Langlands.GeneralLinear n ℝ → ℂ
  complex : {v : InfinitePlace F // v.IsComplex} → Langlands.GeneralLinear n ℂ → ℂ
  finite : ∀ v : S, FiniteLocalGL F n v.1 → ℂ

variable {S : Finset (FinitePlace F)} {n : ℕ}

/-- A single Whittaker product on points integral at all omitted finite places. -/
def WhittakerProduct (c : ℂ) (W : Points F n → ℂ) (L : LocalFactors S n) : Prop :=
  ∀ g : Points F n, (∀ v ∉ S, finiteComponent F n v g ∈ localIntegral F n v) →
    W g = c * ((∏ v, L.real v (realComponent F n v g)) *
      (∏ w, L.complex w (complexComponent F n w g)) *
      ∏ v : S, L.finite v (finiteComponent F n v.1 g))

/-- Applying the dual transform preserves the scalar and dualizes each factor separately. -/
theorem WhittakerProduct.dual {c : ℂ} {W : Points F n → ℂ} {L : LocalFactors S n}
    (hW : WhittakerProduct c W L) :
    WhittakerProduct c (dualFunction F n W)
      ⟨fun v => ArchimedeanLocal.dualFunction n (L.real v),
       fun w => ArchimedeanLocal.dualFunction n (L.complex w),
       fun v => ArchimedeanLocal.dualFunction n (L.finite v)⟩ := by
  intro g hg
  have hh := hW (Unfolding.dualPoint F n g) (fun v hv => dualPoint_integral n v g (hg v hv))
  simpa only [Unfolding.dualFunction_eq, realComponent_dualPoint, complexComponent_dualPoint,
    FiniteWhittakerDual.finiteComponent_dualPoint, ArchimedeanLocal.dualFunction] using hh

section Assembly

open Langlands.RankinSelberg (normalizedAbsoluteValue)
open ArchimedeanLocal (realNormalizedAbs complexNormalizedAbs)

variable [CompactSpace (AdeleQuotient F)] {r t : ℕ} (h : t < r)
variable {T : CuspidalOperatorRealization F r} {T' : CuspidalOperatorRealization F t}
variable (ψ : HarmonicAnalysis.UnitaryAdditiveCharacter (Adeles F))
variable (hψ : IsStandardAdditiveCharacter F ψ.complex)
variable (x : T.Space) (x' : T'.Space)
variable {c c' : ℂ} (L : LocalFactors S (r + 1)) (M : LocalFactors S (t + 1))
variable (hW : WhittakerProduct c (cuspWhittaker F T ψ.complex x) L)
variable (hW' : WhittakerProduct c' (cuspWhittaker F T' ψ.complex⁻¹ x') M)
variable (χR : {v : InfinitePlace F // v.IsReal} → AddChar ℝ ℂ)
variable (χC : {w : InfinitePlace F // w.IsComplex} → AddChar ℂ ℂ)
variable (χS : ∀ v : S, AddChar (FiniteCompletion F v.1) ℂ)
variable (hR : ∀ v, IsLeftEquivariant r (χR v) (L.real v))
variable (hR' : ∀ v, IsLeftInverseEquivariant t (χR v) (M.real v))
variable (hC : ∀ w, IsLeftEquivariant r (χC w) (L.complex w))
variable (hC' : ∀ w, IsLeftInverseEquivariant t (χC w) (M.complex w))
variable (hS : ∀ v, IsLeftEquivariant r (χS v) (L.finite v))
variable (hS' : ∀ v, IsLeftInverseEquivariant t (χS v) (M.finite v))

include hψ hW hW' hR hR' hC hC' hS hS' in
/-- The ordinary pointwise factorization with prescribed local factors. -/
theorem ordinary_product (s : ℂ) (q : WhittakerQuotient F (t + 1))
    (hq : q ∈ unipotentIntegralClasses F (t + 1) S) :
    unequalWhittakerIntegrand F h (cuspWhittaker F T ψ.complex x)
        (cuspWhittaker F T' ψ.complex⁻¹ x') s q =
      (c * c') * ((∏ v, ArchimedeanLocal.realUnequalIntegrand h (L.real v) (M.real v) s
          (realQuotientProjection F t v q)) *
        (∏ w, ArchimedeanLocal.complexUnequalIntegrand h (L.complex w) (M.complex w) s
          (complexQuotientProjection F t w q)) *
        ∏ v : S, ArchimedeanLocal.unequalIntegrand
          (normalizedAbsoluteValue (padicField v.1).canonicalTopologicalData) h
          (L.finite v) (M.finite v) s (finiteQuotientProjection F t v.1 q)) := by
  obtain ⟨g, hg, hK⟩ := exists_integral_rep F S q hq
  rw [ordinaryKernel_of_rep F h T T' ψ.complex hψ x x' s q g hg]
  have hp := hW (pad F (Nat.le_of_lt (Nat.succ_lt_succ h)) g)
    (fun v hv => pad_integral h v g (hK v hv))
  simp only [Unfolding.ordinaryKernel]
  rw [hp, hW' g hK, DeterminantProducts.detPower_product F (t + 1) S g
    (mem_partial_of_integral F S g hK)]
  have eR (v : {v : InfinitePlace F // v.IsReal}) :=
    unequalIntegrand_mk realNormalizedAbs h (χR v) (hR v) (hR' v) s
      (realComponent F (t + 1) v g)
  have eC (w : {w : InfinitePlace F // w.IsComplex}) :=
    unequalIntegrand_mk complexNormalizedAbs h (χC w) (hC w) (hC' w) s
      (complexComponent F (t + 1) w g)
  have eS (v : S) :=
    unequalIntegrand_mk (normalizedAbsoluteValue (padicField v.1).canonicalTopologicalData)
      h (χS v) (hS v) (hS' v) s (finiteComponent F (t + 1) v.1 g)
  have qR (v : {v : InfinitePlace F // v.IsReal}) :
      realQuotientProjection F t v q = Quotient.mk'' (realComponent F (t + 1) v g) :=
    hg ▸ realQuotientProjection_mk F t v g
  have qC (w : {w : InfinitePlace F // w.IsComplex}) :
      complexQuotientProjection F t w q = Quotient.mk'' (complexComponent F (t + 1) w g) :=
    hg ▸ complexQuotientProjection_mk F t w g
  have qS (v : S) : finiteQuotientProjection F t v.1 q =
      Quotient.mk'' (finiteComponent F (t + 1) v.1 g) :=
    hg ▸ finiteQuotientProjection_mk F t v.1 g
  simp only [realComponent_pad F h, complexComponent_pad F h, finiteComponent_pad F h, qR, qC, qS,
    ArchimedeanLocal.realUnequalIntegrand, ArchimedeanLocal.complexUnequalIntegrand, eR, eC, eS,
    Finset.prod_mul_distrib]
  ring

variable (hx : IsSphericalOutside F T S x)
variable (hsupp : FunctionalEquationComparison.FiniteAdditiveSupport ψ S)

include hψ hW hW' hR hR' hC hC' hS hS' hx hsupp in
/-- The dual pointwise factorization with the same scalar and rectangular support. -/
theorem dual_product (s : ℂ) (q : WhittakerQuotient F (t + 1))
    (hq : q ∈ unipotentIntegralClasses F (t + 1) S)
    (y : Matrix (Fin (r - (t + 1))) (Fin (t + 1)) (Adeles F)) :
    dualWhittakerKernel F h (Unfolding.dualWhittaker F h T ψ.complex x)
        (dualFunction F (t + 1) (cuspWhittaker F T' ψ.complex⁻¹ x')) s q y =
      (c * c') * (rectIntegralOutside F (r - (t + 1)) (t + 1) S).indicator (fun y =>
        (∏ v, ArchimedeanLocal.realUnequalDualKernel h (L.real v) (M.real v) s
          (realQuotientProjection F t v q, realRectCoordinates F v y)) *
        (∏ w, ArchimedeanLocal.complexUnequalDualKernel h (L.complex w) (M.complex w) s
          (complexQuotientProjection F t w q, complexRectCoordinates F w y)) *
        ∏ v : S, ArchimedeanLocal.blockKernel
          (normalizedAbsoluteValue (padicField v.1).canonicalTopologicalData) h
          (ArchimedeanLocal.translateFunction (ArchimedeanLocal.unfoldingWeyl h)
            (ArchimedeanLocal.dualFunction (r + 1) (L.finite v)))
          (ArchimedeanLocal.dualFunction (t + 1) (M.finite v)) s
          (finiteQuotientProjection F t v.1 q) (localRectCoordinates F v.1 y)) y := by
  obtain ⟨g, hg, hK⟩ := exists_integral_rep F S q hq
  rw [dualKernel_of_rep F h T T' ψ.complex hψ x x' s q g hg y]
  by_cases hy : y ∈ rectIntegralOutside F (r - (t + 1)) (t + 1) S
  · rw [Set.indicator_of_mem hy]
    have hp := hW.dual (rectangularPoint F h g y * unfoldingWeyl F h)
      (fun v hv => rect_weyl_integral h v g (hK v hv) y (hy v hv))
    simp only [Unfolding.dualWhittaker, translateFunction]
    rw [hp, hW'.dual g hK, DeterminantProducts.detPower_product F (t + 1) S g
      (mem_partial_of_integral F S g hK)]
    have eR (v : {v : InfinitePlace F // v.IsReal}) :=
      dualKernel_mk realNormalizedAbs h (χR v) (hR v) (hR' v) s
        (realComponent F (t + 1) v g) (realRectCoordinates F v y)
    have eC (w : {w : InfinitePlace F // w.IsComplex}) :=
      dualKernel_mk complexNormalizedAbs h (χC w) (hC w) (hC' w) s
        (complexComponent F (t + 1) w g) (complexRectCoordinates F w y)
    have eS (v : S) :=
      dualKernel_mk (normalizedAbsoluteValue (padicField v.1).canonicalTopologicalData)
        h (χS v) (hS v) (hS' v) s (finiteComponent F (t + 1) v.1 g) (localRectCoordinates F v.1 y)
    have qR (v : {v : InfinitePlace F // v.IsReal}) :
        realQuotientProjection F t v q = Quotient.mk'' (realComponent F (t + 1) v g) :=
      hg ▸ realQuotientProjection_mk F t v g
    have qC (w : {w : InfinitePlace F // w.IsComplex}) :
        complexQuotientProjection F t w q = Quotient.mk'' (complexComponent F (t + 1) w g) :=
      hg ▸ complexQuotientProjection_mk F t w g
    have qS (v : S) : finiteQuotientProjection F t v.1 q =
        Quotient.mk'' (finiteComponent F (t + 1) v.1 g) := hg ▸ finiteQuotientProjection_mk F t v.1 g
    have hrect (v : FinitePlace F) :
        finiteComponent F (r + 1) v (rectangularPoint F h g y) =
          ArchimedeanLocal.rectangularPoint h (finiteComponent F (t + 1) v g)
            (localRectCoordinates F v y) := UnequalDualEuler.finiteComponent_rectangularPoint F h v g y
    simp only [realComponent_mul, complexComponent_mul, UnipotentClass.finiteComponent_mul,
      realComponent_rectangularPoint F h, complexComponent_rectangularPoint F h,
      hrect,
      realComponent_unfoldingWeyl F h, complexComponent_unfoldingWeyl F h,
      finiteComponent_unfoldingWeyl F h, qR, qC, qS,
      ArchimedeanLocal.realUnequalDualKernel, ArchimedeanLocal.complexUnequalDualKernel,
      eR, eC, eS, Finset.prod_mul_distrib]
    ring
  · have hv : ∃ v ∉ S, ¬ ∀ i j, finiteProjection F v (y i j) ∈ v.adicCompletionIntegers F := by
      by_contra hn
      exact hy (fun v hv => by_contra fun hfail => hn ⟨v, hv, hfail⟩)
    obtain ⟨v, hv, hbad⟩ := hv
    obtain ⟨ψv, hψv, hcond⟩ := hsupp v hv
    rw [dualWhittaker_eq_zero_of_not_rectIntegral h ψ hψ T x S hx v hv ψv hψv hcond g y hbad,
      Set.indicator_of_notMem hy, zero_mul, zero_mul, mul_zero]

end Assembly

end Langlands.Global.RankinSelbergGlobal.UnequalKernelPointwise
