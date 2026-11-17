import Langlands.Global.RankinSelberg.ComplexPlaceFunctionalEquationReduction
import Langlands.Global.RankinSelberg.ComplexPlaceIsotypic
import Langlands.Global.RankinSelberg.UnramifiedWhittakerFactorizationProof

/-!
# Equivariance of archimedean restrictions of global Whittaker functions at a complex place

For an actual cuspidal realization `T`, a complex place `w`, a finite adelic point `b` and a
`(𝔤, K)`-map `A` at `w`, the functions `g ↦ W_(A f)(ι_w(g) b)` transform under right
translation by `U(r+1)` as the functions `f` of the standard module do.
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
/-- The entries at a complex place `v` of `ι_w(g)`. -/
theorem complexPlaceGL_entry (w v : {v : InfinitePlace F // v.IsComplex})
    (g : Matrix.GeneralLinearGroup (Fin n) ℂ) (i j : Fin n) :
    (((complexPlaceGL F n w g : ArchimedeanGL F n) :
        Matrix (Fin n) (Fin n) (mixedEmbedding.mixedSpace F)) i j).2 v =
      (((Pi.mulSingle w g : {v : InfinitePlace F // v.IsComplex} →
        Matrix.GeneralLinearGroup (Fin n) ℂ) v : Matrix.GeneralLinearGroup (Fin n) ℂ) :
          Matrix (Fin n) (Fin n) ℂ) i j := rfl

omit [NumberField F] in
/-- The archimedean matrix of the compact factor of `l ∈ U(n)` at `w` is `ι_w(l)`. -/
theorem toArchimedeanGL_complexPlaceFactor (w : {v : InfinitePlace F // v.IsComplex})
    (l : Matrix.unitaryGroup (Fin n) ℂ) :
    ArchimedeanCompactFactors.toArchimedeanGL F n
        (ArchimedeanCompactFactors.complexPlaceFactor F n w l) =
      complexPlaceGL F n w (Unitary.toUnits l) := by
  apply Units.ext
  funext i j
  refine Prod.ext (funext fun v => ?_) (funext fun v => ?_)
  · rfl
  · have hL : ((ArchimedeanCompactFactors.toArchimedeanGL F n
          (ArchimedeanCompactFactors.complexPlaceFactor F n w l) :
            Matrix (Fin n) (Fin n) (mixedEmbedding.mixedSpace F)) i j).2 v =
        (((ArchimedeanCompactFactors.complexPlaceFactor F n w l).2 v :
          Matrix.unitaryGroup (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) i j := rfl
    rw [hL, complexPlaceGL_entry, ArchimedeanCompactFactors.complexPlaceFactor_snd]
    by_cases hv : v = w
    · subst hv
      simp only [Pi.mulSingle_eq_same]
      rfl
    · simp only [ne_eq, hv, not_false_eq_true, Pi.mulSingle_eq_of_ne]
      rfl

omit [NumberField F] in
/-- The infinite adelic element of the compact action of `l ∈ U(n)` at `w`. -/
theorem complexPlaceCompactInclusion_val (w : {v : InfinitePlace F // v.IsComplex})
    (l : Matrix.unitaryGroup (Fin n) ℂ) :
    (complexPlaceCompactInclusion F n w l).val =
      (archimedeanGLCoordinates F n).symm (complexPlaceGL F n w (Unitary.toUnits l)) := by
  rw [← toArchimedeanGL_complexPlaceFactor]
  rfl

/-- Right translation of `ι_w(g) b` by the compact element `ι_w(k)` is `ι_w(g k) b`. -/
theorem complexPlacePoint_mul_compact (w : {v : InfinitePlace F // v.IsComplex})
    (g k : Matrix.GeneralLinearGroup (Fin n) ℂ) (b : FiniteAdelicGL F n) :
    complexPlacePoint F n w g * finitePoint F n b *
        (GeneralLinearGroupPoints.adelicEquiv F n).symm
          (AdelicGL.ofInfinite F n ((archimedeanGLCoordinates F n).symm (complexPlaceGL F n w k))) =
      complexPlacePoint F n w (g * k) * finitePoint F n b := by
  have hpair : ∀ (a c : InfiniteAdelicGL F n) (b d : FiniteAdelicGL F n),
      AdelicGL.pair F n a b * AdelicGL.pair F n c d = AdelicGL.pair F n (a * c) (b * d) :=
    fun a c b d => ((AdelicGL.split F n).symm.map_mul (a, b) (c, d)).symm
  have hinf : ∀ c : InfiniteAdelicGL F n, AdelicGL.ofInfinite F n c = AdelicGL.pair F n c 1 :=
    fun _ => rfl
  apply (GeneralLinearGroupPoints.adelicEquiv F n).injective
  simp only [map_mul, MulEquiv.apply_symm_apply, complexPlacePoint, finitePoint, adelicPoint]
  rw [hinf, hpair, hpair, hpair]
  congr 1
  · simp only [map_one, mul_one]
  · simp only [mul_one, one_mul]

end Points


section Theta

variable (F : Type u) [Field F] [NumberField F] (n : ℕ)

/-- `ι_w(g)` is the image of an infinite adelic element. -/
theorem complexPlacePoint_eq_ofInfinite (w : {v : InfinitePlace F // v.IsComplex})
    (g : Matrix.GeneralLinearGroup (Fin n) ℂ) :
    complexPlacePoint F n w g = (GeneralLinearGroupPoints.adelicEquiv F n).symm
      (AdelicGL.ofInfinite F n ((archimedeanGLCoordinates F n).symm (complexPlaceGL F n w g))) :=
  rfl

/-- `g ↦ ι_w(g)` is multiplicative. -/
theorem complexPlacePoint_mul (w : {v : InfinitePlace F // v.IsComplex})
    (g h : Matrix.GeneralLinearGroup (Fin n) ℂ) :
    complexPlacePoint F n w (g * h) = complexPlacePoint F n w g * complexPlacePoint F n w h := by
  rw [complexPlacePoint_eq_ofInfinite, complexPlacePoint_eq_ofInfinite,
    complexPlacePoint_eq_ofInfinite, map_mul, map_mul, map_mul, map_mul]

/-- The adelic entries of `ι_w(g)`. -/
theorem complexPlacePoint_entry (w : {v : InfinitePlace F // v.IsComplex})
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
theorem complexPlaceGL_entry_fst (w : {v : InfinitePlace F // v.IsComplex})
    (g : Matrix.GeneralLinearGroup (Fin n) ℂ) (i j : Fin n)
    (v : {v : InfinitePlace F // v.IsReal}) :
    (((complexPlaceGL F n w g : ArchimedeanGL F n) :
        Matrix (Fin n) (Fin n) (mixedEmbedding.mixedSpace F)) i j).1 v =
      (1 : Matrix (Fin n) (Fin n) ℝ) i j := rfl

omit [NumberField F] in
theorem complexPlaceGL_entry_eq_zero (w : {v : InfinitePlace F // v.IsComplex})
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
theorem complexPlaceGL_entry_eq_one (w : {v : InfinitePlace F // v.IsComplex})
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
theorem complexPlacePoint_mem_unipotentAdelic (w : {v : InfinitePlace F // v.IsComplex})
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
theorem complexPlaceGL_superdiag_sum {r : ℕ} (w : {v : InfinitePlace F // v.IsComplex})
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

/-- A finite sum of adeles given by their infinite and finite components. -/
theorem adeles_sum_mk {J : Type*} (s : Finset J) (a : J → InfiniteAdeles F)
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
theorem genericCharacter_complexPlacePoint {r : ℕ} (χ : AddChar (Adeles F) ℂ)
    (w : {v : InfinitePlace F // v.IsComplex}) (c : ℂˣ)
    (hχ : ∀ y : InfinitePlace.Completion w.1,
      χ (((Pi.single w.1 y : InfiniteAdeles F), (0 : FiniteAdeles F)) : Adeles F) =
        ((complexScaledCharacter c
          (InfinitePlace.Completion.ringEquivComplexOfIsComplex w.2 y) : Circle) : ℂ))
    {u : Matrix.GeneralLinearGroup (Fin (r + 1)) ℂ}
    (hu : u ∈ GeneralLinear.upperUnipotent (r + 1) ℂ) :
    genericCharacter F r χ (fun _ => 1)
        ⟨complexPlacePoint F (r + 1) w u, complexPlacePoint_mem_unipotentAdelic F (r + 1) w hu⟩ =
      complexWhittakerCharacter c u := by
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
    refine (Finset.sum_congr rfl fun i _ => hterm i).trans ((adeles_sum_mk F _ _ _).trans ?_)
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

end Theta

section Component

variable {F : Type u} [Field F] [NumberField F]

open Langlands.Global.HeckeFunctionalEquation

open scoped Classical in
/-- If the component of `ψ` at `w` is `ψ_a`, the hypothesis of
`genericCharacter_complexPlacePoint` holds for `ψ` and `a`. -/
theorem complexComponent_complex (ψ : HarmonicAnalysis.UnitaryAdditiveCharacter (Adeles F))
    (w : {v : InfinitePlace F // v.IsComplex}) (a : ℂˣ)
    (ha : IsComplexAdditiveComponent ψ w.1 w.2 a) (y : InfinitePlace.Completion w.1) :
    ψ.complex (((Pi.single w.1 y : InfiniteAdeles F), (0 : FiniteAdeles F)) : Adeles F) =
      ((complexScaledCharacter a
        (InfinitePlace.Completion.ringEquivComplexOfIsComplex w.2 y) : Circle) : ℂ) :=
  congrArg (fun z : Circle => (z : ℂ)) (ha y)

open scoped Classical in
/-- If the component of `ψ` at `w` is `ψ_a`, the component of `ψ⁻¹` is `ψ_(-a)`. -/
theorem complexComponent_complex_inv (ψ : HarmonicAnalysis.UnitaryAdditiveCharacter (Adeles F))
    (w : {v : InfinitePlace F // v.IsComplex}) (a : ℂˣ)
    (ha : IsComplexAdditiveComponent ψ w.1 w.2 a) (y : InfinitePlace.Completion w.1) :
    ψ.complex⁻¹ (((Pi.single w.1 y : InfiniteAdeles F), (0 : FiniteAdeles F)) : Adeles F) =
      ((complexScaledCharacter (-a)
        (InfinitePlace.Completion.ringEquivComplexOfIsComplex w.2 y) : Circle) : ℂ) := by
  have hneg : -(((Pi.single w.1 y : InfiniteAdeles F), (0 : FiniteAdeles F)) : Adeles F) =
      (((Pi.single w.1 (-y) : InfiniteAdeles F), (0 : FiniteAdeles F)) : Adeles F) := by
    refine Prod.ext ?_ ?_
    · exact (Pi.single_neg w.1 y).symm
    · exact neg_zero
  have hval : complexScaledCharacter a
      (InfinitePlace.Completion.ringEquivComplexOfIsComplex w.2 (-y)) =
      complexScaledCharacter (-a)
        (InfinitePlace.Completion.ringEquivComplexOfIsComplex w.2 y) := by
    rw [map_neg, complexScaledCharacter_apply, complexScaledCharacter_apply, Units.val_neg,
      mul_neg, neg_mul]
  exact ((AddChar.inv_apply _ _).trans (congrArg ψ.complex hneg)).trans
    ((complexComponent_complex ψ w a ha (-y)).trans (congrArg (fun z : Circle => (z : ℂ)) hval))

end Component

section Whittaker

variable {F : Type u} [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]

/-- The realized function of the compact action at `w` is a right translate. -/
theorem cuspFunction_complexPlaceCompact {r : ℕ} (T : CuspidalOperatorRealization F r)
    (w : {v : InfinitePlace F // v.IsComplex}) (l : Matrix.unitaryGroup (Fin (r + 1)) ℂ)
    (y : T.Space) (z : Points F (r + 1)) :
    cuspFunction F T (T.realization.complexPlaceCompactRepresentation w l y) z =
      cuspFunction F T y (z * (GeneralLinearGroupPoints.adelicEquiv F (r + 1)).symm
        (AdelicGL.ofInfinite F (r + 1) (complexPlaceCompactInclusion F (r + 1) w l).val)) := by
  simp only [UnequalAnalytic.cuspFunction_eq F T]
  change ContinuousRationalFunctions.evaluate F (r + 1) (T.realization.toContinuous y)
      (GeneralLinearGroupPoints.adelicEquiv F (r + 1) z *
        AdelicGL.ofInfinite F (r + 1) (complexPlaceCompactInclusion F (r + 1) w l).val) =
    ContinuousRationalFunctions.evaluate F (r + 1) (T.realization.toContinuous y)
      (GeneralLinearGroupPoints.adelicEquiv F (r + 1)
        (z * (GeneralLinearGroupPoints.adelicEquiv F (r + 1)).symm
          (AdelicGL.ofInfinite F (r + 1) (complexPlaceCompactInclusion F (r + 1) w l).val)))
  have h := (GeneralLinearGroupPoints.adelicEquiv F (r + 1)).map_mul z
    ((GeneralLinearGroupPoints.adelicEquiv F (r + 1)).symm
      (AdelicGL.ofInfinite F (r + 1) (complexPlaceCompactInclusion F (r + 1) w l).val))
  rw [MulEquiv.apply_symm_apply] at h
  exact congrArg (ContinuousRationalFunctions.evaluate F (r + 1)
    (T.realization.toContinuous y)) h.symm

/-- The Whittaker coefficient of the compact action at `w` is a right translate. -/
theorem cuspWhittaker_complexPlaceCompact {r : ℕ} (ψ : AddChar (Adeles F) ℂ)
    (T : CuspidalOperatorRealization F r)
    (w : {v : InfinitePlace F // v.IsComplex}) (l : Matrix.unitaryGroup (Fin (r + 1)) ℂ)
    (y : T.Space) (g : Points F (r + 1)) :
    cuspWhittaker F T ψ (T.realization.complexPlaceCompactRepresentation w l y) g =
      cuspWhittaker F T ψ y (g * (GeneralLinearGroupPoints.adelicEquiv F (r + 1)).symm
        (AdelicGL.ofInfinite F (r + 1) (complexPlaceCompactInclusion F (r + 1) w l).val)) := by
  simp only [cuspWhittaker, generalLinearWhittakerFunction,
    Unfolding.subgroupCharacterCoefficient_eq_integral]
  congr 1
  funext q
  simp only [Unfolding.coefficientIntegrand, cuspFunction_complexPlaceCompact, mul_assoc]

/-- **`U(r+1)`-equivariance.** For a `(𝔤, K)`-map `A` at `w`, if `f'` is the right translate
of `f` by `k ∈ U(r+1)`, then `g ↦ W_(A f')(ι_w(g) b)` is the right translate by `k` of
`g ↦ W_(A f)(ι_w(g) b)`. -/
theorem complexPlaceRestriction_rightTranslation {r : ℕ} (ψ : AddChar (Adeles F) ℂ)
    (T : CuspidalOperatorRealization F r) (w : {v : InfinitePlace F // v.IsComplex})
    (b : FiniteAdelicGL F (r + 1)) {d : List ComplexCharacterData}
    {A : complexStandardKFinite (r + 1) d →ₗ[ℂ] T.Space}
    (hA : T.realization.IsComplexPlaceMap w d A)
    (k : Archimedean.unitaryCompact ℂ (r + 1)) (f f' : complexStandardKFinite (r + 1) d)
    (hf' : (f' : Langlands.GeneralLinear (r + 1) ℂ → ℂ) =
      Whittaker.rightTranslation ℂ (Langlands.GeneralLinear (r + 1) ℂ)
        (k : Langlands.GeneralLinear (r + 1) ℂ) f) :
    (fun g => cuspWhittaker F T ψ (A f')
        (complexPlacePoint F (r + 1) w g * finitePoint F (r + 1) b)) =
      Whittaker.rightTranslation ℂ (Langlands.GeneralLinear (r + 1) ℂ)
        (k : Langlands.GeneralLinear (r + 1) ℂ)
        (fun g => cuspWhittaker F T ψ (A f)
          (complexPlacePoint F (r + 1) w g * finitePoint F (r + 1) b)) := by
  refine Exists.elim (hA.1 k f) fun hf he => ?_
  let l : Matrix.unitaryGroup (Fin (r + 1)) ℂ :=
    ⟨((k : Langlands.GeneralLinear (r + 1) ℂ) : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ), k.2⟩
  have hk : Unitary.toUnits l = (k : Langlands.GeneralLinear (r + 1) ℂ) := Units.ext rfl
  have hAf' : A f' = T.realization.complexPlaceCompactRepresentation w l (A f) :=
    (congrArg A (Subtype.ext hf' : f' = ⟨_, hf⟩)).trans he
  funext g
  have hpt : complexPlacePoint F (r + 1) w g * finitePoint F (r + 1) b *
      (GeneralLinearGroupPoints.adelicEquiv F (r + 1)).symm
        (AdelicGL.ofInfinite F (r + 1) (complexPlaceCompactInclusion F (r + 1) w l).val) =
      complexPlacePoint F (r + 1) w (g * (k : Langlands.GeneralLinear (r + 1) ℂ)) *
        finitePoint F (r + 1) b := by
    rw [complexPlaceCompactInclusion_val, hk]
    exact complexPlacePoint_mul_compact F (r + 1) w g _ b
  exact (congrArg (fun y => cuspWhittaker F T ψ y
      (complexPlacePoint F (r + 1) w g * finitePoint F (r + 1) b)) hAf').trans
    ((cuspWhittaker_complexPlaceCompact ψ T w l (A f) _).trans
      (congrArg (cuspWhittaker F T ψ (A f)) hpt))

open scoped Classical in
/-- **`θ`-equivariance.** If `χ` is a standard character of `𝔸` with component `ψ_c` at `w`,
then for `u ∈ N_(r+1)(ℂ)`, `W_x(ι_w(u g) b) = ψ_c(∑ u_(i,i+1)) W_x(ι_w(g) b)`. -/
theorem complexPlaceRestriction_mul_left {r : ℕ} (χ : AddChar (Adeles F) ℂ)
    (hχstd : IsStandardAdditiveCharacter F χ) (w : {v : InfinitePlace F // v.IsComplex})
    (c : ℂˣ)
    (hχ : ∀ y : InfinitePlace.Completion w.1,
      χ (((Pi.single w.1 y : InfiniteAdeles F), (0 : FiniteAdeles F)) : Adeles F) =
        ((complexScaledCharacter c
          (InfinitePlace.Completion.ringEquivComplexOfIsComplex w.2 y) : Circle) : ℂ))
    (T : CuspidalOperatorRealization F r) (b : FiniteAdelicGL F (r + 1)) (x : T.Space)
    {u : Matrix.GeneralLinearGroup (Fin (r + 1)) ℂ}
    (hu : u ∈ GeneralLinear.upperUnipotent (r + 1) ℂ)
    (g : Matrix.GeneralLinearGroup (Fin (r + 1)) ℂ) :
    cuspWhittaker F T χ x (complexPlacePoint F (r + 1) w (u * g) * finitePoint F (r + 1) b) =
      complexWhittakerCharacter c u *
        cuspWhittaker F T χ x (complexPlacePoint F (r + 1) w g * finitePoint F (r + 1) b) := by
  rw [complexPlacePoint_mul, mul_assoc]
  exact (Unfolding.cuspWhittaker_mul_left F T χ hχstd x
    ⟨_, complexPlacePoint_mem_unipotentAdelic F (r + 1) w hu⟩ _).trans
      (congrArg (· * _) (genericCharacter_complexPlacePoint F χ w c hχ hu))

end Whittaker

end Langlands.Global.RankinSelbergGlobal
