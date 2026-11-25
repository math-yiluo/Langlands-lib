import Langlands.Automorphic.CuspidalArchimedeanParameterExistenceTC
import Langlands.Global.RankinSelberg.RealRankZeroParameter
import Langlands.Representation.Archimedean.PrincipalSeriesGKModule
import Langlands.Representation.Archimedean.RealJacquetFrobeniusProof

/-! # Complex-place parameters and real parameters for GL₁ -/

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open NumberField
open scoped Matrix.Norms.Operator TensorProduct

universe u

namespace Langlands.Global

open Automorphic
open Langlands.Archimedean
open LocalFactor.Archimedean

variable {F : Type u} [Field F] [NumberField F]

/-- Every complex place of a number field has standard-module parameters for
actual cuspidal realizations in all positive ranks. -/
theorem exists_cuspidalComplexPlaceParameter [CompactSpace (AdeleQuotient F)]
    {r : ℕ} (T : CuspidalOperatorRealization F r)
    (v : {v : InfinitePlace F // v.IsComplex}) :
    ∃ ds, T.realization.HasComplexPlaceParameter v ds := by
  have hG := cuspidalArchimedeanGenericComponentBridge
    cuspidalArchimedeanIrreducibleAdmissibleComponent cuspidalArchimedeanWhittakerFunctional
    F r T
  obtain ⟨V, _, _, ρ, π, ι, hι, hρ, hπ, hgk, hirr, hadm, hgen⟩ := hG.2 v
  obtain ⟨ds, hds⟩ := Archimedean.complexGenericStandardParameter (r + 1) V ρ π hgk hirr hadm hgen
  exact ⟨ds, OperatorRealization.hasComplexPlaceParameter_of_component hι hρ hπ hds⟩

section RankOne

open RankinSelbergGlobal.RealRankZero

private local instance : AddCommGroup (RationalInvariantFunctions F 1) := Submodule.addCommGroup _
private local instance : AddCommGroup (ContinuousRationalFunctions F 1) := Submodule.addCommGroup _
private local instance : AddCommGroup (FiniteSmoothRationalFunctions F 1) := Submodule.addCommGroup _
private local instance : AddCommGroup (AutomorphicForms F 1) := Submodule.addCommGroup _
private local instance : AddCommGroup (StableAutomorphicFunctions F 1) := Submodule.addCommGroup _
private local instance (T : OperatorRealization F 1) : AddCommGroup T.Space := Submodule.addCommGroup _

private theorem rankOne_standard_eq_eval_smul (c : RealCharacterData)
    (f : realStandardKFinite 1 [RealBlock.character c]) :
    (f : Langlands.GeneralLinear 1 ℝ → ℂ) = f.val 1 • characterFunction c := by
  funext g
  let a : Fin 1 → ℝˣ := fun _ => GeneralLinear.determinant g
  have hg : (GeneralLinear.Iwasawa.diagonalUnits a : Langlands.GeneralLinear 1 ℝ) = g := by
    apply Units.ext
    rw [GeneralLinear.Iwasawa.diagonalUnits_val]
    ext i j
    fin_cases i
    fin_cases j
    simp [a]
  have hf := (Submodule.mem_inf.mp f.2).1.1.2 a 1 1
  simpa [hg, principalSeriesCharacter, realPositionCharacter, a, characterFunction, mul_comm]
    using hf

private theorem rankOne_unitary_eq_one_or_minusOne (k : Matrix.unitaryGroup (Fin 1) ℝ) :
    k = 1 ∨ k = minusOneOrthogonal := by
  have hdet := (Matrix.det_of_mem_unitary k.2).1
  have hsq : (k.val 0 0) * (k.val 0 0) = 1 := by
    simpa [Matrix.det_fin_one] using hdet
  rcases mul_self_eq_one_iff.mp hsq with h | h
  · left
    apply Subtype.ext
    ext i j
    fin_cases i
    fin_cases j
    simpa using h
  · right
    apply Subtype.ext
    ext i j
    fin_cases i
    fin_cases j
    simpa [minusOneOrthogonal] using h

set_option maxHeartbeats 1000000 in
private theorem rankOne_compactSign (T : OperatorRealization F 1) (hT : T.IsIrreducible)
    (v : {v : InfinitePlace F // v.IsReal}) {x : T.Space} (hx : x ≠ 0) :
    ∃ e : Fin 2, ∀ f : T.Space, T.realPlaceCompactRepresentation v minusOneOrthogonal f =
      ((-1 : ℂ) ^ e.val) • f := by
  obtain ⟨ε, hε⟩ := exists_compactRepresentation_eq_smul T hT
    (realPlaceCompactInclusion F 1 v minusOneOrthogonal)
  change ∀ f : T.Space, T.realPlaceCompactRepresentation v minusOneOrthogonal f = ε • f at hε
  have hk : minusOneOrthogonal * minusOneOrthogonal = 1 := by
    apply Subtype.ext
    change (-1 : Matrix (Fin 1) (Fin 1) ℝ) * (-1) = 1
    simp
  let ρ := T.realPlaceCompactRepresentation v
  have hε₂ : ε * ε = 1 := eq_of_smul_eq_smul hx (calc
    (ε * ε) • x = ε • (ε • x) := mul_smul _ _ _
    _ = ε • ρ minusOneOrthogonal x := congrArg (fun y : T.Space => ε • y) (hε x).symm
    _ = ρ minusOneOrthogonal (ρ minusOneOrthogonal x) := (hε _).symm
    _ = ρ (minusOneOrthogonal * minusOneOrthogonal) x :=
      (LinearMap.congr_fun (map_mul ρ minusOneOrthogonal minusOneOrthogonal) x).symm
    _ = ρ 1 x := congrArg (fun k => ρ k x) hk
    _ = (1 : ℂ) • x := (LinearMap.congr_fun (map_one ρ) x).trans (one_smul ℂ x).symm)
  rcases mul_self_eq_one_iff.mp hε₂ with h | h
  · exact ⟨0, fun f => (hε f).trans
      (congrArg (fun z : ℂ => z • f) (h.trans (pow_zero (-1 : ℂ)).symm))⟩
  · exact ⟨1, fun f => (hε f).trans
      (congrArg (fun z : ℂ => z • f) (h.trans (pow_one (-1 : ℂ)).symm))⟩

private theorem rankOne_LieDirection (X : Matrix (Fin 1) (Fin 1) ℝ) :
    X = (X 0 0) • (1 : Matrix (Fin 1) (Fin 1) ℝ) := by
  ext i j
  fin_cases i
  fin_cases j
  simp

private theorem rankOne_complexifiedDirection (X : Matrix (Fin 1) (Fin 1) ℝ) :
    ((1 : ℂ) ⊗ₜ[ℝ] X) =
      ((X 0 0 : ℝ) : ℂ) • ((1 : ℂ) ⊗ₜ[ℝ] (1 : Matrix (Fin 1) (Fin 1) ℝ)) := by
  calc
    _ = (1 : ℂ) ⊗ₜ[ℝ] ((X 0 0) • (1 : Matrix (Fin 1) (Fin 1) ℝ)) :=
      congrArg (fun Y => (1 : ℂ) ⊗ₜ[ℝ] Y) (rankOne_LieDirection X)
    _ = ((X 0 0) • (1 : ℂ)) ⊗ₜ[ℝ] (1 : Matrix (Fin 1) (Fin 1) ℝ) :=
      (TensorProduct.smul_tmul _ _ _).symm
    _ = _ := by rw [TensorProduct.smul_tmul', Complex.real_smul]; rfl

private theorem rankOne_rightTranslation (c : RealCharacterData)
    (f : realStandardKFinite 1 [RealBlock.character c]) (k : Langlands.GeneralLinear 1 ℝ) :
    Whittaker.rightTranslation ℂ (Langlands.GeneralLinear 1 ℝ) k f.val =
      characterFunction c k • f.val := by
  calc
    _ = Whittaker.rightTranslation ℂ (Langlands.GeneralLinear 1 ℝ)
          k (f.val 1 • characterFunction c) :=
      congrArg _ (rankOne_standard_eq_eval_smul c f)
    _ = characterFunction c k • (f.val 1 • characterFunction c) := by
      funext g
      change f.val 1 * characterFunction c (g * k) =
        characterFunction c k * (f.val 1 * characterFunction c g)
      rw [characterFunction_mul]
      ring
    _ = _ := congrArg _ (rankOne_standard_eq_eval_smul c f).symm

private theorem rankOne_rightDerivative (c : RealCharacterData)
    (f : realStandardKFinite 1 [RealBlock.character c]) (X : Matrix (Fin 1) (Fin 1) ℝ) :
    rightDerivative (matrixModel ℝ 1) X f.val = (((X 0 0 : ℝ) : ℂ) * c.exponent) • f.val := by
  calc
    _ = rightDerivative (matrixModel ℝ 1) X (f.val 1 • characterFunction c) :=
      congrArg _ (rankOne_standard_eq_eval_smul c f)
    _ = (((X 0 0 : ℝ) : ℂ) * c.exponent) • (f.val 1 • characterFunction c) := by
      conv_lhs => rw [rankOne_LieDirection X]
      rw [rightDerivative_smul_left, rightDerivative_smul (contMDiff_characterFunction c),
        rightDerivative_characterFunction]
      funext g
      simp only [Pi.smul_apply, Complex.real_smul, smul_eq_mul]
      ring
    _ = _ := congrArg _ (rankOne_standard_eq_eval_smul c f).symm

set_option maxHeartbeats 1000000 in
/-- An irreducible rank-one operator realization has a one-character
standard-module parameter at each real place. -/
theorem exists_rankOne_realPlaceParameter (T : OperatorRealization F 1) (hT : T.IsIrreducible)
    (v : {v : InfinitePlace F // v.IsReal}) :
    ∃ c : RealCharacterData, T.HasRealPlaceParameter v [RealBlock.character c] := by
  obtain ⟨x, g, hg⟩ := T.exists_evaluate_ne_zero hT
  have hx : x ≠ 0 := by
    intro h
    rw [h, map_zero] at hg
    exact hg rfl
  obtain ⟨e, hε⟩ := rankOne_compactSign T hT v hx
  obtain ⟨lam, hlam⟩ := exists_realPlaceLieAction_eq_smul T hT v
    ((1 : ℂ) ⊗ₜ[ℝ] (1 : Matrix (Fin 1) (Fin 1) ℝ))
  let c := RealJacquetFrobenius.charData e lam
  let A : realStandardKFinite 1 [RealBlock.character c] →ₗ[ℂ] T.Space :=
    { toFun := fun f => f.val 1 • x
      map_add' := fun f f' => add_smul (f.val 1) (f'.val 1) x
      map_smul' := fun z f => mul_smul z (f.val 1) x }
  have hA : Function.Injective A := by
    intro f f' he
    have he' : f.val 1 = f'.val 1 := eq_of_smul_eq_smul hx he
    exact Subtype.ext (by
      rw [rankOne_standard_eq_eval_smul c f, rankOne_standard_eq_eval_smul c f', he'])
  refine ⟨c, rfl, A, hA, ?_, ?_⟩
  · intro k f
    let k₀ : Matrix.unitaryGroup (Fin 1) ℝ := ⟨(k.val : Matrix (Fin 1) (Fin 1) ℝ), k.2⟩
    have htr := rankOne_rightTranslation c f k.val
    have hm : Whittaker.rightTranslation ℂ (Langlands.GeneralLinear 1 ℝ) k.val f.val ∈
        realStandardKFinite 1 [RealBlock.character c] := by
      rw [htr]
      exact Submodule.smul_mem _ _ f.2
    refine ⟨hm, ?_⟩
    have he : (⟨_, hm⟩ : realStandardKFinite 1 [RealBlock.character c]) =
        characterFunction c k.val • f := Subtype.ext htr
    rw [he, map_smul]
    change characterFunction c k.val • A f = T.realPlaceCompactRepresentation v k₀ (A f)
    let ρ := T.realPlaceCompactRepresentation v
    rcases rankOne_unitary_eq_one_or_minusOne k₀ with he | he
    · have hk' : k.val = 1 := Units.ext (congrArg Subtype.val he)
      have hρ : ρ k₀ (A f) = A f := by rw [he, map_one, Module.End.one_apply]
      exact (by rw [hk', characterFunction_one, one_smul] : _ = A f).trans hρ.symm
    · have hk' : k.val = Unitary.toUnits minusOneOrthogonal :=
        Units.ext (congrArg Subtype.val he)
      have hρ : ρ k₀ (A f) = (-1 : ℂ) ^ e.val • A f :=
        (congrArg (fun j => ρ j (A f)) he).trans (hε (A f))
      have hd : characterFunction c k.val = (-1 : ℂ) ^ e.val := by
        rw [hk', toUnits_minusOneOrthogonal, characterFunction, determinant_scalarUnit,
          character_neg_one]
        rfl
      exact (congrArg (fun z : ℂ => z • A f) hd).trans hρ.symm
  · intro X f
    have hder := rankOne_rightDerivative c f X
    have hm : rightDerivative (matrixModel ℝ 1) X f.val ∈
        realStandardKFinite 1 [RealBlock.character c] := by
      rw [hder]
      exact Submodule.smul_mem _ _ f.2
    refine ⟨hm, ?_⟩
    have he : (⟨_, hm⟩ : realStandardKFinite 1 [RealBlock.character c]) =
        (((X 0 0 : ℝ) : ℂ) * c.exponent) • f := Subtype.ext hder
    have hAction :
        T.realPlaceLieAction v ((1 : ℂ) ⊗ₜ[ℝ] X) (A f) =
          (((X 0 0 : ℝ) : ℂ) * lam) • A f := by
      calc
        _ = T.realPlaceLieAction v (((X 0 0 : ℝ) : ℂ) •
            ((1 : ℂ) ⊗ₜ[ℝ] (1 : Matrix (Fin 1) (Fin 1) ℝ))) (A f) :=
          congrArg (fun Y => T.realPlaceLieAction v Y (A f)) (rankOne_complexifiedDirection X)
        _ = ((X 0 0 : ℝ) : ℂ) • T.realPlaceLieAction v
            ((1 : ℂ) ⊗ₜ[ℝ] (1 : Matrix (Fin 1) (Fin 1) ℝ)) (A f) :=
          LinearMap.congr_fun (map_smul (T.realPlaceLieAction v) _ _) (A f)
        _ = _ := (congrArg (fun y : T.Space => ((X 0 0 : ℝ) : ℂ) • y) (hlam (A f))).trans
          (mul_smul _ _ _).symm
    exact (congrArg A he).trans ((map_smul A _ f).trans hAction.symm)

end RankOne

/-- Complex-place parameters in arbitrary rank and real-place parameters in
rank one, over any number field with compact adele quotient. -/
def CuspidalArchimedeanParameterPartialStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)],
    (∀ (r : ℕ) (T : CuspidalOperatorRealization F r) (v : {v : InfinitePlace F // v.IsComplex}),
      ∃ ds, T.realization.HasComplexPlaceParameter v ds) ∧
    (∀ (T : CuspidalOperatorRealization F 0) (v : {v : InfinitePlace F // v.IsReal}),
      ∃ c : RealCharacterData, T.realization.HasRealPlaceParameter v [RealBlock.character c])

theorem cuspidalArchimedeanParameterPartial :
    CuspidalArchimedeanParameterPartialStatement.{u} :=
  fun _ _ _ _ => ⟨fun _ T v => exists_cuspidalComplexPlaceParameter T v,
    fun T v => exists_rankOne_realPlaceParameter T.realization T.irreducible v⟩

end Langlands.Global
