import Langlands.Automorphic.CuspidalCoefficientProbes
import Langlands.Global.AdelicBlockParabolicPlaceCompact
import Langlands.Global.CompactJacquetBlockEvaluation

/-! # Standard tensors from compact cuspidal block evaluations -/

noncomputable section

open scoped BigOperators TensorProduct Manifold ContDiff Matrix.Norms.Operator

namespace Langlands.Global

open Langlands.GeneralLinear Langlands.Automorphic Langlands.Archimedean
open Langlands.LocalFactor.Archimedean

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 100000

attribute [local instance 100] LieRing.ofAssociativeRing

universe u uR uV uW uI uP

section CompactCovariance

variable {R : Type uR} [RCLike R] {n : ℕ} {B : BlockShape n}
  {W : Type uW} [AddCommGroup W] [Module ℂ W]
  {V : Fin B.length → Type uV} [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]

/-- Evaluation at a point with trivial coordinate at the chosen place commutes
with the compact block Levi action. -/
def IsBlockCompactEvaluation
    (κ : Representation ℂ (Matrix.unitaryGroup (Fin n) R) W)
    (ρ : ∀ i : Fin B.length, Representation ℂ (Matrix.unitaryGroup (Fin (B.size i)) R) (V i))
    (ev : W →ₗ[ℂ] (⨂[ℂ] i, V i)) : Prop :=
  ∀ (k : B.CompactLevi R) (w : W),
    ev (κ (B.compactLeviEmbedding R k) w) = PiTensorProduct.map (fun i => ρ i (k i)) (ev w)

variable {κ : Representation ℂ (Matrix.unitaryGroup (Fin n) R) W}
  {ρ : ∀ i : Fin B.length, Representation ℂ (Matrix.unitaryGroup (Fin (B.size i)) R) (V i)}

theorem IsBlockCompactEvaluation.apply_single
    {ev : W →ₗ[ℂ] (⨂[ℂ] i, V i)} (h : IsBlockCompactEvaluation (B := B) κ ρ ev)
    (i : Fin B.length) (k : Matrix.unitaryGroup (Fin (B.size i)) R) (w : W) :
    ev (κ (B.compactLeviEmbedding R (Pi.mulSingle i k)) w) =
      PiTensorProduct.map (Function.update (fun _ => LinearMap.id) i (ρ i k)) (ev w) := by
  rw [h]
  congr 2
  funext j
  by_cases hj : j = i
  · subst j
    simp
  · simp [hj, Module.End.one_eq_id]

private theorem separates_compactEvaluations
    {I : Type uI} {P : Type uP}
    (ev : I → W →ₗ[ℂ] (⨂[ℂ] i, V i))
    (hEvK : ∀ y, IsBlockCompactEvaluation (B := B) κ ρ (ev y))
    (test : P → (⨂[ℂ] i, V i) →ₗ[ℂ] ℂ)
    (hTest : ∀ z, (∀ p (k : B.CompactLevi R),
      test p (PiTensorProduct.map (fun i => ρ i (k i)) z) = 0) → z = 0)
    (hSep : ∀ w, (∀ y k, ev y (κ k w) = 0) → w = 0)
    (w : W) (hw : ∀ (a : I × P) k, ((test a.2).comp (ev a.1)) (κ k w) = 0) :
    w = 0 := by
  apply hSep w
  intro y k
  apply hTest
  intro p l
  rw [← hEvK y l, ← Module.End.mul_apply, ← map_mul]
  exact hw (y, p) (B.compactLeviEmbedding R l * k)

end CompactCovariance

variable {F : Type u} [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]
  {c n : ℕ} {m : Fin c → ℕ} (T : ∀ i, CuspidalOperatorRealization F (m i))
  {W : Type uW} [AddCommGroup W] [Module ℂ W] {I : Type uI}

local instance (n : ℕ) : AddCommGroup (RationalInvariantFunctions F n) := Submodule.addCommGroup _
local instance (n : ℕ) : AddCommGroup (ContinuousRationalFunctions F n) := Submodule.addCommGroup _
local instance (n : ℕ) : AddCommGroup (FiniteSmoothRationalFunctions F n) := Submodule.addCommGroup _
local instance (n : ℕ) : AddCommGroup (AutomorphicForms F n) := Submodule.addCommGroup _
local instance (n : ℕ) : AddCommGroup (StableAutomorphicFunctions F n) := Submodule.addCommGroup _
local instance {n : ℕ} (S : OperatorRealization F n) : AddCommGroup S.Space :=
  Submodule.addCommGroup _

private abbrev cuspidalCoefficientTensor := PiTensorProduct ℂ (fun i => ↥((T i).Space))
local notation "E" => cuspidalCoefficientTensor T
private abbrev cuspidalBlockShape (hm : ∑ i, (m i + 1) = n) : BlockShape n :=
  ⟨c, fun i => m i + 1, fun _ => Nat.succ_pos _, hm⟩

section Real

open RealLeviSlices RealBlockPosition

variable (v : {w : NumberField.InfinitePlace F // w.IsReal}) (ds : Fin c → List RealBlock)

local notation "RK" => Matrix.unitaryGroup (Fin n) ℝ
local notation "RM" => Matrix (Fin n) (Fin n) ℝ

private abbrev realProbeParameters := ∀ i, Module.Dual ℂ ((T i).realStandardMultiplicity v (ds i))

/-- Apply the real place Lie action in one cuspidal coefficient slot. -/
abbrev realCuspidalBlockLie (i : Fin c) (X : Matrix (Fin (m i + 1)) (Fin (m i + 1)) ℝ) :
    Module.End ℂ E :=
  PiTensorProduct.map (Function.update (fun _ => LinearMap.id) i
    ((T i).realization.realPlaceLieAction v (1 ⊗ₜ X)))

private theorem hasRealCompactBlockSlices_of_compactLevi
    {s : Fin c → ℕ} (hs : ∀ i, 0 < s i) (heq : s = sz ds) (hn : ∑ i, s i = ∑ i, sz ds i)
    {κ : Representation ℂ (Matrix.unitaryGroup (Fin (∑ i, sz ds i)) ℝ) W}
    (probe : W →ₗ[ℂ] ℂ)
    (hslice : ∀ (i : Fin c) (w : W), ∃ f ∈ realStandardModule (s i) (ds i),
      ∀ k : Matrix.unitaryGroup (Fin (s i)) ℝ,
        probe (κ ((⟨c, s, hs, hn⟩ : BlockShape (∑ j, sz ds j)).compactLeviEmbedding ℝ
          (Pi.mulSingle i k)) w) = f (Unitary.toUnits k)) :
    HasRealCompactBlockSlices ds κ probe := by
  subst s
  intro i w
  obtain ⟨f, hf, hk⟩ := hslice i w
  refine ⟨f, hf, fun k => ?_⟩
  rw [← BlockShape.compactLeviEmbedding_real_single (sz ds) hs i k]
  exact hk k

set_option maxHeartbeats 800000 in
/-- Normalized block evaluations with actual real cuspidal coefficients embed the
source into the standard module of the ordered concatenation tensored with a scalar
multiplicity space. -/
theorem exists_realStandardTensor_of_cuspidalBlockEvaluations
    (hm : ∑ i, (m i + 1) = n) (hp : ∀ i, (T i).realization.HasRealPlaceParameter v (ds i))
    {κ : Representation ℂ RK W} {π : (ℂ ⊗[ℝ] RM) →ₗ⁅ℂ⁆ Module.End ℂ W}
    (hgk : IsRealGKModule n κ π) (ev : I → W →ₗ[ℂ] E)
    (hEvK : ∀ y, IsBlockCompactEvaluation (B := cuspidalBlockShape hm) κ
      (fun i => (T i).realization.realPlaceCompactRepresentation v) (ev y))
    (hEvL : ∀ y, IsNormalizedBlockLieEvaluation (cuspidalBlockShape hm) π
      (realCuspidalBlockLie T v) (ev y))
    (hsep : ∀ w, (∀ y k, ev y (κ k w) = 0) → w = 0) :
    ∃ e : W →ₗ[ℂ] realStandardKFinite n (flat ds) ⊗[ℂ] (I × realProbeParameters T v ds → ℂ),
      Function.Injective e ∧
      (∀ k w, e (κ k w) = TensorProduct.map (realStandardRep n (flat ds) k) LinearMap.id (e w)) ∧
      ∀ (X : RM) w, e (π (1 ⊗ₜ X) w) =
        TensorProduct.map (realStandardLie n (flat ds) (1 ⊗ₜ X)) LinearMap.id (e w) := by
  have hs : (fun i => m i + 1) = sz ds := funext fun i => (hp i).1.symm
  have hn : n = ∑ i, sz ds i := by
    rw [← hm]
    exact congrArg (fun s : Fin c → ℕ => ∑ i, s i) hs
  subst hn
  let B := cuspidalBlockShape hm
  let test : realProbeParameters T v ds → Module.Dual ℂ E :=
    CuspidalOperatorRealization.realCoefficientProbe T v ds hp
  let probe (a : I × realProbeParameters T v ds) : W →ₗ[ℂ] ℂ := (test a.2).comp (ev a.1)
  refine exists_realStandardTensor_of_compactJacquet ds hgk probe ?_ ?_ ?_
  · rintro ⟨y, μ⟩
    refine isRealJacquetFunctional_of_normalizedBlockEvaluation B ds (fun i => (hp i).1)
      κ π (realCuspidalBlockLie T v) (ev y) (hEvL y) (test μ) ?_ ?_ ?_
    · intro i X hX z
      exact (CuspidalOperatorRealization.realCoefficientProbe_jacquet T v ds hp μ i z).1 X hX
    · intro i a z
      exact ((CuspidalOperatorRealization.realCoefficientProbe_jacquet T v ds hp μ i z).2 a).1
    · intro i a w
      rw [← B.compactLeviEmbedding_signReflection i a, (hEvK y).apply_single]
      exact ((CuspidalOperatorRealization.realCoefficientProbe_jacquet T v ds hp μ i (ev y w)).2 a).2
  · rintro ⟨y, μ⟩
    apply hasRealCompactBlockSlices_of_compactLevi ds (fun i => Nat.succ_pos (m i)) hs hm
    intro i w
    obtain ⟨f, _, hfK, _⟩ :=
      CuspidalOperatorRealization.realCoefficientProbe_slice T v ds hp μ i (ev y w)
    refine ⟨f.val, f.property.1, fun k => ?_⟩
    change test μ (ev y (κ (B.compactLeviEmbedding ℝ (Pi.mulSingle i k)) w)) = _
    rw [(hEvK y).apply_single]
    exact hfK k
  · exact separates_compactEvaluations (B := B) (κ := κ) (V := fun i => ↥((T i).Space))
      (ρ := fun i => (T i).realization.realPlaceCompactRepresentation v) ev hEvK test
      (CuspidalOperatorRealization.realCoefficientProbe_separates T v ds hp) hsep

end Real

section Complex

open RealLeviChart RealLeviSlices

private theorem length_flatten_ofFn {α : Type*} :
    ∀ {c : ℕ} (ds : Fin c → List α), (List.ofFn ds).flatten.length = ∑ i, (ds i).length
  | 0, _ => by simp
  | c + 1, ds => by
    rw [List.ofFn_succ, List.flatten_cons, List.length_append, length_flatten_ofFn, Fin.sum_univ_succ]

private theorem getElem?_flatten_ofFn {α : Type*} :
    ∀ {c : ℕ} (ds : Fin c → List α) (i : Fin c) (a : ℕ), a < (ds i).length →
      (List.ofFn ds).flatten[start (fun j => (ds j).length) i + a]? = (ds i)[a]?
  | 0, _, i, _, _ => i.elim0
  | c + 1, ds, i, a, ha => by
    rw [List.ofFn_succ, List.flatten_cons]
    induction i using Fin.cases with
    | zero =>
      rw [Fin.val_zero, start_zero', zero_add, List.getElem?_append_left ha]
    | succ i =>
      rw [Fin.val_succ, start_succ', add_assoc,
        List.getElem?_append_right (by omega), Nat.add_sub_cancel_left]
      exact getElem?_flatten_ofFn (fun j => ds j.succ) i a ha

private theorem get_flatten_ofFn_index {α : Type*} (B : BlockShape n)
    (ds : Fin B.length → List α) (hs : ∀ i, (ds i).length = B.size i)
    (hn : (List.ofFn ds).flatten.length = n) (i : Fin B.length) (a : Fin (B.size i)) :
    (List.ofFn ds).flatten.get (Fin.cast hn.symm (B.index i a)) =
      (ds i).get (Fin.cast (hs i).symm a) := by
  have hsize : B.size = fun j => (ds j).length := funext fun j => (hs j).symm
  have ha : (a : ℕ) < (ds i).length := (hs i).symm ▸ a.isLt
  have hpos : (B.index i a : ℕ) = start B.size i + a := val_pos B.size i a
  have hidx := getElem?_flatten_ofFn ds i a ha
  rw [← congrArg (fun s => start s i) hsize, ← hpos] at hidx
  have hb : (B.index i a : ℕ) < (List.ofFn ds).flatten.length :=
    hn.symm ▸ (B.index i a).isLt
  rw [List.getElem?_eq_getElem hb, List.getElem?_eq_getElem ha, Option.some_inj] at hidx
  exact hidx

private theorem kappa_one (ds : List ComplexCharacterData) (hn : ds.length = n)
    (a : Fin n) :
    ComplexSwapJacquet.kappa ds hn a 1 =
      complexShiftedExponent (fun j => ds.get (Fin.cast hn.symm j)) a := by
  have ha : (a : ℕ) < ds.length := hn.symm ▸ a.isLt
  rw [ComplexSwapJacquet.kappa_eq, ComplexSwapJacquet.posExponent_eq_get _ _ ha]
  simp [complexShiftedExponent]
  ring

private theorem kappa_I (ds : List ComplexCharacterData) (hn : ds.length = n)
    (a : Fin n) :
    ComplexSwapJacquet.kappa ds hn a Complex.I =
      Complex.I * ((ds.get (Fin.cast hn.symm a)).weight : ℂ) := by
  have ha : (a : ℕ) < ds.length := hn.symm ▸ a.isLt
  rw [ComplexSwapJacquet.kappa_eq, ComplexSwapJacquet.posWeight_eq_get _ _ ha]
  simp [mul_comm]

variable (v : {w : NumberField.InfinitePlace F // w.IsComplex})
  (ds : Fin c → List ComplexCharacterData)

local notation "CK" => Matrix.unitaryGroup (Fin n) ℂ
local notation "CM" => Matrix (Fin n) (Fin n) ℂ

private abbrev complexProbeParameters := ∀ i, Module.Dual ℂ ((T i).complexStandardMultiplicity v (ds i))

/-- Apply the complex place Lie action in one cuspidal coefficient slot. -/
abbrev complexCuspidalBlockLie (i : Fin c) (X : Matrix (Fin (m i + 1)) (Fin (m i + 1)) ℂ) :
    Module.End ℂ E :=
  PiTensorProduct.map (Function.update (fun _ => LinearMap.id) i
    ((T i).realization.complexPlaceLieAction v (1 ⊗ₜ X)))

set_option maxHeartbeats 800000 in
/-- Normalized block evaluations with actual complex cuspidal coefficients embed
the source into the standard module of the ordered character concatenation
tensored with a scalar multiplicity space. -/
theorem exists_complexStandardTensor_of_cuspidalBlockEvaluations
    (hm : ∑ i, (m i + 1) = n) (hp : ∀ i, (T i).realization.HasComplexPlaceParameter v (ds i))
    {κ : Representation ℂ CK W} {π : (ℂ ⊗[ℝ] CM) →ₗ⁅ℂ⁆ Module.End ℂ W}
    (hgk : IsComplexGKModule n κ π) (ev : I → W →ₗ[ℂ] E)
    (hEvK : ∀ y, IsBlockCompactEvaluation (B := cuspidalBlockShape hm) κ
      (fun i => (T i).realization.complexPlaceCompactRepresentation v) (ev y))
    (hEvL : ∀ y, IsNormalizedBlockLieEvaluation (cuspidalBlockShape hm) π
      (complexCuspidalBlockLie T v) (ev y))
    (hsep : ∀ w, (∀ y k, ev y (κ k w) = 0) → w = 0) :
    ∃ e : W →ₗ[ℂ] complexStandardKFinite n (List.ofFn ds).flatten ⊗[ℂ]
          (I × complexProbeParameters T v ds → ℂ), Function.Injective e ∧
      (∀ k w, e (κ k w) = TensorProduct.map
        (complexStandardRep n (List.ofFn ds).flatten k) LinearMap.id (e w)) ∧
      ∀ (X : CM) w, e (π (1 ⊗ₜ X) w) = TensorProduct.map
        (complexStandardLie n (List.ofFn ds).flatten (1 ⊗ₜ X)) LinearMap.id (e w) := by
  let B := cuspidalBlockShape hm
  let D := (List.ofFn ds).flatten
  have hD : D.length = n := by
    rw [show D.length = ∑ i, (ds i).length from length_flatten_ofFn ds, ← hm]
    exact Finset.sum_congr rfl (fun i _ => (hp i).1)
  let d (j : Fin n) := D.get (Fin.cast hD.symm j)
  have hd (i : Fin c) (a : Fin (m i + 1)) :
      d (B.index i a) = (ds i).get (Fin.cast (hp i).1.symm a) :=
    get_flatten_ofFn_index B ds (fun i => (hp i).1) hD i a
  have hList : List.ofFn d = D := by
    subst hD
    exact List.ofFn_get D
  change ∃ e : W →ₗ[ℂ] complexStandardKFinite n D ⊗[ℂ] (I × complexProbeParameters T v ds → ℂ),
    Function.Injective e ∧
    (∀ k w, e (κ k w) = TensorProduct.map (complexStandardRep n D k) LinearMap.id (e w)) ∧
    ∀ (X : CM) w, e (π (1 ⊗ₜ X) w) =
      TensorProduct.map (complexStandardLie n D (1 ⊗ₜ X)) LinearMap.id (e w)
  rw [← hList]
  let test : complexProbeParameters T v ds → Module.Dual ℂ E :=
    CuspidalOperatorRealization.complexCoefficientProbe T v ds hp
  let probe (a : I × complexProbeParameters T v ds) : W →ₗ[ℂ] ℂ := (test a.2).comp (ev a.1)
  refine exists_complexStandardTensor_of_compactJacquet d hgk probe ?_ ?_
  · rintro ⟨y, μ⟩
    refine isComplexJacquetFunctional_of_normalizedBlockEvaluation B hd π
      (complexCuspidalBlockLie T v) (ev y) (hEvL y) (test μ) ?_ ?_ ?_
    · intro i X hX z
      exact (CuspidalOperatorRealization.complexCoefficientProbe_jacquet T v ds hp μ i z).1 X hX
    · intro i a z
      rw [← kappa_one (ds i) (hp i).1 a]
      exact (CuspidalOperatorRealization.complexCoefficientProbe_jacquet T v ds hp μ i z).2 a 1
    · intro i a z
      rw [← kappa_I (ds i) (hp i).1 a]
      exact (CuspidalOperatorRealization.complexCoefficientProbe_jacquet T v ds hp μ i z).2 a Complex.I
  · exact separates_compactEvaluations (B := B) (κ := κ) (V := fun i => ↥((T i).Space))
      (ρ := fun i => (T i).realization.complexPlaceCompactRepresentation v) ev hEvK test
      (CuspidalOperatorRealization.complexCoefficientProbe_separates T v ds hp) hsep

end Complex

end Langlands.Global
