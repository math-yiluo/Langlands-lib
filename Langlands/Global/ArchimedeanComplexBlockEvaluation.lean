import Langlands.Global.ArchimedeanCompactBlockEvaluation
import Langlands.Global.ArchimedeanBlockCompactLevi
import Langlands.Representation.Archimedean.BlockPrincipalSeriesNormalization
import Langlands.Representation.Archimedean.ComplexPartialJacquet
import Langlands.Representation.Archimedean.PrincipalSeriesAdmissible
import Langlands.Representation.Archimedean.RealLeviSlices
import Langlands.Representation.Archimedean.UnitaryCompactAdmissibility

/-! # Compact block tensor evaluations of the original-order complex standard module -/

noncomputable section

open scoped BigOperators Matrix.Norms.Operator TensorProduct

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.ArchimedeanCompactBlocks

open _root_.Langlands.Archimedean
open LocalFactor.Archimedean
open Archimedean.RealLeviChart (pos val_pos start)
open Archimedean.RealLeviSlices (start_zero' start_succ')
open Archimedean.ComplexGramFormula (phaseUnit norm_phaseUnit)
open Archimedean.ComplexPrincipalSeriesExtension (phaseMatrix)
open AdelicBlockScalarSections (indexedEvaluation)
open Langlands.GeneralLinear

local notation "G" => Langlands.GeneralLinear
local notation "K" => unitaryCompact ℂ
local notation "U" => (fun n => Matrix.unitaryGroup (Fin n) ℂ)
local notation "V" => (fun n d => kFiniteFunctions (complexStandardModule n d) (K n))

private theorem positionCharacter_append_left (xs ys : List ComplexCharacterData)
    (a : ℕ) (ha : a < xs.length) :
    complexPositionCharacter (xs ++ ys) a = complexPositionCharacter xs a := by
  induction xs generalizing a with
  | nil => simp at ha
  | cons d xs ih =>
      cases a with
      | zero => rfl
      | succ a => exact ih a (Nat.lt_of_succ_lt_succ ha)

private theorem positionCharacter_append_right (xs ys : List ComplexCharacterData) (a : ℕ) :
    complexPositionCharacter (xs ++ ys) (xs.length + a) = complexPositionCharacter ys a := by
  induction xs with
  | nil => simp
  | cons d xs ih =>
      simpa only [List.cons_append, List.length_cons, Nat.succ_add, complexPositionCharacter] using ih

private theorem positionCharacter_flat : ∀ {c : ℕ}
    (ds : Fin c → List ComplexCharacterData) (i : Fin c) (a : Fin (ds i).length),
    complexPositionCharacter (List.ofFn ds).flatten (pos (fun j => (ds j).length) i a) =
      complexPositionCharacter (ds i) a
  | 0, _, i, _ => i.elim0
  | c + 1, ds, i, a => by
      rw [List.ofFn_succ, List.flatten_cons, val_pos]
      revert a
      induction i using Fin.cases with
      | zero =>
          intro a
          rw [Fin.val_zero, start_zero', zero_add]
          exact positionCharacter_append_left _ _ a a.isLt
      | succ i =>
          intro a
          rw [Fin.val_succ, start_succ', add_assoc, positionCharacter_append_right]
          rw [← val_pos (fun j : Fin c => (ds j.succ).length) i a]
          exact positionCharacter_flat (fun j => ds j.succ) i a

private theorem positionCharacter_one (d : List ComplexCharacterData) (p : ℕ) :
    complexPositionCharacter d p 1 = 1 := by
  induction d generalizing p with
  | nil => rfl
  | cons a d ih =>
      cases p with
      | zero => simp [complexPositionCharacter]
      | succ p => exact ih p

/-- The matrix of a compact element, viewed as a unitary matrix. -/
private def compactToUnitary (n : ℕ) : K n →* U n where
  toFun k := ⟨k.val.val, k.property⟩
  map_one' := rfl
  map_mul' _ _ := rfl

private theorem toUnits_compactToUnitary (n : ℕ) (k : K n) :
    Unitary.toUnits (compactToUnitary n k) = k.val :=
  Units.ext rfl

/-- The complex standard module's compact action in the group of units. -/
abbrev complexCompactAction (n : ℕ) (d : List ComplexCharacterData) :
    Representation ℂ (K n) (V n d) :=
  (complexStandardRep n d).comp (compactToUnitary n)

theorem complexCompactAction_apply (n : ℕ) (d : List ComplexCharacterData)
    (k : K n) (f : V n d) (g : G n ℂ) :
    (complexCompactAction n d k f).val g = f.val (g * k.val) := by
  change (complexStandardRep n d (compactToUnitary n k) f).val g = _
  rw [principalSeriesRep_apply_coe, toUnits_compactToUnitary]
  rfl

private theorem complexCompactAction_isFiniteVector (n : ℕ) (d : List ComplexCharacterData)
    (f : V n d) : FiniteVectors.IsFiniteVector (complexCompactAction n d) f := by
  have : FiniteDimensional ℂ (FiniteVectors.orbitSpan (complexStandardRep n d) f) :=
    (isComplexGKModule_complexStandardModule n d).1 f
  apply Submodule.finiteDimensional_of_le (S₂ := FiniteVectors.orbitSpan (complexStandardRep n d) f)
  apply Submodule.span_le.mpr
  rintro _ ⟨k, rfl⟩
  exact FiniteVectors.action_mem_orbitSpan _ (compactToUnitary n k) f

private def restrictCompact (n : ℕ) (d : List ComplexCharacterData) :
    V n d →ₗ[ℂ] (K n → ℂ) :=
  (LinearMap.funLeft ℂ ℂ (Subtype.val : K n → G n ℂ)).comp (V n d).subtype

private theorem restrictCompact_injective (n : ℕ) (d : List ComplexCharacterData) :
    Function.Injective (restrictCompact n d) := by
  intro f g h
  apply Subtype.ext
  refine PrincipalSeries.eq_of_eqOn_unitaryCompact_of_mem_principalSeries f.2.1 g.2.1 fun k hk => ?_
  exact congrFun h (⟨k, hk⟩ : K n)

variable {c : ℕ} (ds : Fin c → List ComplexCharacterData)
variable (hsize : ∀ i, 0 < (ds i).length)

local notation "sz" => (fun i : Fin c => List.length (ds i))
local notation "N" => (∑ i, sz i)
local notation "dflat" => (List.flatten (List.ofFn ds))

/-- The block shape of the complex lists preserves their original order. -/
abbrev complexBlockShape : BlockShape N := ⟨c, sz, hsize, rfl⟩

local notation "B" => complexBlockShape ds hsize
local notation "J" => compactLeviEmbedding ℂ B

private theorem blockIndex (i : Fin c) (a : Fin (sz i)) : (B).index i a = pos sz i a := by
  simp [complexBlockShape, BlockShape.index, BlockShape.indexEquiv, pos]

private def pad (i : Fin c) (a : Fin (sz i) → ℂˣ) (x : Fin N) : ℂˣ :=
  Pi.mulSingle (M := fun j => Fin (sz j) → ℂˣ) i a (finSigmaFinEquiv.symm x).1
    (finSigmaFinEquiv.symm x).2

private theorem pad_index (i : Fin c) (a : Fin (sz i) → ℂˣ) (l : Fin c) (p : Fin (sz l)) :
    pad ds i a (pos sz l p) = Pi.mulSingle (M := fun j => Fin (sz j) → ℂˣ) i a l p := by
  rw [pad, pos, Equiv.symm_apply_apply]

private theorem leviEmbedding_diagonal_single (i : Fin c) (a : Fin (sz i) → ℂˣ) :
    (B).leviEmbedding ℂ (Pi.mulSingle i (Iwasawa.diagonalUnits a)) =
      Iwasawa.diagonalUnits (pad ds i a) := by
  classical
  apply Units.ext
  refine Matrix.ext fun x y => ?_
  obtain ⟨⟨l, p⟩, rfl⟩ := (B).indexEquiv.surjective x
  obtain ⟨⟨m, q⟩, rfl⟩ := (B).indexEquiv.surjective y
  change (B).leviEmbedding ℂ (Pi.mulSingle i (Iwasawa.diagonalUnits a)) ((B).index l p) ((B).index m q) =
    (Iwasawa.diagonalUnits (pad ds i a)).val ((B).index l p) ((B).index m q)
  rw [Iwasawa.diagonalUnits_val]
  by_cases hlm : l = m
  · subst m
    rw [(B).leviEmbedding_apply_same]
    by_cases hli : l = i
    · subst l
      rw [Pi.mulSingle_eq_same, Iwasawa.diagonalUnits_val]
      by_cases hpq : p = q
      · subst q
        rw [Matrix.diagonal_apply_eq, Matrix.diagonal_apply_eq, blockIndex ds hsize i p,
          pad_index, Pi.mulSingle_eq_same]
      · rw [Matrix.diagonal_apply_ne _ hpq,
          Matrix.diagonal_apply_ne _ (fun h => hpq (((B).index i).injective h))]
    · rw [Pi.mulSingle_eq_of_ne hli]
      change (1 : Matrix (Fin (sz l)) (Fin (sz l)) ℂ) p q = _
      by_cases hpq : p = q
      · subst q
        rw [Matrix.one_apply_eq, Matrix.diagonal_apply_eq, blockIndex ds hsize l p,
          pad_index, Pi.mulSingle_eq_of_ne hli, Pi.one_apply, Units.val_one]
      · rw [Matrix.one_apply_ne hpq,
          Matrix.diagonal_apply_ne _ (fun h => hpq (((B).index l).injective h))]
  · rw [(B).leviEmbedding_apply_ne _ _ _ _ hlm]
    exact (Matrix.diagonal_apply_ne _ (fun h => hlm
      (congrArg Sigma.fst ((B).indexEquiv.injective h)))).symm

private theorem character_pad_phase (i : Fin c) (a : Fin (sz i) → ℂˣ) :
    principalSeriesCharacter ℂ N (complexPositionCharacter dflat) (pad ds i fun p => phaseUnit (a p)) =
      principalSeriesCharacter ℂ (sz i) (complexPositionCharacter (ds i)) (fun p => phaseUnit (a p)) := by
  rw [principalSeriesCharacter_eq_blockProduct sz ℂ _ _ (positionCharacter_flat ds)]
  have hp (l : Fin c) (p : Fin (sz l)) :
      ‖(pad ds i (fun p => phaseUnit (a p)) (pos sz l p) : ℂ)‖ = 1 := by
    rw [pad_index]
    by_cases hli : l = i
    · subst l
      simp only [Pi.mulSingle_eq_same, norm_phaseUnit]
    · simp only [Pi.mulSingle_eq_of_ne hli, Pi.one_apply, Units.val_one, norm_one]
  simp only [hp, one_pow, Complex.ofReal_one, Complex.one_cpow, Finset.prod_const_one, mul_one]
  rw [Finset.prod_eq_single i]
  · congr 1
    funext p
    rw [pad_index, Pi.mulSingle_eq_same]
  · intro l _ hli
    simp only [pad_index, Pi.mulSingle_eq_of_ne hli, Pi.one_apply]
    simp [principalSeriesCharacter, positionCharacter_one]
  · simp

private def compactSingle (i : Fin c) : K (sz i) →* K N :=
  (J).comp (MonoidHom.mulSingle (fun j => ↥(K (sz j))) i)

private theorem compactSingle_val (i : Fin c) (x : K (sz i)) :
    (compactSingle ds hsize i x).val =
      (B).leviEmbedding ℂ (Pi.mulSingle i x.val) := by
  change (B).leviEmbedding ℂ (fun l =>
    (Pi.mulSingle (M := fun p => ↥(K (sz p))) i x l).val) = _
  congr 1
  funext l
  by_cases hli : l = i
  · subst l
    rw [Pi.mulSingle_eq_same, Pi.mulSingle_eq_same]
  · rw [Pi.mulSingle_eq_of_ne hli, Pi.mulSingle_eq_of_ne hli]
    rfl

private theorem continuous_compactSingle_val (i : Fin c) :
    Continuous fun x : K (sz i) => (compactSingle ds hsize i x).val := by
  simp only [compactSingle_val]
  exact ((B).leviEmbeddingContinuous ℂ).continuous.comp
    ((continuous_mulSingle i).comp continuous_subtype_val)

private theorem compactSingle_phase (i : Fin c) (a : Fin (sz i) → ℂˣ) :
    (compactSingle ds hsize i (matrixUnitaryToCompact ℂ (sz i) (phaseMatrix a))).val =
      Iwasawa.diagonalUnits (pad ds i fun p => phaseUnit (a p)) := by
  have hphase : (matrixUnitaryToCompact ℂ (sz i) (phaseMatrix a)).val =
      Iwasawa.diagonalUnits (fun p => phaseUnit (a p)) := Units.ext rfl
  rw [compactSingle_val, hphase, leviEmbedding_diagonal_single]

private def compactSliceValue (i : Fin c) : V N dflat →ₗ[ℂ] (K (sz i) → ℂ) :=
  (LinearMap.funLeft ℂ ℂ (fun x => (compactSingle ds hsize i x).val)).comp (V N dflat).subtype

private theorem compactSliceValue_mem_range (i : Fin c) (w : V N dflat) :
    compactSliceValue ds hsize i w ∈ LinearMap.range (restrictCompact (sz i) (ds i)) := by
  let Q := matrixUnitaryToCompact ℂ (sz i)
  let C := (LinearMap.funLeft ℂ ℂ Q).comp (compactSliceValue ds hsize i)
  let φ := C w
  have hc : Continuous φ := w.2.1.1.continuous.comp
    ((continuous_compactSingle_val ds hsize i).comp (continuous_matrixUnitaryToCompact ℂ (sz i)))
  let O := FiniteVectors.orbitSpan (complexCompactAction N dflat) w
  have : FiniteDimensional ℂ O := complexCompactAction_isFiniteVector N dflat w
  have hf : FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k : U (sz i) => fun x => φ (x * k))) := by
    apply Submodule.finiteDimensional_of_le (S₂ := O.map C)
    apply Submodule.span_le.mpr
    rintro _ ⟨k, rfl⟩
    let k' := compactSingle ds hsize i (Q k)
    refine ⟨complexCompactAction N dflat k' w, FiniteVectors.action_mem_orbitSpan _ _ _, ?_⟩
    funext x
    change (complexCompactAction N dflat k' w).val (compactSingle ds hsize i (Q x)).val =
      w.val (compactSingle ds hsize i (Q (x * k))).val
    rw [complexCompactAction_apply, map_mul Q, map_mul (compactSingle ds hsize i)]
    rfl
  have hφ (a : Fin (sz i) → ℂˣ) (k : U (sz i)) :
      φ (phaseMatrix a * k) =
        principalSeriesCharacter ℂ (sz i) (complexPositionCharacter (ds i)) (fun p => phaseUnit (a p)) *
          φ k := by
    let z := pad ds i (fun p => phaseUnit (a p))
    have ha := w.2.1.2 z (1 : upperUnipotent N ℂ) ((compactSingle ds hsize i (Q k)).val)
    change w.val (compactSingle ds hsize i (Q (phaseMatrix a * k))).val =
      _ * w.val (compactSingle ds hsize i (Q k)).val
    rw [map_mul Q, map_mul (compactSingle ds hsize i)]
    change w.val ((compactSingle ds hsize i (Q (phaseMatrix a))).val *
      (compactSingle ds hsize i (Q k)).val) = _
    rw [show Q (phaseMatrix a) = matrixUnitaryToCompact ℂ (sz i) (phaseMatrix a) from rfl,
      compactSingle_phase]
    simpa only [OneMemClass.coe_one, mul_one, z, character_pad_phase] using ha
  obtain ⟨v, hv, he⟩ := complexPrincipalSeriesExtension (sz i) (ds i) φ hc hf hφ
  refine ⟨⟨v, hv⟩, funext fun x => ?_⟩
  change v x.val = w.val (compactSingle ds hsize i x).val
  have hx : Q (compactToUnitary (sz i) x) = x := Subtype.ext (toUnits_compactToUnitary _ x)
  simpa only [φ, C, compactSliceValue, LinearMap.comp_apply, LinearMap.funLeft_apply,
    Submodule.subtype_apply, hx, toUnits_compactToUnitary]
    using he (compactToUnitary (sz i) x)

/-- The standard function of a block determined by the ambient compact slice
through the identity. -/
def complexBlockSlice (i : Fin c) : V N dflat →ₗ[ℂ] V (sz i) (ds i) :=
  (LinearEquiv.ofInjective (restrictCompact (sz i) (ds i))
    (restrictCompact_injective (sz i) (ds i))).symm.toLinearMap.comp
      ((compactSliceValue ds hsize i).codRestrict _ (compactSliceValue_mem_range ds hsize i))

theorem complexBlockSlice_compact (i : Fin c) (x : K (sz i)) (f : V N dflat) :
    (complexBlockSlice ds hsize i f).val x.val = f.val (compactSingle ds hsize i x).val := by
  let e := LinearEquiv.ofInjective (restrictCompact (sz i) (ds i))
    (restrictCompact_injective (sz i) (ds i))
  let y : LinearMap.range (restrictCompact (sz i) (ds i)) :=
    ⟨compactSliceValue ds hsize i f, compactSliceValue_mem_range ds hsize i f⟩
  exact congrArg (fun z : LinearMap.range (restrictCompact (sz i) (ds i)) => z.val x)
    (e.apply_symm_apply y)

private def valueAtOne : V N dflat →ₗ[ℂ] ℂ :=
  (LinearMap.proj 1).comp (V N dflat).subtype

private theorem blockSlice_valueAtOne (i : Fin c) (x : K (sz i)) (f : V N dflat) :
    restrictCompact (sz i) (ds i) (complexBlockSlice ds hsize i f) x =
      valueAtOne ds (complexCompactAction N dflat ((J) (Pi.mulSingle i x)) f) := by
  change (complexBlockSlice ds hsize i f).val x.val =
    (complexCompactAction N dflat (compactSingle ds hsize i x) f).val 1
  rw [complexBlockSlice_compact, complexCompactAction_apply, one_mul]

/-- The actual complex standard module evaluated as a tensor of the block standard modules. -/
def complexEvaluation (k : K N) : V N dflat →ₗ[ℂ] (⨂[ℂ] i, V (sz i) (ds i)) :=
  evaluation (J) (complexCompactAction N dflat) (valueAtOne ds)
    (fun i => restrictCompact (sz i) (ds i)) (complexBlockSlice ds hsize)
    (blockSlice_valueAtOne ds hsize) (fun i => restrictCompact_injective (sz i) (ds i))
    (complexCompactAction_isFiniteVector N dflat) k

theorem complexEvaluation_value (k : K N) (f : V N dflat) (q : ∀ i, K (sz i)) :
    indexedEvaluation (fun i => restrictCompact (sz i) (ds i)) (complexEvaluation ds hsize k f) q =
      f.val (((J) q).val * k.val) := by
  rw [complexEvaluation, evaluation_value]
  change (complexCompactAction N dflat ((J) q * k) f).val 1 = _
  rw [complexCompactAction_apply, one_mul]
  rfl

theorem complexEvaluation_right (k h : K N) (f : V N dflat) :
    complexEvaluation ds hsize k (complexCompactAction N dflat h f) =
      complexEvaluation ds hsize (k * h) f := by
  apply evaluation_right

theorem complexEvaluation_left (q : ∀ i, K (sz i)) (k : K N) (f : V N dflat) :
    complexEvaluation ds hsize ((J) q * k) f =
      PiTensorProduct.map (fun i => complexCompactAction (sz i) (ds i) (q i))
        (complexEvaluation ds hsize k f) := by
  apply evaluation_left
  intro i p t f'
  exact complexCompactAction_apply (sz i) (ds i) p f' t.val

theorem complexEvaluation_separates (f : V N dflat)
    (hf : ∀ k, complexEvaluation ds hsize k f = 0) : f = 0 := by
  apply Subtype.ext
  apply PrincipalSeries.eq_zero_of_mem_principalSeries_of_eqOn_unitaryCompact f.2.1
  intro g hg
  have h := complexEvaluation_value ds hsize ⟨g, hg⟩ f 1
  simpa only [hf, map_zero, Pi.zero_apply, Submonoid.coe_one, map_one, one_mul] using h.symm

end Langlands.Global.ArchimedeanCompactBlocks
