import Langlands.Global.AdelicBlockDeterminantCharacter
import Langlands.Global.CompletionResidueAdic
import Langlands.Global.FiniteAdelicGL.PadicComparison
import Langlands.Group.GL.BlockModulus

/-!
# The finite-place normalization of adelic block induction

The identity-supported inclusion of a finite local parabolic respects its Levi
projection and the positive half character defining normalized induction.
-/

noncomputable section

open scoped NNReal WithZero

set_option autoImplicit false

universe u

namespace Langlands.Global.CompletionPadic

open IsDedekindDomain

private theorem discreteValuation_eq_of_isEquiv {K : Type*} [Field K]
    (v w : Valuation K ℤᵐ⁰) (he : v.IsEquiv w)
    (hv : Function.Surjective v) (hw : Function.Surjective w) : v = w := by
  have hstep (a : ℤᵐ⁰) : a < 1 ↔ a ≤ WithZero.exp (-1) := by
    simpa [← WithZero.exp_add] using
      (WithZero.lt_mul_exp_iff_le (x := a) (y := WithZero.exp (-1)) WithZero.exp_ne_zero)
  have hlt : WithZero.exp (-1) < (1 : ℤᵐ⁰) := by norm_num
  obtain ⟨x, hx⟩ := hv (WithZero.exp (-1))
  have hxw : w x = WithZero.exp (-1) := by
    refine le_antisymm ((hstep _).mp (he.lt_one_iff_lt_one.mp (hx ▸ hlt))) ?_
    by_contra! hn
    obtain ⟨y, hy⟩ := hw (WithZero.exp (-1))
    have hxy : v x < v y := (Valuation.isEquiv_iff_val_lt_val.mp he).mpr (hy ▸ hn)
    have hy' : v y ≤ WithZero.exp (-1) :=
      (hstep _).mp (he.lt_one_iff_lt_one.mpr (hy ▸ hlt))
    exact (not_lt_of_ge hy') (hx ▸ hxy)
  ext z
  by_cases hz : z = 0
  · simp [hz]
  let k := -WithZero.log (v z)
  have hp : v (x ^ k) = v z := by
    rw [map_zpow₀, hx, ← WithZero.exp_zsmul, zsmul_eq_mul, mul_neg_one]
    simpa [k] using WithZero.exp_log (v.ne_zero_iff.mpr hz)
  calc
    v z = v (x ^ k) := hp.symm
    _ = w (x ^ k) := by rw [map_zpow₀, map_zpow₀, hx, hxw]
    _ = w z := he.eq_iff.mp hp

variable {F : Type u} [Field F] [NumberField F] (v : FinitePlace F)

/-- The discrete valuation of the canonical p-adic object is the completion valuation. -/
theorem valued_eq_canonicalDiscreteValuation :
    (Valued.v : Valuation (FiniteCompletion F v) ℤᵐ⁰) =
      (padicField v).canonicalTopologicalData.discreteValuation := by
  let T := (padicField v).canonicalTopologicalData
  apply discreteValuation_eq_of_isEquiv _ _ ?_
    (HeightOneSpectrum.valuedAdicCompletion_surjective F v) T.discreteValuation_surjective
  apply Valuation.isEquiv_iff_val_le_one.mpr
  intro x
  have he := (topologicalData_vle v x 1).symm
  rw [map_one] at he
  refine he.trans ?_
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let e := IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt (padicField v).Carrier
  change x ≤ᵥ 1 ↔ e (ValuativeRel.valuation (padicField v).Carrier x) ≤ 1
  rw [← map_one e, e.strictMono.le_iff_le]
  exact (ValuativeRel.valuation (padicField v).Carrier).vle_one_iff

/-- The canonical p-adic object uses the same residue cardinality as the completion. -/
theorem canonicalResidueCardinality_eq_absNorm :
    (padicField v).canonicalTopologicalData.residueCardinality = Ideal.absNorm v.asIdeal := by
  let T := (padicField v).canonicalTopologicalData
  have h : T.Integers = (v.adicCompletionIntegers F).toSubring := by
    ext x
    exact (T.canonicalNorm_le_one_iff_mem_integers x).symm.trans
      (mem_adicCompletionIntegers_iff v x).symm
  let e : T.Integers ≃+* v.adicCompletionIntegers F := RingEquiv.subringCongr h
  exact (Nat.card_congr (IsLocalRing.ResidueField.mapEquiv e).toEquiv).trans
    (CompletionResidue.card_adicResidueField F v)

/-- The canonical normalized p-adic absolute value is the actual completion norm. -/
theorem norm_eq_canonicalNormalizedAbs (x : FiniteCompletion F v) :
    ‖x‖ = (padicField v).canonicalTopologicalData.normalizedAbs x := by
  let T := (padicField v).canonicalTopologicalData
  by_cases hx : x = 0
  · rw [hx, norm_zero, T.normalizedAbs_zero]
  have hvx : Valued.v x ≠ 0 := Valuation.ne_zero_iff _ |>.mpr hx
  have hlog : WithZero.log (Valued.v x) = (WithZero.unzero hvx).toAdd :=
    congrArg WithZero.log (WithZero.coe_unzero hvx).symm
  rw [NumberField.FinitePlace.norm_def, WithZeroMulInt.toNNReal_neg_apply _ hvx,
    NNReal.coe_zpow, NNReal.coe_natCast, T.normalizedAbs_of_ne_zero hx,
    canonicalResidueCardinality_eq_absNorm v, PadicField.TopologicalData.ord,
    ← valued_eq_canonicalDiscreteValuation v, neg_neg]

end Langlands.Global.CompletionPadic

namespace Langlands.Global.AdelicBlockParabolic

open Langlands.GeneralLinear

variable (F : Type u) [Field F] [NumberField F] {n : ℕ} (B : BlockShape n)
  (v : FinitePlace F)

/-- Insert an actual local Levi at one finite place by embedding every diagonal block. -/
def finitePlaceLeviInclusion : B.Levi (FiniteCompletion F v) →ₜ* FullLevi F B where
  toFun m i := AdelicGL.ofFinite F (B.size i) (FiniteAdelicGL.localInclusion F (B.size i) v (m i))
  map_one' := funext fun i => by simp
  map_mul' m m' := funext fun i => by simp
  continuous_toFun := continuous_pi fun i =>
    (AdelicGL.ofFinite F (B.size i)).continuous.comp
      ((FiniteAdelicGL.localInclusion F (B.size i) v).continuous.comp (continuous_apply i))

@[simp]
theorem finitePlaceLeviInclusion_apply (m : B.Levi (FiniteCompletion F v)) (i : Fin B.length) :
    finitePlaceLeviInclusion F B v m i =
      AdelicGL.ofFinite F (B.size i) (FiniteAdelicGL.localInclusion F (B.size i) v (m i)) := rfl

private theorem localInclusion_mem_parabolic (p : B.parabolic (FiniteCompletion F v)) :
    FiniteAdelicGL.localInclusion F n v p.val ∈ B.parabolic (FiniteAdeles F) := by
  apply (B.mem_parabolic_iff _ _).mpr
  intro i j a b hij
  refine IsDedekindDomain.FiniteAdeleRing.ext _ fun w => ?_
  change FiniteAdelicGL.localProjection F n w
    (FiniteAdelicGL.localInclusion F n v p.val) (B.index i a) (B.index j b) = 0
  by_cases hw : w = v
  · subst w
    rw [FiniteAdelicGL.localProjection_localInclusion]
    exact (B.mem_parabolic_iff _ _).mp p.property i j a b hij
  · rw [FiniteAdelicGL.localProjection_localInclusion_of_ne F n v w hw]
    exact Matrix.one_apply_ne (fun h => hij.ne ((congrArg Sigma.fst (B.indexEquiv.injective h)).symm))

/-- Insert a local parabolic matrix with identity at every other place. -/
def finitePlaceParabolicInclusion : B.parabolic (FiniteCompletion F v) →ₜ* Full F B :=
  (ofFinite F B).comp
    { toFun p := ⟨FiniteAdelicGL.localInclusion F n v p.val, localInclusion_mem_parabolic F B v p⟩
      map_one' := Subtype.ext ((FiniteAdelicGL.localInclusion F n v).map_one)
      map_mul' p q := Subtype.ext ((FiniteAdelicGL.localInclusion F n v).map_mul p.val q.val)
      continuous_toFun := ((FiniteAdelicGL.localInclusion F n v).continuous.comp
        continuous_subtype_val).subtype_mk _ }

@[simp]
theorem finitePlaceParabolicInclusion_val (p : B.parabolic (FiniteCompletion F v)) :
    (finitePlaceParabolicInclusion F B v p).val =
      AdelicGL.ofFinite F n (FiniteAdelicGL.localInclusion F n v p.val) := rfl

@[simp]
theorem leviProjection_finitePlaceParabolicInclusion (p : B.parabolic (FiniteCompletion F v)) :
    B.leviProjection (Adeles F) (finitePlaceParabolicInclusion F B v p) =
      finitePlaceLeviInclusion F B v (B.leviProjection (FiniteCompletion F v) p) := by
  funext i
  apply Units.ext
  ext a b
  rw [B.leviProjection_apply, finitePlaceParabolicInclusion_val, finitePlaceLeviInclusion_apply]
  apply Prod.ext
  · change (1 : GeneralLinear n (InfiniteAdeles F)) (B.index i a) (B.index i b) =
      (1 : GeneralLinear (B.size i) (InfiniteAdeles F)) a b
    simp [Matrix.one_apply]
  · apply IsDedekindDomain.FiniteAdeleRing.ext
    intro w
    change FiniteAdelicGL.localProjection F n w (FiniteAdelicGL.localInclusion F n v p.val)
        (B.index i a) (B.index i b) =
      FiniteAdelicGL.localProjection F (B.size i) w (FiniteAdelicGL.localInclusion F (B.size i) v
        (B.leviProjection (FiniteCompletion F v) p i)) a b
    by_cases hw : w = v
    · subst w
      simp
    · rw [FiniteAdelicGL.localProjection_localInclusion_of_ne F n v w hw,
        FiniteAdelicGL.localProjection_localInclusion_of_ne F (B.size i) v w hw]
      simp [Matrix.one_apply]

end Langlands.Global.AdelicBlockParabolic

namespace Langlands.Global.AdelicBlockDeterminantCharacter

open Langlands.GeneralLinear AdelicBlockParabolic CompletionPadic

variable (F : Type u) [Field F] [NumberField F] {n : ℕ}

/-- The full determinant norm restricts to the canonical p-adic determinant norm. -/
theorem determinantNorm_finitePlaceInclusion (v : FinitePlace F)
    (g : FiniteLocalGL F n v) :
    determinantNorm F n (AdelicGL.ofFinite F n (FiniteAdelicGL.localInclusion F n v g)) =
      (padicField v).canonicalTopologicalData.determinantNorm n g := by
  apply Units.ext
  apply NNReal.eq
  rw [coe_determinantNorm_localInclusion, PadicField.TopologicalData.determinantNorm_coe]
  exact norm_eq_canonicalNormalizedAbs v (Matrix.GeneralLinearGroup.det g).val

variable (B : BlockShape n) (v : FinitePlace F)

/-- The adelic pairwise determinant character restricts to the canonical local modulus. -/
theorem leviCharacter_finitePlaceLeviInclusion (m : B.Levi (FiniteCompletion F v)) :
    leviCharacter F B (finitePlaceLeviInclusion F B v m) =
      (padicField v).canonicalTopologicalData.leviModulus B m := by
  rw [leviCharacter_apply, PadicField.TopologicalData.leviModulus_apply]
  simp only [finitePlaceLeviInclusion_apply, determinantNorm_finitePlaceInclusion]

/-- The positive half in adelic covariance restricts to the one in local normalized induction. -/
theorem parabolicHalfCharacter_finitePlaceParabolicInclusion
    (p : B.parabolic (FiniteCompletion F v)) :
    parabolicHalfCharacter F B (finitePlaceParabolicInclusion F B v p) =
      (padicField v).canonicalTopologicalData.parabolicHalfModulus B p := by
  apply Units.ext
  change (leviHalfCharacter F B
    (B.leviProjection (Adeles F) (finitePlaceParabolicInclusion F B v p)) : ℂ) =
    ((padicField v).canonicalTopologicalData.leviHalfModulus B
      (B.leviProjection (FiniteCompletion F v) p) : ℂ)
  rw [coe_leviHalfCharacter, PadicField.TopologicalData.leviHalfModulus_apply,
    leviProjection_finitePlaceParabolicInclusion, leviCharacter_finitePlaceLeviInclusion]

end Langlands.Global.AdelicBlockDeterminantCharacter
