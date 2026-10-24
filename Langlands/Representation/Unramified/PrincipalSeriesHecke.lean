import Langlands.Representation.Unramified.StandardHeckeSum
import Langlands.Representation.Unramified.PrincipalSeries
import Langlands.Group.GL.SingletonBlocks
import Langlands.Representation.Unramified.SphericalConstituentExistenceProof

/-!
# Standard Hecke scalars on unramified principal series

On the vectors of the normalized principal series `I(z)` fixed by `K = GL_(r+1)(O_F)`,
the sum of the translates by the labelled coset representatives of `K t_i K` is the
scalar `q^(i(r+1-i)/2) e_i(z)`, where `e_i` is the `i`-th elementary symmetric
function of the uniformizer values `z`.
-/

noncomputable section

namespace Langlands.Unramified

open Correspondence GeneralLinear GeneralLinear.BlockShape GeneralLinear.Iwasawa MinusculeCosets
  SphericalExistence
open scoped NNReal

universe uF

/-! ### Counting pairs -/

section Counting

variable {m : ℕ}

theorem card_radicalPairs (S : Finset (Fin m)) :
    Fintype.card (RadicalPairs S) =
      ∑ a : Fin m, ∑ b : Fin m, if a ∈ S ∧ b ∉ S ∧ a < b then 1 else 0 := by
  rw [Fintype.card_subtype, Finset.card_filter, Fintype.sum_prod_type]
  rfl

/-- The pairs `a < b` separated by `S`, counted in both orders. -/
theorem separated_pair_count (S : Finset (Fin m)) :
    (∑ a : Fin m, ∑ b : Fin m, if a ∈ S ∧ b ∉ S ∧ a < b then 1 else 0) +
      (∑ a : Fin m, ∑ b : Fin m, if a ∉ S ∧ b ∈ S ∧ a < b then 1 else 0) =
      S.card * (m - S.card) := by
  rw [Finset.sum_comm (f := fun a b : Fin m => if a ∉ S ∧ b ∈ S ∧ a < b then 1 else 0),
    ← Finset.sum_add_distrib]
  have h : ∀ a b : Fin m, ((if a ∈ S ∧ b ∉ S ∧ a < b then 1 else 0) +
      (if b ∉ S ∧ a ∈ S ∧ b < a then 1 else 0) : ℕ) =
        (if a ∈ S then 1 else 0) * (if b ∉ S then 1 else 0) := by
    intro a b
    by_cases ha : a ∈ S <;> by_cases hb : b ∈ S
    · simp [ha, hb]
    · have hab : a ≠ b := fun h => hb (h ▸ ha)
      rcases hab.lt_or_gt with h | h
      · simp [ha, hb, h, not_lt_of_gt h]
      · simp [ha, hb, h, not_lt_of_gt h]
    · simp [ha, hb]
    · simp [ha, hb]
  simp_rw [← Finset.sum_add_distrib, h, ← Finset.sum_mul_sum, Finset.sum_boole]
  rw [Finset.filter_univ_mem, Finset.filter_not, Finset.filter_univ_mem, Finset.card_sdiff,
    Finset.card_univ, Fintype.card_fin, Finset.inter_univ]
  simp

end Counting

/-! ### The real scalar of a subset -/

section Scalar

variable {m : ℕ}

/-- For `q > 0`, the radical count and the square root of the modulus of `t_S` combine to
`√q ^ (|S| (m - |S|))`. -/
theorem radical_mul_sqrt_modulus (q : ℝ) (hq : 0 < q) (S : Finset (Fin m)) :
    q ^ Fintype.card (RadicalPairs S) *
      ∏ a : Fin m, ∏ b ∈ Finset.univ.filter (fun b => a < b),
        Real.sqrt (q ^ (-subsetExponent S a)) / Real.sqrt (q ^ (-subsetExponent S b)) =
      Real.sqrt q ^ (S.card * (m - S.card)) := by
  rw [card_radicalPairs, ← separated_pair_count]
  simp_rw [← Finset.sum_add_distrib, ← Finset.prod_pow_eq_pow_sum]
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun a _ => ?_
  rw [Finset.prod_filter, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun b _ => ?_
  have hs : Real.sqrt q ≠ 0 := (Real.sqrt_pos.2 hq).ne'
  have hsq : Real.sqrt q * Real.sqrt q = q := Real.mul_self_sqrt hq.le
  by_cases hab : a < b <;> by_cases ha : a ∈ S <;> by_cases hb : b ∈ S <;>
    simp [hab, ha, hb, subsetExponent, Real.sqrt_inv, hs]
  · field_simp
    rw [Real.sq_sqrt hq.le]

end Scalar

/-! ### Elementary symmetric coefficients -/

theorem elementaryCoefficient_ofTuple {n : ℕ} (z : Fin n → ℂˣ) (i : ℕ) :
    elementaryCoefficient (Eigenvalues.ofTuple z) i =
      ∑ S : {S : Finset (Fin n) // S.card = i}, ∏ j ∈ S.1, (z j : ℂ) := by
  classical
  rw [elementaryCoefficient, Eigenvalues.eulerPolynomial_ofTuple]
  have h1 : ∀ j, (1 - Polynomial.C (z j : ℂ) * Polynomial.X) =
      Polynomial.C (-(z j : ℂ)) * Polynomial.X + 1 := by
    intro j
    rw [Polynomial.C_neg]
    ring
  simp_rw [h1]
  rw [Finset.prod_add]
  simp only [Finset.prod_const_one, mul_one, Finset.prod_mul_distrib, Finset.prod_const,
    ← map_prod, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow]
  rw [← Finset.sum_filter, Finset.mul_sum]
  refine (Finset.sum_subtype (p := fun S : Finset (Fin n) => S.card = i) (F := inferInstance) _
    (fun S => by simp [eq_comm]) _).trans ?_
  · refine Finset.sum_congr rfl fun S _ => ?_
    rw [Finset.prod_neg, S.2, ← mul_assoc, ← pow_add, ← two_mul, pow_mul]
    simp

/-! ### Principal series -/

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance psHeckeFieldTopology : TopologicalSpace F.Carrier :=
  F.canonicalTopologicalData.topology
local instance psHeckeFieldValuativeRel : ValuativeRel F.Carrier :=
  F.canonicalTopologicalData.valuativeRel
local instance psHeckeFieldLocalField : IsNonarchimedeanLocalField F.Carrier :=
  F.canonicalTopologicalData.localField
local instance psHeckeGeneralLinearTopology (n : ℕ) :
    TopologicalSpace (GeneralLinear n F.Carrier) := F.canonicalGeneralLinearTopology n
local instance psHeckeGeneralLinearTopologicalGroup (n : ℕ) :
    IsTopologicalGroup (GeneralLinear n F.Carrier) := F.canonicalGeneralLinearTopologicalGroup n
local instance psHeckeGeneralLinearT2 (n : ℕ) : T2Space (GeneralLinear n F.Carrier) :=
  F.canonicalGeneralLinearT2Space n
local instance psHeckeGeneralLinearMeasurable (n : ℕ) :
    MeasurableSpace (GeneralLinear n F.Carrier) := borel _
local instance psHeckeGeneralLinearBorel (n : ℕ) :
    BorelSpace (GeneralLinear n F.Carrier) := ⟨rfl⟩

theorem borelShape_eq_singletons (r : ℕ) : borelShape r = BlockShape.singletons (r + 1) := rfl

theorem isSmooth_principalSeriesOfTuple {r : ℕ} (z : Fin (r + 1) → ℂˣ) :
    IsSmooth (principalSeriesOfTuple F z) :=
  F.canonicalTopologicalData.isSmooth_normalizedProductInduced _ _

/-- The diagonal Levi element of the Borel subgroup with `ϖ` in the positions of `S`. -/
abbrev subsetLevi {r : ℕ} (ϖ : F.Carrierˣ) (S : Finset (Fin (r + 1))) :
    (borelShape r).Levi F.Carrier :=
  singletonLevi F.Carrier fun j => ϖ ^ subsetExponent S j

/-- The positive square root of the modulus of a Borel Levi element, as a real number. -/
abbrev sqrtModulus {r : ℕ} (m : (borelShape r).Levi F.Carrier) : ℝ :=
  ((NNReal.sqrt (F.canonicalTopologicalData.leviModulus (borelShape r) m : ℝ≥0)) : ℝ)

/-- A `1 × 1` scalar matrix acts on a line induced from a character by the value of the
character. -/
theorem characterRepresentation_scalar (χ : QuasiCharacter F) (a : F.Carrierˣ) (x : ℂ) :
    characterRepresentation (determinantQuasiCharacter F 1 χ)
        (GeneralLinear.scalar a : GeneralLinear ((1 : ℕ+) : ℕ) F.Carrier) x = (χ a : ℂ) • x := by
  change ((χ.toMonoidHom (Matrix.GeneralLinearGroup.det
    (Matrix.GeneralLinearGroup.scalar (Fin ((1 : ℕ+) : ℕ)) a)) : ℂˣ) : ℂ) • x = _
  rw [Matrix.GeneralLinearGroup.det_scalar, Fintype.card_fin, PNat.one_coe, pow_one]
  rfl

/-- The block factors of the principal series act on the tensor product of the lines by
the product of the characters at the diagonal entries. -/
theorem blockTensor_subsetLevi {r : ℕ} (z : Fin (r + 1) → ℂˣ) (ϖ : F.Carrierˣ)
    (S : Finset (Fin (r + 1))) (w : PiTensorProduct ℂ fun _ : Fin (borelShape r).length => ℂ) :
    (borelShape r).blockTensor (blockCharacters F z) (subsetLevi F ϖ S) w =
      ((∏ j, character F (z j) (ϖ ^ subsetExponent S j) : ℂˣ) : ℂ) • w := by
  have key : ((borelShape r).blockTensor (blockCharacters F z) (subsetLevi F ϖ S) :
      Module.End ℂ (PiTensorProduct ℂ fun _ : Fin (borelShape r).length => ℂ)) =
      ((∏ j, character F (z j) (ϖ ^ subsetExponent S j) : ℂˣ) : ℂ) • LinearMap.id := by
    apply PiTensorProduct.ext
    apply MultilinearMap.ext
    intro v
    erw [LinearMap.compMultilinearMap_apply, blockTensor_tprod]
    have hσ : ∀ j : Fin (borelShape r).length,
        blockCharacters F z j (subsetLevi F ϖ S j) (v j) =
          (character F (z j) (ϖ ^ subsetExponent S j) : ℂ) • v j := fun j =>
      characterRepresentation_scalar F (characterTuple F z j) _ (v j)
    simp_rw [hσ]
    rw [MultilinearMap.map_smul_univ, LinearMap.compMultilinearMap_apply, LinearMap.smul_apply,
      LinearMap.id_apply, Units.coe_prod]
    rfl
  rw [key]
  rfl

/-! ### Representatives in the Borel subgroup -/

theorem labelledRep_isUpperTriangular {K : Type*} [Field K] {m i : ℕ} {Λ : Type*} (ϖ : Kˣ)
    (σ : Λ → K) (α : CosetIndex Λ m i) : (labelledRep ϖ σ α).val.IsUpperTriangular := by
  change ((radicalElement α.1.1 (liftCoeff σ α.1.1 α.2)).val *
    (subsetTorus ϖ α.1.1).val).IsUpperTriangular
  rw [torus_val]
  exact (radicalElement_mem_upperUnipotent _ _).1.mul (Matrix.blockTriangular_diagonal _)

/-- The Levi part of a labelled representative is the subset torus. -/
theorem leviProjection_labelledRep {r i : ℕ} {Λ : Type*} (ϖ : F.Carrierˣ) (σ : Λ → F.Carrier)
    (α : CosetIndex Λ (r + 1) i)
    (h : labelledRep ϖ σ α ∈ (borelShape r).parabolic F.Carrier) :
    (borelShape r).leviProjection F.Carrier ⟨labelledRep ϖ σ α, h⟩ = subsetLevi F ϖ α.1.1 := by
  change (singletons (r + 1)).leviProjection F.Carrier ⟨labelledRep ϖ σ α, h⟩ =
    singletonLevi F.Carrier _
  funext j
  apply Units.ext
  ext a b
  obtain rfl : a = b := Subsingleton.elim a b
  rw [leviProjection_apply, singletons_index, singletonLevi_apply]
  change (radicalElement α.1.1 (liftCoeff σ α.1.1 α.2) * subsetTorus ϖ α.1.1) j j = _
  rw [mul_subsetTorus_apply, radicalElement_apply]
  have hp : ¬IsRadicalPair α.1.1 j j := fun h => h.ne rfl
  by_cases hj : j ∈ α.1.1 <;>
    simp [hp, hj, subsetExponent, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply]

/-- Evaluation of a principal-series function at a labelled representative. -/
theorem eval_labelledRep {r i : ℕ} {Λ : Type*} (z : Fin (r + 1) → ℂˣ) (ϖ : F.Carrierˣ)
    (σ : Λ → F.Carrier)
    (φ : Induction.SmoothFunctions ((borelShape r).parabolic F.Carrier) (borelInducing F z))
    (α : CosetIndex Λ (r + 1) i) :
    Induction.eval _ _ φ (labelledRep ϖ σ α) =
      ((sqrtModulus F (subsetLevi F ϖ α.1.1) : ℂ) *
        ((∏ j, character F (z j) (ϖ ^ subsetExponent α.1.1 j) : ℂˣ) : ℂ)) •
        Induction.eval _ _ φ 1 := by
  have h := mem_parabolic_of_isUpperTriangular (borelShape r) _
    (labelledRep_isUpperTriangular ϖ σ α)
  have hcov := F.canonicalTopologicalData.normalizedProductInduced_covariant (borelShape r)
    (blockCharacters F z) φ ⟨_, h⟩ 1
  rw [mul_one] at hcov
  rw [hcov, leviProjection_labelledRep F ϖ σ α h, blockTensor_subsetLevi, smul_smul]

/-- The square root of the modulus of the subset torus of the canonical uniformizer. -/
theorem sqrtModulus_subsetLevi {r : ℕ} (S : Finset (Fin (r + 1))) :
    sqrtModulus F (subsetLevi F F.canonicalTopologicalData.uniformizerUnit S) =
      ∏ a : Fin (r + 1), ∏ b ∈ Finset.univ.filter (fun b => a < b),
        Real.sqrt ((F.canonicalTopologicalData.residueCardinality : ℝ) ^ (-subsetExponent S a)) /
          Real.sqrt ((F.canonicalTopologicalData.residueCardinality : ℝ) ^
            (-subsetExponent S b)) := by
  have h : F.canonicalTopologicalData.leviModulus (borelShape r)
      (subsetLevi F F.canonicalTopologicalData.uniformizerUnit S) = _ :=
    F.canonicalTopologicalData.leviModulus_singletonLevi
      (fun j => F.canonicalTopologicalData.uniformizerUnit ^ subsetExponent S j)
  have hs : ∀ x : ℝ≥0, NNReal.sqrt x = NNReal.sqrtHom x := fun _ => rfl
  rw [sqrtModulus, h, Units.coe_prod, hs, map_prod]
  simp_rw [Units.coe_prod, map_prod, ← hs, Units.val_div_eq_div_val, NNReal.sqrt_div,
    NNReal.coe_prod, NNReal.coe_div, Real.coe_sqrt,
    PadicField.TopologicalData.normalizedAbsUnits_coe,
    LocalFactor.PadicAbelian.uniformizerUnit_zpow_abs]

/-! ### Fixed vectors are determined by their value at the identity -/

/-- Evaluation at a point, as a linear map. -/
def evalAt {r : ℕ} (z : Fin (r + 1) → ℂˣ) (g : GeneralLinear (r + 1) F.Carrier) :
    Induction.SmoothFunctions ((borelShape r).parabolic F.Carrier) (borelInducing F z) →ₗ[ℂ]
      PiTensorProduct ℂ (fun _ : Fin (borelShape r).length => ℂ) where
  toFun φ := Induction.eval _ _ φ g
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem evalAt_apply {r : ℕ} (z : Fin (r + 1) → ℂˣ) (g : GeneralLinear (r + 1) F.Carrier)
    (φ : Induction.SmoothFunctions ((borelShape r).parabolic F.Carrier) (borelInducing F z)) :
    evalAt F z g φ = Induction.eval _ _ φ g := rfl

/-- The group acts on the principal series by right translation. -/
theorem eval_principalSeriesOfTuple {r : ℕ} (z : Fin (r + 1) → ℂˣ)
    (g x : GeneralLinear (r + 1) F.Carrier)
    (φ : Induction.SmoothFunctions ((borelShape r).parabolic F.Carrier) (borelInducing F z)) :
    Induction.eval _ _ (principalSeriesOfTuple F z g φ) x = Induction.eval _ _ φ (x * g) := rfl

/-- A `K`-fixed vector of the principal series vanishing at the identity is zero. -/
theorem eq_zero_of_eval_one {r : ℕ} {z : Fin (r + 1) → ℂˣ}
    (φ : fixedVectors (principalSeriesOfTuple F z) (sphericalSubgroup F r))
    (h : Induction.eval _ _ (φ : Induction.SmoothFunctions ((borelShape r).parabolic F.Carrier)
      (borelInducing F z)) 1 = 0) : φ = 0 := by
  have hall : ∀ g, Induction.eval _ _ (φ : Induction.SmoothFunctions
      ((borelShape r).parabolic F.Carrier) (borelInducing F z)) g = 0 := by
    intro g
    obtain ⟨b, k, hk, rfl⟩ := exists_borel_mul_spherical F g
    have hk1 : Induction.eval _ _ (φ : Induction.SmoothFunctions
        ((borelShape r).parabolic F.Carrier) (borelInducing F z)) k = 0 := by
      have hfix : principalSeriesOfTuple F z k (φ : _) = φ := φ.property ⟨k, hk⟩
      have := congrArg (fun ψ => Induction.eval _ _ ψ 1) hfix
      rw [← h, ← this, eval_principalSeriesOfTuple, one_mul]
    have hcov := F.canonicalTopologicalData.normalizedProductInduced_covariant (borelShape r)
      (blockCharacters F z) (φ : _) b k
    rw [hcov, hk1, map_zero, smul_zero]
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  funext g
  exact hall g

/-! ### The scalar -/

/-- The sum over the labelled representatives of the scalars at their Levi parts. -/
theorem sum_labelledRep_scalar {r : ℕ} (z : Fin (r + 1) → ℂˣ) (i : Fin (r + 2)) :
    ∑ α : CosetIndex F.canonicalTopologicalData.ResidueField (r + 1) i.val,
        ((sqrtModulus F (subsetLevi F F.canonicalTopologicalData.uniformizerUnit α.1.1) : ℂ) *
          ((∏ j, character F (z j)
            (F.canonicalTopologicalData.uniformizerUnit ^ subsetExponent α.1.1 j) : ℂˣ) : ℂ)) =
      standardHeckeScalar F (Eigenvalues.ofTuple z) i := by
  have hq : (0 : ℝ) < F.canonicalTopologicalData.residueCardinality := by
    have := F.canonicalTopologicalData.residueCardinality_gt_one
    exact_mod_cast Nat.zero_lt_of_lt this
  have hΛ : Fintype.card F.canonicalTopologicalData.ResidueField =
      F.canonicalTopologicalData.residueCardinality :=
    Nat.card_eq_fintype_card.symm
  have hchar : ∀ (S : Finset (Fin (r + 1))),
      ((∏ j, character F (z j)
        (F.canonicalTopologicalData.uniformizerUnit ^ subsetExponent S j) : ℂˣ) : ℂ) =
        ∏ j ∈ S, (z j : ℂ) := by
    intro S
    rw [Units.coe_prod, ← Finset.prod_filter_mul_prod_filter_not Finset.univ (· ∈ S)]
    rw [Finset.filter_univ_mem]
    have h1 : ∀ j ∈ Finset.univ.filter (· ∉ S), ((character F (z j)
        (F.canonicalTopologicalData.uniformizerUnit ^ subsetExponent S j) : ℂˣ) : ℂ) = 1 := by
      intro j hj
      rw [Finset.mem_filter] at hj
      simp [subsetExponent, hj.2, PadicField.TopologicalData.ord_one]
    rw [Finset.prod_eq_one h1, mul_one]
    refine Finset.prod_congr rfl fun j hj => ?_
    simp [subsetExponent, hj, PadicField.TopologicalData.ord_uniformizer]
  rw [Fintype.sum_sigma]
  simp only [hchar, sqrtModulus_subsetLevi, Finset.sum_const, Finset.card_univ,
    Fintype.card_fun, hΛ, nsmul_eq_mul]
  rw [standardHeckeScalar, elementaryCoefficient_ofTuple, Finset.mul_sum]
  refine Finset.sum_congr rfl fun S _ => ?_
  have key := radical_mul_sqrt_modulus _ hq S.1
  rw [S.2] at key
  have key' := congrArg (fun x : ℝ => (x : ℂ)) key
  push_cast at key'
  push_cast
  rw [← mul_assoc, key']

/-- On `K`-fixed vectors of the principal series, the sum of the translates by the labelled
representatives of `K t_i K` is the standard Hecke scalar of the spectrum of `z`. -/
theorem principalSeries_sum_labelledRep {r : ℕ} (z : Fin (r + 1) → ℂˣ) (i : Fin (r + 2))
    (φ : fixedVectors (principalSeriesOfTuple F z) (sphericalSubgroup F r)) :
    ∑ α : CosetIndex F.canonicalTopologicalData.ResidueField (r + 1) i.val,
        principalSeriesOfTuple F z
          (labelledRep F.canonicalTopologicalData.uniformizerUnit (residueLift F) α)
          (φ : Induction.SmoothFunctions ((borelShape r).parabolic F.Carrier)
            (borelInducing F z)) =
      standardHeckeScalar F (Eigenvalues.ofTuple z) i •
        (φ : Induction.SmoothFunctions ((borelShape r).parabolic F.Carrier)
          (borelInducing F z)) := by
  have hc := (Hecke.cornerAction (sphericalHaar F r) (principalSeriesOfTuple F z)
    (isSmooth_principalSeriesOfTuple F z) (sphericalOpenSubgroup F r)
    (sphericalOpenSubgroup_isCompact F r) (standardHeckeElement F r i) φ).property
  rw [standardHecke_cornerAction_eq_sum F (principalSeriesOfTuple F z)
    (isSmooth_principalSeriesOfTuple F z) i φ] at hc
  have hmem := sub_mem hc (Submodule.smul_mem _ (standardHeckeScalar F (Eigenvalues.ofTuple z) i)
    φ.property)
  have h0 := eq_zero_of_eval_one F
    (⟨_, hmem⟩ : fixedVectors (principalSeriesOfTuple F z) (sphericalSubgroup F r)) (by
      change evalAt F z 1 (_ - _) = 0
      rw [map_sub, map_sum, map_smul]
      simp only [evalAt_apply, eval_principalSeriesOfTuple, one_mul, eval_labelledRep]
      rw [← Finset.sum_smul, sum_labelledRep_scalar, sub_self])
  exact sub_eq_zero.1 (congrArg Subtype.val h0)

end Langlands.Unramified
