import Langlands.Representation.RankinSelberg.RankOneQuotient
import Langlands.BaseChange.SatakeCharacterStatement
import Langlands.Group.GL.UnramifiedCharacter
import Langlands.LocalField.SmoothCharacterNormProof
import Langlands.Representation.RankinSelberg.RankOneCharacterReductionProof
import Langlands.Representation.Unramified.StandardMonomialSupport
import Langlands.Representation.Unramified.TopHeckeOperator

/-! # Base change of the rank-one spherical Hecke algebra -/

noncomputable section

namespace Langlands.BaseChange

open Correspondence Langlands.Unramified
open Hecke.HeckeAlgebra.Corner

universe u v

attribute [local instance] heckeFieldTopology heckeFieldValuativeRel heckeFieldLocalField
  heckeGeneralLinearTopology heckeGeneralLinearTopologicalGroup heckeGeneralLinearT2
  heckeGeneralLinearMeasurable heckeGeneralLinearBorel

variable {p : ℕ} [Fact p.Prime]

section TopHecke

variable {F : PadicField.{u} p} {E : PadicField.{v} p} {l r : ℕ}

private theorem standardHeckeScalar_top_ofTuple (F : PadicField.{u} p)
    (s : Fin (r + 1) → ℂˣ) :
    standardHeckeScalar F (Eigenvalues.ofTuple s) (Fin.last (r + 1)) =
      ∏ j, (s j : ℂ) := by
  classical
  rw [standardHeckeScalar_last, elementaryCoefficient_ofTuple]
  have eq_univ (S : {S : Finset (Fin (r + 1)) // S.card = r + 1}) : S.1 = Finset.univ :=
    Finset.eq_univ_of_card S.1 (by simpa using S.property)
  have : Subsingleton {S : Finset (Fin (r + 1)) // S.card = r + 1} :=
    ⟨fun S S' => Subtype.ext ((eq_univ S).trans (eq_univ S').symm)⟩
  rw [Fintype.sum_subsingleton _ ⟨Finset.univ, by simp⟩]

/-- In every rank, base change carries the uniformizer scalar double coset
to the `l`-th convolution power of the corresponding base-field coset. -/
theorem IsUnramifiedBaseChangeHom.map_standardHeckeElement_last
    {b : SphericalHeckeAlgebra E r →ₐ[ℂ] SphericalHeckeAlgebra F r}
    (hb : IsUnramifiedBaseChangeHom F E l r b)
    (hSatakeF : SatakeCharacterStatement.{u}) (hSatakeE : SatakeCharacterStatement.{v}) :
    b (standardHeckeElement E r (Fin.last (r + 1))) =
      standardHeckeElement F r (Fin.last (r + 1)) ^ l := by
  apply sub_eq_zero.mp
  apply (hSatakeF p F r).2
  intro s ω hω
  obtain ⟨z, rfl⟩ := Eigenvalues.ofTuple_surjective _ s
  obtain ⟨η, hη⟩ := (hSatakeE p E r).1 (Eigenvalues.power (Eigenvalues.ofTuple z) l)
  have h := DFunLike.congr_fun (hb _ ω η hω hη) (standardHeckeElement E r (Fin.last (r + 1)))
  change ω (b (standardHeckeElement E r (Fin.last (r + 1)))) = _ at h
  rw [map_sub, sub_eq_zero, h, hη, map_pow, hω, Eigenvalues.power_ofTuple,
    standardHeckeScalar_top_ofTuple, standardHeckeScalar_top_ofTuple]
  simp only [Units.val_pow_eq_pow_val, Finset.prod_pow]

end TopHecke

section RankOne

variable (F : PadicField.{u} p)

/-- In rank one, determinant order is the coordinate on the spherical double cosets. -/
abbrev rankOneOrder (g : GeneralLinear 1 F.Carrier) : ℤ :=
  F.canonicalTopologicalData.ord (GeneralLinear.determinant g : F.Carrier)

theorem rankOne_determinant_injective {K : Type*} [Field K] :
    Function.Injective (GeneralLinear.determinant (R := K) (n := 1)) := by
  intro g h e
  rw [← RankinSelberg.scalar_determinant_rankOne g, ← RankinSelberg.scalar_determinant_rankOne h, e]

theorem rankOne_mul_comm {K : Type*} [Field K] (g h : GeneralLinear 1 K) : g * h = h * g :=
  Langlands.RankinSelberg.rankOne_mul_comm g h

theorem rankOneOrder_mul (g h : GeneralLinear 1 F.Carrier) :
    rankOneOrder F (g * h) = rankOneOrder F g + rankOneOrder F h := by
  rw [rankOneOrder, map_mul, Units.val_mul,
    F.canonicalTopologicalData.ord_mul (Units.ne_zero _) (Units.ne_zero _)]

theorem rankOneOrder_inv (g : GeneralLinear 1 F.Carrier) :
    rankOneOrder F g⁻¹ = -rankOneOrder F g := by
  rw [rankOneOrder, map_inv, Units.val_inv_eq_inv_val, F.canonicalTopologicalData.ord_inv]

theorem rankOneOrder_zpow (g : GeneralLinear 1 F.Carrier) (m : ℤ) :
    rankOneOrder F (g ^ m) = m * rankOneOrder F g := by
  rw [rankOneOrder, map_zpow, Units.val_zpow_eq_zpow_val, F.canonicalTopologicalData.ord_zpow]

theorem rankOne_mem_spherical_iff (g : GeneralLinear 1 F.Carrier) :
    g ∈ sphericalOpenSubgroup F 0 ↔ rankOneOrder F g = 0 := by
  let T := F.canonicalTopologicalData
  let w := ValuativeRel.valuation F.Carrier
  have hord (x : GeneralLinear 1 F.Carrier) (hx : rankOneOrder F x = 0) :
      ∀ i j, x i j ∈ w.integer := by
    intro i j
    fin_cases i
    fin_cases j
    change (x : Matrix (Fin 1) (Fin 1) F.Carrier) 0 0 ∈ w.integer
    rw [← Matrix.det_fin_one (x : Matrix (Fin 1) (Fin 1) F.Carrier)]
    exact (w.mem_integer_iff _).2
      ((T.normalizedAbs_eq_one_iff_valuation_eq_one _).1
        ((T.ord_eq_zero_iff_normalizedAbs (GeneralLinear.determinant x)).1 hx)).le
  constructor
  · intro hg
    exact (T.ord_eq_zero_iff_normalizedAbs _).2
      ((T.normalizedAbs_eq_one_iff_valuation_eq_one _).2 (valuation_det_of_mem_spherical hg))
  · intro hg
    exact (Conductor.mem_integralSubgroup w.integer 0 g).2
      ⟨hord g hg, hord g⁻¹ (by rw [rankOneOrder_inv, hg, neg_zero])⟩

private abbrev rankOneDiagonal : GeneralLinear 1 F.Carrier :=
  standardDiagonal F 0 (Fin.last 1)

private theorem rankOneOrder_diagonal : rankOneOrder F (rankOneDiagonal F) = 1 := by
  rw [rankOneOrder, rankOneDiagonal, standardDiagonal_last, GeneralLinear.determinant,
    Matrix.GeneralLinearGroup.det_scalar, Fintype.card_fin, pow_one,
    PadicField.TopologicalData.uniformizerUnit_val, F.canonicalTopologicalData.ord_uniformizer]

private theorem rankOne_mem_normalizer (g : GeneralLinear 1 F.Carrier) :
    g ∈ Subgroup.normalizer ((sphericalOpenSubgroup F 0).toSubgroup :
      Set (GeneralLinear 1 F.Carrier)) :=
  Subgroup.center_le_normalizer _ (Subgroup.mem_center_iff.2 (fun x => rankOne_mul_comm x g))

private def rankOneCoset : GeneralLinear 1 F.Carrier →* SphericalHeckeAlgebra F 0 where
  toFun := doubleCoset (sphericalOpenSubgroup F 0) (sphericalOpenSubgroup_isCompact F 0)
    (sphericalHaar F 0)
  map_one' := doubleCoset_one _ _ _
  map_mul' g h := by
    have he := doubleCoset_mul_mul_of_mem_normalizer (sphericalOpenSubgroup F 0)
      (sphericalOpenSubgroup_isCompact F 0) (sphericalHaar F 0)
      (rankOne_mem_normalizer F g) (rankOne_mem_normalizer F h) 1
    simpa only [doubleCoset_one, mul_one] using he.symm

private theorem rankOneCoset_power_apply (m : ℤ) (g : GeneralLinear 1 F.Carrier) :
    rankOneCoset F (rankOneDiagonal F ^ m) g = if rankOneOrder F g = m then 1 else 0 := by
  classical
  change doubleCoset (sphericalOpenSubgroup F 0) (sphericalOpenSubgroup_isCompact F 0)
    (sphericalHaar F 0) (rankOneDiagonal F ^ m) g = _
  rw [doubleCoset_apply_of_mem_normalizer _ _ _ (rankOne_mem_normalizer F _),
    one_apply, sphericalHaar_real_self]
  have hmem : (rankOneDiagonal F ^ m)⁻¹ * g ∈ sphericalOpenSubgroup F 0 ↔
      rankOneOrder F g = m := by
    rw [rankOne_mem_spherical_iff, rankOneOrder_mul, rankOneOrder_inv, rankOneOrder_zpow,
      rankOneOrder_diagonal, mul_one]
    omega
  simp [Set.indicator_apply, hmem]

private theorem rankOneCoset_eq (x : GeneralLinear 1 F.Carrier) :
    rankOneCoset F x = rankOneCoset F (rankOneDiagonal F ^ rankOneOrder F x) := by
  let d := rankOneDiagonal F ^ rankOneOrder F x
  have hk : d⁻¹ * x ∈ sphericalOpenSubgroup F 0 := by
    rw [rankOne_mem_spherical_iff, rankOneOrder_mul, rankOneOrder_inv]
    dsimp [d]
    rw [rankOneOrder_zpow, rankOneOrder_diagonal, mul_one, neg_add_cancel]
  have hx : x ∈ Hecke.TestFunction.doubleCosetSet (sphericalOpenSubgroup F 0) d :=
    (Hecke.TestFunction.mem_doubleCosetSet _ _ _).2
      ⟨1, one_mem _, d⁻¹ * x, hk, by rw [one_mul, mul_inv_cancel_left]⟩
  exact doubleCoset_eq_of_mem _ _ _ hx

/-- A spherical rank-one function is constant at each determinant order. -/
theorem rankOne_eq_of_order (f : SphericalHeckeAlgebra F 0) {x y : GeneralLinear 1 F.Carrier}
    (h : rankOneOrder F x = rankOneOrder F y) : f x = f y := by
  have hk : x⁻¹ * y ∈ sphericalOpenSubgroup F 0 := by
    rw [rankOne_mem_spherical_iff, rankOneOrder_mul, rankOneOrder_inv, h, neg_add_cancel]
  have he := rightInvariant (sphericalHaar F 0) (sphericalOpenSubgroup F 0)
    (sphericalOpenSubgroup_isCompact F 0) f ⟨x⁻¹ * y, hk⟩ x
  change f (x * (x⁻¹ * y)) = f x at he
  rw [mul_inv_cancel_left] at he
  exact he.symm

end RankOne

section BaseChange

variable {F : PadicField.{u} p} {E : PadicField.{v} p} {l : ℕ}
variable {b : SphericalHeckeAlgebra E 0 →ₐ[ℂ] SphericalHeckeAlgebra F 0}

private theorem map_rankOneCoset_power (hb : IsUnramifiedBaseChangeHom F E l 0 b)
    (hSatakeF : SatakeCharacterStatement.{u}) (hSatakeE : SatakeCharacterStatement.{v})
    (m : ℤ) :
    b (rankOneCoset E (rankOneDiagonal E ^ m)) =
      rankOneCoset F (rankOneDiagonal F ^ ((l : ℤ) * m)) := by
  let aE := (rankOneCoset E).toHomUnits (rankOneDiagonal E)
  let aF := (rankOneCoset F).toHomUnits (rankOneDiagonal F)
  have ha : Units.map b.toMonoidHom aE = aF ^ l := by
    apply Units.ext
    exact hb.map_standardHeckeElement_last hSatakeF hSatakeE
  calc
    b (rankOneCoset E (rankOneDiagonal E ^ m)) =
        (Units.map b.toMonoidHom (aE ^ m) : (SphericalHeckeAlgebra F 0)ˣ).val := by
      dsimp [aE]
      rw [← map_zpow]
      rfl
    _ = (aF ^ ((l : ℤ) * m) : (SphericalHeckeAlgebra F 0)ˣ).val := by
      rw [map_zpow, ha, ← zpow_natCast, ← zpow_mul]
    _ = rankOneCoset F (rankOneDiagonal F ^ ((l : ℤ) * m)) := by
      dsimp [aF]
      rw [← map_zpow]
      rfl

/-- In rank one the spherical base-change map multiplies the Laurent exponents by `l`. -/
theorem IsUnramifiedBaseChangeHom.rankOne_apply (hb : IsUnramifiedBaseChangeHom F E l 0 b)
    (hSatakeF : SatakeCharacterStatement.{u}) (hSatakeE : SatakeCharacterStatement.{v})
    (hl : l ≠ 0) (φ : SphericalHeckeAlgebra E 0) (g : GeneralLinear 1 F.Carrier) :
    b φ g = if (l : ℤ) ∣ rankOneOrder F g then
      φ (standardDiagonal E 0 (Fin.last 1) ^ (rankOneOrder F g / (l : ℤ))) else 0 := by
  have hspan : φ ∈ Submodule.span ℂ (Set.range (rankOneCoset E)) := by
    change φ ∈ Submodule.span ℂ (Set.range (doubleCoset (sphericalOpenSubgroup E 0)
      (sphericalOpenSubgroup_isCompact E 0) (sphericalHaar E 0)))
    rw [span_range_doubleCoset]
    exact Submodule.mem_top
  induction hspan using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨x, rfl⟩ := hf
    rw [rankOneCoset_eq E x, map_rankOneCoset_power hb hSatakeF hSatakeE,
      rankOneCoset_power_apply]
    by_cases hdiv : (l : ℤ) ∣ rankOneOrder F g
    · rw [ite_eq_left hdiv, rankOneCoset_power_apply, rankOneOrder_zpow, rankOneOrder_diagonal, mul_one]
      obtain ⟨k, hk⟩ := hdiv
      have hlnz : (l : ℤ) ≠ 0 := by exact_mod_cast hl
      rw [hk, mul_comm (l : ℤ) k, Int.mul_ediv_cancel _ hlnz, mul_comm k (l : ℤ)]
      simp only [mul_right_inj' hlnz]
    · rw [ite_eq_right hdiv, ite_eq_right]
      exact fun h => hdiv ⟨_, h⟩
  | zero =>
    rw [map_zero]
    change (0 : ℂ) = if (l : ℤ) ∣ rankOneOrder F g then 0 else 0
    simp
  | add a c _ _ ha hc =>
    rw [map_add]
    change b a g + b c g = if (l : ℤ) ∣ rankOneOrder F g then
      a (rankOneDiagonal E ^ (rankOneOrder F g / (l : ℤ))) +
        c (rankOneDiagonal E ^ (rankOneOrder F g / (l : ℤ))) else 0
    rw [ha, hc]
    split_ifs
    · rfl
    · exact add_zero 0
  | smul a f _ hf =>
    rw [map_smul]
    change a * b f g = if (l : ℤ) ∣ rankOneOrder F g then
      a * f (rankOneDiagonal E ^ (rankOneOrder F g / (l : ℤ))) else 0
    rw [hf]
    split_ifs
    · rfl
    · exact mul_zero a

theorem IsUnramifiedBaseChangeHom.rankOne_apply_of_order (hb : IsUnramifiedBaseChangeHom F E l 0 b)
    (hSatakeF : SatakeCharacterStatement.{u}) (hSatakeE : SatakeCharacterStatement.{v})
    (hl : l ≠ 0) (φ : SphericalHeckeAlgebra E 0) {g : GeneralLinear 1 F.Carrier}
    {x : GeneralLinear 1 E.Carrier} (h : rankOneOrder F g = (l : ℤ) * rankOneOrder E x) :
    b φ g = φ x := by
  rw [hb.rankOne_apply hSatakeF hSatakeE hl, ite_eq_left ⟨rankOneOrder E x, h⟩]
  apply rankOne_eq_of_order
  rw [rankOneOrder_zpow, rankOneOrder_diagonal, mul_one, h, mul_comm (l : ℤ)]
  exact Int.mul_ediv_cancel _ (by exact_mod_cast hl)

end BaseChange

end Langlands.BaseChange
