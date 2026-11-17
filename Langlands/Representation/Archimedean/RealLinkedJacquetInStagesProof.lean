import Langlands.Representation.Archimedean.RealLinkedJacquetPairReduction
import Langlands.Representation.Archimedean.RealInductionStagesDerivative
import Langlands.Representation.Archimedean.RealSliceSurjective
import Langlands.Representation.Archimedean.JacquetKernel

/-!
# Induction in stages for the linked real Jacquet functional

This file proves `RealLinkedJacquetFunctionalInStagesStatement`. For a list
`pre ++ core ++ post` of real blocks of total rank `n`, with `a = rank pre`, `r = rank core` and
`c = (rank post - rank pre)/2`, restriction to the middle block,
`Res F (g) = F(diag(1_a, g, 1))`, maps the `O(n)`-finite functions of the standard module of
`pre ++ core ++ post` to the `O(r)`-finite functions of the standard module of `core` twisted
by `|det|^c`. If `ℓ'` is a functional as in `RealLinkedJacquetFunctionalExists` for the twisted
list, then `ℓ' ∘ Res` is one for `pre ++ core ++ post`.

`Res` is built from Worker 109's slice `σ₁` (module `RealInductionStagesSlice`) and the twist
by `|det|^c`. Nonvanishing of `ℓ' ∘ Res` uses Worker 109's induced maps `Ind T`
(`RealInductionStagesInduce`) and an explicit polynomial test function on `O(n)`.
-/

noncomputable section

open scoped TensorProduct Matrix Manifold ContDiff Matrix.Norms.Operator

set_option autoImplicit false

namespace Langlands.Archimedean

attribute [local instance 100] LieRing.ofAssociativeRing

set_option backward.isDefEq.respectTransparency false

namespace RealLinkedJacquetStages

open Langlands.GeneralLinear Langlands.LocalFactor.Archimedean
open InductionStages RealBlockRotation RealBlockFourierFinite

/-! ## The factor `|det|^s` -/

section DetPow

variable {r : ℕ}

/-- `|det g|^s` on `GL_r(ℝ)`. -/
def detPow (r : ℕ) (s : ℂ) (g : Langlands.GeneralLinear r ℝ) : ℂ :=
  ((|(g : Matrix (Fin r) (Fin r) ℝ).det| : ℝ) : ℂ) ^ s

theorem abs_det_pos (g : Langlands.GeneralLinear r ℝ) :
    0 < |(g : Matrix (Fin r) (Fin r) ℝ).det| :=
  abs_pos.mpr ((Matrix.isUnit_iff_isUnit_det _).mp (Units.isUnit g)).ne_zero

theorem ofReal_abs_det_ne_zero (g : Langlands.GeneralLinear r ℝ) :
    ((|(g : Matrix (Fin r) (Fin r) ℝ).det| : ℝ) : ℂ) ≠ 0 :=
  Complex.ofReal_ne_zero.mpr (abs_det_pos g).ne'

theorem detPow_add (s t : ℂ) (g : Langlands.GeneralLinear r ℝ) :
    detPow r (s + t) g = detPow r s g * detPow r t g :=
  Complex.cpow_add _ _ (ofReal_abs_det_ne_zero g)

theorem detPow_zero (g : Langlands.GeneralLinear r ℝ) : detPow r 0 g = 1 :=
  Complex.cpow_zero _

theorem detPow_ne_zero (s : ℂ) (g : Langlands.GeneralLinear r ℝ) : detPow r s g ≠ 0 :=
  Complex.cpow_ne_zero_iff.mpr (Or.inl (ofReal_abs_det_ne_zero g))

theorem detPow_mul_detPow_neg (s : ℂ) (g : Langlands.GeneralLinear r ℝ) :
    detPow r s g * detPow r (-s) g = 1 := by
  rw [← detPow_add, add_neg_cancel, detPow_zero]

theorem detPow_mul (s : ℂ) (g g' : Langlands.GeneralLinear r ℝ) :
    detPow r s (g * g') = detPow r s g * detPow r s g' := by
  simp only [detPow, Units.val_mul, Matrix.det_mul, abs_mul, Complex.ofReal_mul]
  exact Complex.mul_cpow_ofReal_nonneg (abs_nonneg _) (abs_nonneg _) _

theorem detPow_of_abs_det_eq_one (s : ℂ) {g : Langlands.GeneralLinear r ℝ}
    (hg : |(g : Matrix (Fin r) (Fin r) ℝ).det| = 1) : detPow r s g = 1 := by
  rw [detPow, hg, Complex.ofReal_one, Complex.one_cpow]

theorem detPow_of_mem_unitaryCompact (s : ℂ) {k : Langlands.GeneralLinear r ℝ}
    (hk : k ∈ unitaryCompact ℝ r) : detPow r s k = 1 := by
  refine detPow_of_abs_det_eq_one s ?_
  have h := Unitary.star_mul_self_of_mem (Matrix.det_of_mem_unitary hk)
  rw [star_trivial] at h
  rcases mul_self_eq_one_iff.mp h with h' | h' <;> rw [h'] <;> simp

theorem detPow_of_mem_upperUnipotent (s : ℂ) {u : Langlands.GeneralLinear r ℝ}
    (hu : u ∈ Langlands.GeneralLinear.upperUnipotent r ℝ) : detPow r s u = 1 := by
  refine detPow_of_abs_det_eq_one s ?_
  rw [Matrix.det_of_isUpperTriangular hu.1, Finset.prod_eq_one fun i _ => hu.2 i, abs_one]

theorem detPow_diagonalUnits (s : ℂ) (t : Fin r → ℝˣ) :
    detPow r s (Iwasawa.diagonalUnits t) = ∏ j, ((|((t j : ℝˣ) : ℝ)| : ℝ) : ℂ) ^ s := by
  rw [detPow, Iwasawa.diagonalUnits_val, Matrix.det_diagonal, Finset.abs_prod]
  exact cpow_prod_ofReal _ _ (fun _ => abs_nonneg _) _

theorem contMDiff_detPow (s : ℂ) : ContMDiff (matrixModel ℝ r) 𝓘(ℝ, ℂ) ∞ (detPow r s) := by
  refine contMDiff_of_contDiffOn
    (ψ := fun y : Matrix (Fin r) (Fin r) ℝ => ((|y.det| : ℝ) : ℂ) ^ s) (fun y hy => ?_)
    fun _ => rfl
  have hdet : y.det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det y).mp hy).ne_zero
  have hd : ContDiff ℝ ∞ (fun y : Matrix (Fin r) (Fin r) ℝ => y.det) :=
    PrincipalSeriesExtension.contDiff_det_comp fun p q =>
      PrincipalSeriesExtension.contDiff_entry p q
  have habs : ContDiffAt ℝ ∞ (fun y : Matrix (Fin r) (Fin r) ℝ => |y.det|) y :=
    (contDiffAt_abs hdet).comp y hd.contDiffAt
  exact (PrincipalSeriesExtension.contDiffAt_ofReal_cpow habs (abs_pos.mpr hdet) _).contDiffWithinAt

/-- Worker 109's factor `ν = |det|^(-c)` is `detPow`. -/
theorem sliceFactor_eq_detPow (n a r : ℕ) :
    sliceFactor n a r = detPow r (-sliceExponent n a r) :=
  rfl

/-- Products of smooth functions on `GL_r(ℝ)` are smooth. -/
theorem contMDiff_mul_fun {f f' : Langlands.GeneralLinear r ℝ → ℂ}
    (hf : ContMDiff (matrixModel ℝ r) 𝓘(ℝ, ℂ) ∞ f)
    (hf' : ContMDiff (matrixModel ℝ r) 𝓘(ℝ, ℂ) ∞ f') :
    ContMDiff (matrixModel ℝ r) 𝓘(ℝ, ℂ) ∞ (fun g => f g * f' g) :=
  contMDiff_of_contDiffOn (ψ := fun y => unitsExtension f y * unitsExtension f' y)
    ((contDiffOn_unitsExtension hf).mul (contDiffOn_unitsExtension hf'))
    fun g => by rw [unitsExtension_val, unitsExtension_val]

/-- Multiplication by `|det|^s` as a linear map of functions on `GL_r(ℝ)`. -/
def detPowMul (r : ℕ) (s : ℂ) :
    (Langlands.GeneralLinear r ℝ → ℂ) →ₗ[ℂ] (Langlands.GeneralLinear r ℝ → ℂ) where
  toFun f g := detPow r s g * f g
  map_add' f f' := by
    funext g
    simp only [Pi.add_apply, mul_add]
  map_smul' c f := by
    funext g
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

theorem detPowMul_apply (s : ℂ) (f : Langlands.GeneralLinear r ℝ → ℂ)
    (g : Langlands.GeneralLinear r ℝ) : detPowMul r s f g = detPow r s g * f g :=
  rfl

end DetPow

/-! ## Twisted lists of blocks -/

section TwistLists

open GramFormula

theorem ofReal_abs_units_ne_zero (x : ℝˣ) : ((|(x : ℝ)| : ℝ) : ℂ) ≠ 0 :=
  Complex.ofReal_ne_zero.mpr (abs_pos.mpr x.ne_zero).ne'

/-- The position characters of a twisted list. -/
theorem realPositionCharacter_map_twist (s : ℝ) : ∀ (ds : List RealBlock) (i : ℕ),
    i < realRank ds → ∀ x : ℝˣ,
      realPositionCharacter (ds.map (realBlockTwist s)) i x =
        realPositionCharacter ds i x * ((|(x : ℝ)| : ℝ) : ℂ) ^ (s : ℂ)
  | [], i, h, _ => by simp at h
  | .character c :: _, 0, _, x => by
      simp only [List.map_cons, realBlockTwist, realPositionCharacter,
        RealJacquetFrobenius.charData_character_apply, RealJacquetFrobenius.charFun]
      rw [c.character_eq, Complex.cpow_add _ _ (ofReal_abs_units_ne_zero x)]
      ring
  | .character _ :: ds, i + 1, h, x => by
      rw [realRank_cons, rank_character] at h
      exact realPositionCharacter_map_twist s ds i (by omega) x
  | .induced d :: _, 0, _, x => by
      simp only [List.map_cons, realBlockTwist, realPositionCharacter,
        realInducedFirstCharacter, characterOfParams_weight, characterOfParams_exponent]
      rw [show d.exponent + (s : ℂ) + (d.weight.natAbs : ℂ) / 2 =
          (d.exponent + (d.weight.natAbs : ℂ) / 2) + s by ring,
        Complex.cpow_add _ _ (ofReal_abs_units_ne_zero x)]
      ring
  | .induced d :: _, 1, _, x => by
      simp only [List.map_cons, realBlockTwist, realPositionCharacter,
        realInducedSecondCharacter, characterOfParams_weight, characterOfParams_exponent]
      rw [show d.exponent + (s : ℂ) - (d.weight.natAbs : ℂ) / 2 =
          (d.exponent - (d.weight.natAbs : ℂ) / 2) + s by ring,
        Complex.cpow_add _ _ (ofReal_abs_units_ne_zero x)]
  | .induced _ :: ds, i + 2, h, x => by
      rw [realRank_cons, rank_induced] at h
      exact realPositionCharacter_map_twist s ds i (by omega) x

/-- The induction blocks of a twisted list. -/
theorem realInducedBlockAt_map_twist (s : ℝ) : ∀ (ds : List RealBlock) (p : ℕ),
    realInducedBlockAt (ds.map (realBlockTwist s)) p =
      (realInducedBlockAt ds p).map fun d => characterOfParams d.weight (d.exponent + s)
  | [], _ => rfl
  | .character _ :: _, 0 => rfl
  | .character _ :: ds, p + 1 => realInducedBlockAt_map_twist s ds p
  | .induced _ :: _, 0 => rfl
  | .induced _ :: _, 1 => rfl
  | .induced _ :: ds, p + 2 => realInducedBlockAt_map_twist s ds p

end TwistLists

/-! ## Twisting standard modules -/

section Twist

variable {r : ℕ}

/-- The block Fourier coefficients of `|det|^s f`. -/
theorem blockFourierCoefficient_detPowMul (s : ℂ) (p : ℕ) (k : ℤ)
    (f : Langlands.GeneralLinear r ℝ → ℂ) (g : Langlands.GeneralLinear r ℝ) :
    blockFourierCoefficient r p k (detPowMul r s f) g =
      detPow r s g * blockFourierCoefficient r p k f g := by
  unfold blockFourierCoefficient
  rw [← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr fun θ _ => ?_
  simp only [detPowMul_apply, detPow_mul,
    detPow_of_mem_unitaryCompact s (blockRotation_mem_unitaryCompact r p θ), one_mul]
  ring

/-- **Twisting.** Let `es` be a list of rank `r` whose position characters are those of `ds`
times `|·|^s` and whose induction blocks have the weights of those of `ds`. Then `|det|^s`
maps the standard module of `ds` into that of `es`. -/
theorem detPowMul_mem_realStandardModule {s : ℝ} {ds es : List RealBlock}
    (hχ : ∀ i : Fin r, ∀ x : ℝˣ, realPositionCharacter es i x =
      realPositionCharacter ds i x * ((|(x : ℝ)| : ℝ) : ℂ) ^ (s : ℂ))
    (hind : ∀ p d', realInducedBlockAt es p = some d' →
      ∃ d, realInducedBlockAt ds p = some d ∧ d.weight = d'.weight)
    {f : Langlands.GeneralLinear r ℝ → ℂ} (hf : f ∈ realStandardModule r ds) :
    detPowMul r s f ∈ realStandardModule r es := by
  refine ⟨⟨contMDiff_mul_fun (contMDiff_detPow (s : ℂ)) hf.1.1, fun t u g => ?_⟩, fun p d' hd' k hk g => ?_⟩
  · have hu : detPow r s (u : Langlands.GeneralLinear r ℝ) = 1 :=
      detPow_of_mem_upperUnipotent _ u.2
    rw [detPowMul_apply, detPowMul_apply, hf.1.2 t u g, detPow_mul, detPow_mul, hu, mul_one,
      detPow_diagonalUnits]
    have hP : principalSeriesCharacter ℝ r (realPositionCharacter es) t =
        principalSeriesCharacter ℝ r (realPositionCharacter ds) t *
          ∏ j, ((|((t j : ℝˣ) : ℝ)| : ℝ) : ℂ) ^ (s : ℂ) := by
      unfold principalSeriesCharacter
      rw [← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun j _ => ?_
      rw [hχ j (t j)]
      ring
    rw [hP]
    ring
  · obtain ⟨d, hd, hw⟩ := hind p d' hd'
    rw [blockFourierCoefficient_detPowMul, hf.2 p d hd k (by rw [hw]; exact hk) g, mul_zero]

theorem detPowMul_mem_kFiniteVectors (s : ℂ) {f : Langlands.GeneralLinear r ℝ → ℂ}
    (hf : f ∈ kFiniteVectors (Whittaker.rightTranslation ℂ (Langlands.GeneralLinear r ℝ))
      (unitaryCompact ℝ r)) :
    detPowMul r s f ∈ kFiniteVectors (Whittaker.rightTranslation ℂ (Langlands.GeneralLinear r ℝ))
      (unitaryCompact ℝ r) := by
  rw [mem_kFiniteVectors_iff] at hf ⊢
  have hle : Submodule.span ℂ (Set.range fun k : unitaryCompact ℝ r =>
      Whittaker.rightTranslation ℂ (Langlands.GeneralLinear r ℝ) (k : Langlands.GeneralLinear r ℝ)
        (detPowMul r s f)) ≤
      (Submodule.span ℂ (Set.range fun k : unitaryCompact ℝ r =>
        Whittaker.rightTranslation ℂ (Langlands.GeneralLinear r ℝ)
          (k : Langlands.GeneralLinear r ℝ) f)).map (detPowMul r s) := by
    rw [Submodule.span_le]
    rintro _ ⟨k, rfl⟩
    refine ⟨Whittaker.rightTranslation ℂ (Langlands.GeneralLinear r ℝ)
      (k : Langlands.GeneralLinear r ℝ) f, Submodule.subset_span ⟨k, rfl⟩, ?_⟩
    funext g
    change detPow r s g * f (g * k) = detPow r s (g * k) * f (g * k)
    rw [detPow_mul, detPow_of_mem_unitaryCompact s k.2, mul_one]
  have := hf
  exact Submodule.finiteDimensional_of_le hle

/-- Multiplication by `|det|^s` from the `O(r)`-finite functions of the standard module of `ds`
to those of `es`, under the hypotheses of `detPowMul_mem_realStandardModule`. -/
def twK {s : ℝ} {ds es : List RealBlock}
    (hχ : ∀ i : Fin r, ∀ x : ℝˣ, realPositionCharacter es i x =
      realPositionCharacter ds i x * ((|(x : ℝ)| : ℝ) : ℂ) ^ (s : ℂ))
    (hind : ∀ p d', realInducedBlockAt es p = some d' →
      ∃ d, realInducedBlockAt ds p = some d ∧ d.weight = d'.weight) :
    KFin r ds →ₗ[ℂ] KFin r es :=
  ((detPowMul r s).comp (KFin r ds).subtype).codRestrict _ fun f =>
    ⟨detPowMul_mem_realStandardModule hχ hind f.2.1, detPowMul_mem_kFiniteVectors _ f.2.2⟩

theorem twK_apply_coe {s : ℝ} {ds es : List RealBlock}
    (hχ : ∀ i : Fin r, ∀ x : ℝˣ, realPositionCharacter es i x =
      realPositionCharacter ds i x * ((|(x : ℝ)| : ℝ) : ℂ) ^ (s : ℂ))
    (hind : ∀ p d', realInducedBlockAt es p = some d' →
      ∃ d, realInducedBlockAt ds p = some d ∧ d.weight = d'.weight) (f : KFin r ds)
    (g : Langlands.GeneralLinear r ℝ) :
    (twK hχ hind f : Langlands.GeneralLinear r ℝ → ℂ) g =
      detPow r s g * (f : Langlands.GeneralLinear r ℝ → ℂ) g :=
  rfl

/-- The hypotheses of `twK` for `ds` and its twist `ds.map (realBlockTwist s)`. -/
theorem twist_char (s : ℝ) {ds : List RealBlock} (hr : realRank ds = r) (i : Fin r) (x : ℝˣ) :
    realPositionCharacter (ds.map (realBlockTwist s)) i x =
      realPositionCharacter ds i x * ((|(x : ℝ)| : ℝ) : ℂ) ^ (s : ℂ) :=
  realPositionCharacter_map_twist s ds i (hr ▸ i.isLt) x

theorem twist_ind (s : ℝ) (ds : List RealBlock) (p : ℕ) (d' : ComplexCharacterData)
    (hd' : realInducedBlockAt (ds.map (realBlockTwist s)) p = some d') :
    ∃ d, realInducedBlockAt ds p = some d ∧ d.weight = d'.weight := by
  rw [realInducedBlockAt_map_twist, Option.map_eq_some_iff] at hd'
  obtain ⟨d, hd, rfl⟩ := hd'
  exact ⟨d, hd, rfl⟩

theorem untwist_char (s : ℝ) {ds : List RealBlock} (hr : realRank ds = r) (i : Fin r)
    (x : ℝˣ) :
    realPositionCharacter ds i x =
      realPositionCharacter (ds.map (realBlockTwist s)) i x *
        ((|(x : ℝ)| : ℝ) : ℂ) ^ ((-s : ℝ) : ℂ) := by
  rw [twist_char s hr, mul_assoc, ← Complex.cpow_add _ _ (ofReal_abs_units_ne_zero x)]
  push_cast
  rw [add_neg_cancel, Complex.cpow_zero, mul_one]

theorem untwist_ind (s : ℝ) (ds : List RealBlock) (p : ℕ) (d : ComplexCharacterData)
    (hd : realInducedBlockAt ds p = some d) :
    ∃ d', realInducedBlockAt (ds.map (realBlockTwist s)) p = some d' ∧ d'.weight = d.weight :=
  ⟨characterOfParams d.weight (d.exponent + s), by rw [realInducedBlockAt_map_twist, hd]; rfl,
    characterOfParams_weight _ _⟩

end Twist

/-! ## Restriction to the middle block -/

section Restriction

open GramFormula

variable {n a r : ℕ} {pre core post : List RealBlock}

/-- The twist exponent `c = (rank post - rank pre)/2` of the statement. -/
def twistExp (pre post : List RealBlock) : ℝ :=
  ((realRank post : ℝ) - (realRank pre : ℝ)) / 2

/-- The twisted list `core'` of the statement. -/
abbrev twisted (pre core post : List RealBlock) : List RealBlock :=
  core.map (realBlockTwist (twistExp pre post))

theorem realRank_twisted : realRank (twisted pre core post) = realRank core :=
  realRank_map_realBlockTwist _ _

theorem sliceExponent_eq (hn : realRank (pre ++ core ++ post) = n) (ha : realRank pre = a)
    (hr : realRank core = r) : sliceExponent n a r = ((twistExp pre post : ℝ) : ℂ) := by
  subst ha hr
  rw [← hn, realRank_append', realRank_append']
  unfold sliceExponent twistExp
  push_cast
  ring

/-- **Restriction** `Res F (g) = F(ι g)`, from the `O(n)`-finite functions of the standard module
of `pre ++ core ++ post` to the `O(r)`-finite functions of that of the twisted list. -/
def res (h : a + r ≤ n) (ha : realRank pre = a) (hr : realRank core = r) :
    KFin n (pre ++ core ++ post) →ₗ[ℂ] KFin r (twisted pre core post) :=
  twK (twist_char (twistExp pre post) hr) (twist_ind (twistExp pre post) core) ∘ₗ
    sliceK h ha hr 1

variable (h : a + r ≤ n) (ha : realRank pre = a) (hr : realRank core = r)
  (hn : realRank (pre ++ core ++ post) = n)

include hn in
theorem res_apply (F : KFin n (pre ++ core ++ post)) (g : Langlands.GeneralLinear r ℝ) :
    (res h ha hr F : Langlands.GeneralLinear r ℝ → ℂ) g =
      (F : Langlands.GeneralLinear n ℝ → ℂ) (blockEmb h g) := by
  rw [res, LinearMap.comp_apply, twK_apply_coe, sliceK_apply_coe, slice_apply,
    OneMemClass.coe_one, mul_one, ← mul_assoc, sliceFactor_eq_detPow,
    sliceExponent_eq hn ha hr, detPow_mul_detPow_neg, one_mul]

include hn in
theorem coe_res (F : KFin n (pre ++ core ++ post)) :
    (res h ha hr F : Langlands.GeneralLinear r ℝ → ℂ) =
      fun g => (F : Langlands.GeneralLinear n ℝ → ℂ) (blockEmb h g) :=
  funext fun g => res_apply h ha hr hn F g

include hn in
/-- `Res ∘ R(P Z Pᵀ) = R(Z) ∘ Res`. -/
theorem res_lie_mid (Z : Matrix (Fin r) (Fin r) ℝ) (F : KFin n (pre ++ core ++ post)) :
    res h ha hr (lie n (pre ++ core ++ post) (embMat n a r * Z * (embMat n a r)ᵀ) F) =
      lie r (twisted pre core post) Z (res h ha hr F) := by
  apply Subtype.ext
  rw [coe_res h ha hr hn, lie_apply_coe, lie_apply_coe, coe_res h ha hr hn]
  funext g
  exact (rightDerivative_comp_blockEmb h F.2.1.1.1 Z g).symm

include hn in
theorem res_pow_lie_mid (Z : Matrix (Fin r) (Fin r) ℝ) (k : ℕ)
    (F : KFin n (pre ++ core ++ post)) :
    res h ha hr ((lie n (pre ++ core ++ post) (embMat n a r * Z * (embMat n a r)ᵀ) ^ k) F) =
      (lie r (twisted pre core post) Z ^ k) (res h ha hr F) := by
  induction k generalizing F with
  | zero => rfl
  | succ k ih =>
    rw [pow_succ, pow_succ, Module.End.mul_apply, Module.End.mul_apply, ih,
      res_lie_mid h ha hr hn]

/-- `Res ∘ R(A) = (∑ αᵢ Aᵢᵢ) Res` for `A` upper triangular and zero on the middle block. -/
theorem res_lie_upper {A : Matrix (Fin n) (Fin n) ℝ} (hA1 : ∀ i j : Fin n, j < i → A i j = 0)
    (hA2 : ∀ i j : Fin n, IsMid a r i → IsMid a r j → A i j = 0)
    (F : KFin n (pre ++ core ++ post)) :
    res h ha hr (lie n (pre ++ core ++ post) A F) =
      (∑ i : Fin n, (realPositionExponent (pre ++ core ++ post) i + ((n : ℂ) - 1) / 2 -
        ((i : ℕ) : ℂ)) * (A i i : ℂ)) • res h ha hr F := by
  have hs : sliceK h ha hr 1 (lie n (pre ++ core ++ post) A F) =
      (∑ i : Fin n, (realPositionExponent (pre ++ core ++ post) i + ((n : ℂ) - 1) / 2 -
        ((i : ℕ) : ℂ)) * (A i i : ℂ)) • sliceK h ha hr 1 F := by
    apply Subtype.ext
    rw [Submodule.coe_smul, sliceK_one_apply_coe, sliceK_one_apply_coe, lie_apply_coe]
    exact slice_rightDerivative_upper h (fun i x => realPositionCharacter_exp _ i x) F.2.1.1
      hA1 hA2
  rw [res, LinearMap.comp_apply, hs, map_smul, LinearMap.comp_apply]

theorem apply_blockEmb_mul_diagonalUnits {χ : ℕ → ℝˣ → ℂ} {G : Langlands.GeneralLinear n ℝ → ℂ}
    (hG : G ∈ principalSeries ℝ n χ) (t : Fin n → ℝˣ) (g : Langlands.GeneralLinear r ℝ) :
    G (blockEmb h g * Iwasawa.diagonalUnits t) =
      principalSeriesCharacter ℝ n χ (outUnits a r t) *
        G (blockEmb h (g * Iwasawa.diagonalUnits (midUnits h t))) := by
  have harg : blockEmb h g * (Iwasawa.diagonalUnits t : Langlands.GeneralLinear n ℝ) =
      (Iwasawa.diagonalUnits (outUnits a r t) : Langlands.GeneralLinear n ℝ) *
        ((1 : upperUnipotent n ℝ) : Langlands.GeneralLinear n ℝ) *
        blockEmb h (g * Iwasawa.diagonalUnits (midUnits h t)) := by
    rw [diagonalUnits_eq_mul h t, map_mul, OneMemClass.coe_one, mul_one, ← mul_assoc,
      ← diagonalUnits_outUnits_mul_blockEmb, mul_assoc]
  rw [harg, hG.2]

include hn in
/-- `Res (R(diag t) F) (g) = χ(t_out) Res F (g diag(t_mid))`. -/
theorem res_rep_apply (κ : Matrix.unitaryGroup (Fin n) ℝ) (t : Fin n → ℝˣ)
    (hκ : (Unitary.toUnits κ : Langlands.GeneralLinear n ℝ) = Iwasawa.diagonalUnits t)
    (F : KFin n (pre ++ core ++ post)) (g : Langlands.GeneralLinear r ℝ) :
    (res h ha hr (realStandardRep n (pre ++ core ++ post) κ F) : Langlands.GeneralLinear r ℝ → ℂ) g =
      principalSeriesCharacter ℝ n (realPositionCharacter (pre ++ core ++ post)) (outUnits a r t) *
        (res h ha hr F : Langlands.GeneralLinear r ℝ → ℂ) (g * Iwasawa.diagonalUnits (midUnits h t)) := by
  rw [res_apply h ha hr hn, res_apply h ha hr hn, realStandardRep_apply_coe]
  change (F : Langlands.GeneralLinear n ℝ → ℂ) (blockEmb h g * Unitary.toUnits κ) = _
  rw [hκ]
  exact apply_blockEmb_mul_diagonalUnits h F.2.1.1 t g

end Restriction

/-! ## The Jacquet functional `ℓ' ∘ Res` -/

section Transfer

open GramFormula RealStrictCharacterLanglandsQuotient

variable {n a r : ℕ}

/-- `P E_{kl} Pᵀ = E_{ι k, ι l}`. -/
theorem embMat_single_transpose (h : a + r ≤ n) (k l : Fin r) :
    embMat n a r * Matrix.single k l (1 : ℝ) * (embMat n a r)ᵀ =
      Matrix.single (idx h k) (idx h l) 1 := by
  ext i j
  by_cases hi : IsMid a r i
  · obtain ⟨k', rfl⟩ := exists_idx_of_isMid h hi
    by_cases hj : IsMid a r j
    · obtain ⟨l', rfl⟩ := exists_idx_of_isMid h hj
      rw [mid_apply_idx h]
      simp only [Matrix.single_apply, (idx_injective h).eq_iff]
    · have hne : idx h l ≠ j := fun e => hj (e ▸ isMid_idx h l)
      rw [mid_apply_of_not_isMid_right _ _ hj, Matrix.single_apply_of_col_ne _ _ hne]
  · have hne : idx h k ≠ i := fun e => hi (e ▸ isMid_idx h k)
    rw [mid_apply_of_not_isMid_left _ hi, Matrix.single_apply_of_row_ne hne]

/-- `P (Pᵀ X P) Pᵀ` is `X` on the middle block and `0` elsewhere. -/
theorem mid_midBlock_apply (h : a + r ≤ n) (X : Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) :
    (embMat n a r * midBlock n a r X * (embMat n a r)ᵀ) i j =
      if IsMid a r i ∧ IsMid a r j then X i j else 0 := by
  by_cases hi : IsMid a r i
  · obtain ⟨k, rfl⟩ := exists_idx_of_isMid h hi
    by_cases hj : IsMid a r j
    · obtain ⟨l, rfl⟩ := exists_idx_of_isMid h hj
      rw [mid_apply_idx h, midBlock_apply h, ite_eq_left ⟨hi, hj⟩]
    · rw [mid_apply_of_not_isMid_right _ _ hj, ite_eq_right fun hh => hj hh.2]
  · rw [mid_apply_of_not_isMid_left _ hi, ite_eq_right fun hh => hi hh.1]

theorem principalSeriesCharacter_one' {χ : ℕ → ℝˣ → ℂ} (h1 : ∀ i, χ i 1 = 1) :
    principalSeriesCharacter ℝ n χ 1 = 1 := by
  unfold principalSeriesCharacter
  simp [h1]

theorem outUnits_signVec_idx (h : a + r ≤ n) (j : Fin r) :
    outUnits a r (signVec (idx h j)) = 1 := by
  funext i
  by_cases hi : IsMid a r i
  · simp [outUnits, hi]
  · have hne : i ≠ idx h j := fun e => hi (e ▸ isMid_idx h j)
    simp [outUnits, hi, signVec, hne]

theorem midUnits_signVec_idx (h : a + r ≤ n) (j : Fin r) :
    midUnits h (signVec (idx h j)) = signVec j := by
  funext j'
  simp [midUnits, signVec, (idx_injective h).eq_iff]

theorem outUnits_signVec_of_not_isMid {j : Fin n} (hj : ¬IsMid a r j) :
    outUnits a r (signVec j) = signVec j := by
  funext i
  by_cases hi : IsMid a r i
  · have hne : i ≠ j := fun e => hj (e ▸ hi)
    simp [outUnits, hi, signVec, hne]
  · simp [outUnits, hi]

theorem midUnits_signVec_of_not_isMid (h : a + r ≤ n) {j : Fin n} (hj : ¬IsMid a r j) :
    midUnits h (signVec j) = 1 := by
  funext j'
  have hne : idx h j' ≠ j := fun e => hj (e ▸ isMid_idx h j')
  simp [midUnits, signVec, hne]

/-- The exponents of `ℓ' ∘ Res`: `a'` on the middle block, `αᵢ = τᵢ + (n - 1)/2 - i` outside. -/
def resExp (a r : ℕ) (L : List RealBlock) (a' : Fin r → ℂ) (i : Fin n) : ℂ :=
  if hi : IsMid a r i then a' ⟨(i : ℕ) - a, by unfold IsMid at hi; omega⟩
  else realPositionExponent L i + ((n : ℂ) - 1) / 2 - ((i : ℕ) : ℂ)

/-- The signs of `ℓ' ∘ Res`: `e'` on the middle block, the sign of `χᵢ(-1)` outside. -/
def resSign (a r : ℕ) (L : List RealBlock) (e' : Fin r → Fin 2) (i : Fin n) : Fin 2 :=
  if hi : IsMid a r i then e' ⟨(i : ℕ) - a, by unfold IsMid at hi; omega⟩
  else if realPositionCharacter L i (-1) = 1 then 0 else 1

theorem resExp_idx (h : a + r ≤ n) (L : List RealBlock) (a' : Fin r → ℂ) (j : Fin r) :
    resExp a r L a' (idx h j) = a' j := by
  rw [resExp, dite_eq_left (isMid_idx h j)]
  congr 1
  ext
  simp [idx_val]

theorem resSign_idx (h : a + r ≤ n) (L : List RealBlock) (e' : Fin r → Fin 2) (j : Fin r) :
    resSign a r L e' (idx h j) = e' j := by
  rw [resSign, dite_eq_left (isMid_idx h j)]
  congr 1
  ext
  simp [idx_val]

theorem neg_one_pow_resSign {L : List RealBlock} (e' : Fin r → Fin 2) {i : Fin n}
    (hi : ¬IsMid a r i) :
    (-1 : ℂ) ^ (resSign a r L e' i).val = realPositionCharacter L i (-1) := by
  rw [resSign, dite_eq_right hi]
  rcases realPositionCharacter_neg_one L i with h1 | h1
  · rw [ite_eq_left h1, h1]
    rfl
  · rw [ite_eq_right (by rw [h1]; norm_num), h1]
    simp

variable {pre core post : List RealBlock}
  (h : a + r ≤ n) (ha : realRank pre = a) (hr : realRank core = r)
  (hn : realRank (pre ++ core ++ post) = n)

include hn in
/-- `Res ∘ ρ(s_{ι j}) = ρ(s_j) ∘ Res`. -/
theorem res_sign_mid (j : Fin r) (F : KFin n (pre ++ core ++ post)) :
    res h ha hr (realStandardRep n (pre ++ core ++ post) (signReflection n (idx h j)) F) =
      realStandardRep r (twisted pre core post) (signReflection r j) (res h ha hr F) := by
  apply Subtype.ext
  funext g
  rw [res_rep_apply h ha hr hn _ _ (toUnits_signReflection _), outUnits_signVec_idx,
    principalSeriesCharacter_one' (realPositionCharacter_one _), one_mul,
    midUnits_signVec_idx, realStandardRep_apply_coe]
  change _ = (res h ha hr F : Langlands.GeneralLinear r ℝ → ℂ) (g * Unitary.toUnits _)
  rw [toUnits_signReflection]

include hn in
/-- `Res ∘ ρ(s_i) = χᵢ(-1) Res` for `i` outside the middle block. -/
theorem res_sign_out {i : Fin n} (hi : ¬IsMid a r i) (F : KFin n (pre ++ core ++ post)) :
    res h ha hr (realStandardRep n (pre ++ core ++ post) (signReflection n i) F) =
      realPositionCharacter (pre ++ core ++ post) i (-1) • res h ha hr F := by
  apply Subtype.ext
  funext g
  rw [res_rep_apply h ha hr hn _ _ (toUnits_signReflection _), outUnits_signVec_of_not_isMid hi,
    principalSeriesCharacter_signVec (realPositionCharacter_one _),
    midUnits_signVec_of_not_isMid h hi, map_one, mul_one]
  rfl

include hn in
/-- The real Jacquet functional `ℓ' ∘ Res`: if `ℓ'` is a real Jacquet functional with
exponents `a'` and signs `e'` on the twisted list, then `ℓ' ∘ Res` is one with exponents
`resExp` and signs `resSign`. -/
theorem isRealJacquetFunctional_comp_res {ℓ' : KFin r (twisted pre core post) →ₗ[ℂ] ℂ}
    {a' : Fin r → ℂ} {e' : Fin r → Fin 2}
    (hJ : IsRealJacquetFunctional r (realStandardRep r (twisted pre core post))
      (realStandardLie r (twisted pre core post)) ℓ' a' e') :
    IsRealJacquetFunctional n (realStandardRep n (pre ++ core ++ post))
      (realStandardLie n (pre ++ core ++ post)) (ℓ' ∘ₗ res h ha hr)
      (resExp a r (pre ++ core ++ post) a') (resSign a r (pre ++ core ++ post) e') := by
  refine ⟨fun X hX v => ?_, fun j v => ⟨?_, ?_⟩⟩
  · set Z := midBlock n a r X with hZ
    set Xo := X - embMat n a r * Z * (embMat n a r)ᵀ with hXo
    have hXo_apply : ∀ i j : Fin n, Xo i j = X i j - if IsMid a r i ∧ IsMid a r j then X i j else 0 :=
      fun i j => by rw [hXo, Matrix.sub_apply, hZ, mid_midBlock_apply h]
    have hsplit : X = Xo + embMat n a r * Z * (embMat n a r)ᵀ := by
      rw [hXo, sub_add_cancel]
    have hlow : ∀ i j : Fin n, j < i → Xo i j = 0 := fun i j hij => by
      rw [hXo_apply, hX i j (le_of_lt hij)]
      split_ifs <;> simp
    have hmid : ∀ i j : Fin n, IsMid a r i → IsMid a r j → Xo i j = 0 := fun i j hi hj => by
      rw [hXo_apply, ite_eq_left ⟨hi, hj⟩, sub_self]
    have hdiag : ∀ i : Fin n, Xo i i = 0 := fun i => by
      rw [hXo_apply, hX i i le_rfl]
      split_ifs <;> simp
    have hZu : ∀ k l : Fin r, (l : ℕ) ≤ k → Z k l = 0 := fun k l hlk => by
      rw [hZ, midBlock_apply h]
      exact hX _ _ (by simp only [idx_val]; omega)
    change ℓ' (res h ha hr (lie n (pre ++ core ++ post) X v)) = 0
    rw [hsplit, lie_add, LinearMap.add_apply, map_add, map_add,
      res_lie_upper h ha hr hlow hmid, res_lie_mid h ha hr hn]
    simp only [hdiag, Complex.ofReal_zero, mul_zero, Finset.sum_const_zero, zero_smul, map_zero,
      zero_add]
    exact hJ.1 Z hZu _
  · change ℓ' (res h ha hr (lie n (pre ++ core ++ post) (Matrix.single j j 1) v)) =
      resExp a r (pre ++ core ++ post) a' j * ℓ' (res h ha hr v)
    by_cases hj : IsMid a r j
    · obtain ⟨j', rfl⟩ := exists_idx_of_isMid h hj
      rw [← embMat_single_transpose h, res_lie_mid h ha hr hn, resExp_idx]
      exact (hJ.2 j' _).1
    · have hA1 : ∀ i i' : Fin n, i' < i → Matrix.single j j (1 : ℝ) i i' = 0 := fun i i' hii' => by
        rw [Matrix.single_apply, ite_eq_right]
        rintro ⟨rfl, rfl⟩
        exact lt_irrefl _ hii'
      have hA2 : ∀ i i' : Fin n, IsMid a r i → IsMid a r i' → Matrix.single j j (1 : ℝ) i i' = 0 :=
        fun i i' hi _ =>
          Matrix.single_apply_of_row_ne (fun e : j = i => hj (by rw [e]; exact hi)) _ _ _
      rw [res_lie_upper h ha hr hA1 hA2, map_smul, smul_eq_mul, resExp, dite_eq_right hj]
      congr 1
      rw [Finset.sum_eq_single j]
      · rw [Matrix.single_apply_same, Complex.ofReal_one, mul_one]
      · intro i _ hij
        rw [Matrix.single_apply_of_row_ne (Ne.symm hij), Complex.ofReal_zero, mul_zero]
      · simp
  · change ℓ' (res h ha hr (realStandardRep n (pre ++ core ++ post) (signReflection n j) v)) =
      (-1) ^ (resSign a r (pre ++ core ++ post) e' j).val * ℓ' (res h ha hr v)
    by_cases hj : IsMid a r j
    · obtain ⟨j', rfl⟩ := exists_idx_of_isMid h hj
      rw [res_sign_mid h ha hr hn, resSign_idx]
      exact (hJ.2 j' _).2
    · rw [res_sign_out h ha hr hn hj, map_smul, smul_eq_mul, neg_one_pow_resSign e' hj]

include hn in
/-- **Transfer.** If `ℓ'` satisfies the conclusion of `RealLinkedJacquetFunctionalExists` for the
twisted list and `ℓ' ∘ Res ≠ 0`, then `ℓ' ∘ Res` satisfies it for `pre ++ core ++ post`, at the
position `a + p'`. -/
theorem exists_of_res_ne_zero {ℓ' : KFin r (twisted pre core post) →ₗ[ℂ] ℂ} {a' : Fin r → ℂ}
    {e' : Fin r → Fin 2} {p' k : ℕ} (hp' : p' + 1 < r)
    (hJ : IsRealJacquetFunctional r (realStandardRep r (twisted pre core post))
      (realStandardLie r (twisted pre core post)) ℓ' a' e')
    (hδ : a' ⟨p', Nat.lt_of_succ_lt hp'⟩ - a' ⟨p' + 1, hp'⟩ = 1 - (k : ℂ))
    (hk : ∀ v : KFin r (twisted pre core post),
      ℓ' ((realStandardLie r (twisted pre core post)
        (1 ⊗ₜ Matrix.single (⟨p' + 1, hp'⟩ : Fin r) ⟨p', Nat.lt_of_succ_lt hp'⟩ (1 : ℝ)) ^ k)
          v) = 0)
    (hne : ℓ' ∘ₗ res h ha hr ≠ 0) :
    RealLinkedJacquetFunctionalExists n (pre ++ core ++ post) := by
  have hp : a + p' + 1 < n := by omega
  have e0 : (⟨a + p', Nat.lt_of_succ_lt hp⟩ : Fin n) = idx h ⟨p', Nat.lt_of_succ_lt hp'⟩ :=
    Fin.ext rfl
  have e1 : (⟨a + p' + 1, hp⟩ : Fin n) = idx h ⟨p' + 1, hp'⟩ := Fin.ext rfl
  refine ⟨ℓ' ∘ₗ res h ha hr, resExp a r (pre ++ core ++ post) a',
    resSign a r (pre ++ core ++ post) e', a + p', k, hp, hne,
    isRealJacquetFunctional_comp_res h ha hr hn hJ, ?_, fun v => ?_⟩
  · rw [e0, e1, resExp_idx, resExp_idx, hδ]
  · change ℓ' (res h ha hr ((lie n (pre ++ core ++ post)
      (Matrix.single (⟨a + p' + 1, hp⟩ : Fin n) ⟨a + p', Nat.lt_of_succ_lt hp⟩ 1) ^ k) v)) = 0
    rw [e0, e1, ← embMat_single_transpose h, res_pow_lie_mid h ha hr hn]
    exact hk _

end Transfer

/-! ## Surjectivity of the restriction -/

section Surjective

variable {n a r : ℕ} {pre core post : List RealBlock}

/-- Multiplication by `|det|^{-c}`, the inverse of the twist in `res`. -/
def untwK (hr : realRank core = r) : KFin r (twisted pre core post) →ₗ[ℂ] KFin r core :=
  twK (untwist_char (twistExp pre post) hr) (untwist_ind (twistExp pre post) core)

theorem twK_untwK (hr : realRank core = r) (f : KFin r (twisted pre core post)) :
    twK (twist_char (twistExp pre post) hr) (twist_ind (twistExp pre post) core)
      (untwK (pre := pre) (post := post) hr f) = f := by
  apply Subtype.ext
  funext g
  rw [twK_apply_coe, untwK, twK_apply_coe, ← mul_assoc, Complex.ofReal_neg,
    detPow_mul_detPow_neg, one_mul]

/-- **Restriction is onto.** -/
theorem res_surjective (h : a + r ≤ n) (ha : realRank pre = a) (hr : realRank core = r)
    (hn : realRank (pre ++ core ++ post) = n) :
    Function.Surjective (res (post := post) h ha hr) := by
  intro f
  obtain ⟨F, hF⟩ := RealSliceSurjective.sliceK_one_surjective (post := post) h ha hr hn
    (untwK (pre := pre) (post := post) hr f)
  refine ⟨F, ?_⟩
  rw [res, LinearMap.comp_apply, hF, twK_untwK]

end Surjective

end RealLinkedJacquetStages

open Langlands.LocalFactor.Archimedean InductionStages RealLinkedJacquetStages in
/-- **Induction in stages** for the linked real Jacquet functional: a functional as in
`RealLinkedJacquetFunctionalExists` for the twisted middle list `core'` gives one for
`pre ++ core ++ post`, namely `ℓ' ∘ Res`. -/
theorem realLinkedJacquetFunctionalInStages : RealLinkedJacquetFunctionalInStagesStatement := by
  intro n pre core post hn hex
  obtain ⟨ℓ', a', e', p', k, hp', hne', hJ, hδ, hk⟩ := hex
  have h : realRank pre + realRank core ≤ n := by
    rw [← hn, realRank_append', realRank_append']
    omega
  refine exists_of_res_ne_zero (pre := pre) (core := core) (post := post) h rfl rfl hn hp' hJ hδ
    hk fun h0 => hne' (LinearMap.ext fun v => ?_)
  obtain ⟨F, rfl⟩ := res_surjective h rfl rfl hn v
  exact LinearMap.congr_fun h0 F

end Langlands.Archimedean
