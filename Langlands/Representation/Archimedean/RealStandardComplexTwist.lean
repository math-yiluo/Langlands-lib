import Langlands.Representation.Archimedean.RealTemperedTwist

/-!
# Complex determinant twists of real standard modules

For a complex number `s`, multiplication by `|det g|^s` identifies the `O(n)`-finite functions
of the real standard module of a list of blocks `ds` with those of the list in which `s` is
added to every block exponent. It commutes with right translation by `O(n)` and changes each
right derivative by the scalar derivative of `|det|^s` at the identity. See the paired
Markdown.
-/

noncomputable section

open scoped TensorProduct Matrix Manifold ContDiff Matrix.Norms.Operator

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Archimedean

attribute [local instance 100] LieRing.ofAssociativeRing

namespace RealComplexTwist

open Langlands.LocalFactor.Archimedean
open InductionStages RealLinkedJacquetStages

/-! ## Twisting blocks by a complex exponent -/

/-- The real block `x` twisted by `|det|^c` for a complex `c`: the exponent `t` of the block
becomes `t + c`; the parity of a character block and the weight of an induction block stay. -/
def realBlockComplexTwist (c : ℂ) : RealBlock → RealBlock
  | .character d => .character (RealJacquetFrobenius.charData d.parity (d.exponent + c))
  | .induced d => .induced (characterOfParams d.weight (d.exponent + c))

/-- For a real exponent this is the published `realBlockTwist`. -/
theorem realBlockComplexTwist_ofReal (c : ℝ) :
    realBlockComplexTwist (c : ℂ) = realBlockTwist c := by
  funext x
  cases x <;> rfl

@[simp]
theorem realBlockComplexTwist_rank (c : ℂ) (x : RealBlock) :
    (realBlockComplexTwist c x).rank = x.rank := by
  cases x <;> rfl

theorem realRank_map_realBlockComplexTwist (c : ℂ) (l : List RealBlock) :
    realRank (l.map (realBlockComplexTwist c)) = realRank l := by
  induction l with
  | nil => rfl
  | cons x l ih =>
      rw [List.map_cons, realRank_cons, realRank_cons, ih, realBlockComplexTwist_rank]

section TwistLists

open GramFormula

/-- The position characters of a twisted list are those of the list times `|·|^s`. -/
theorem realPositionCharacter_map_complexTwist (s : ℂ) : ∀ (ds : List RealBlock) (i : ℕ),
    i < realRank ds → ∀ x : ℝˣ,
      realPositionCharacter (ds.map (realBlockComplexTwist s)) i x =
        realPositionCharacter ds i x * ((|(x : ℝ)| : ℝ) : ℂ) ^ s
  | [], i, h, _ => by simp at h
  | .character c :: _, 0, _, x => by
      simp only [List.map_cons, realBlockComplexTwist, realPositionCharacter,
        RealJacquetFrobenius.charData_character_apply, RealJacquetFrobenius.charFun]
      rw [c.character_eq, Complex.cpow_add _ _ (ofReal_abs_units_ne_zero x)]
      ring
  | .character _ :: ds, i + 1, h, x => by
      rw [realRank_cons, rank_character] at h
      exact realPositionCharacter_map_complexTwist s ds i (by omega) x
  | .induced d :: _, 0, _, x => by
      simp only [List.map_cons, realBlockComplexTwist, realPositionCharacter,
        realInducedFirstCharacter, characterOfParams_weight, characterOfParams_exponent]
      rw [show d.exponent + s + (d.weight.natAbs : ℂ) / 2 =
          (d.exponent + (d.weight.natAbs : ℂ) / 2) + s by ring,
        Complex.cpow_add _ _ (ofReal_abs_units_ne_zero x)]
      ring
  | .induced d :: _, 1, _, x => by
      simp only [List.map_cons, realBlockComplexTwist, realPositionCharacter,
        realInducedSecondCharacter, characterOfParams_weight, characterOfParams_exponent]
      rw [show d.exponent + s - (d.weight.natAbs : ℂ) / 2 =
          (d.exponent - (d.weight.natAbs : ℂ) / 2) + s by ring,
        Complex.cpow_add _ _ (ofReal_abs_units_ne_zero x)]
  | .induced _ :: ds, i + 2, h, x => by
      rw [realRank_cons, rank_induced] at h
      exact realPositionCharacter_map_complexTwist s ds i (by omega) x

/-- The induction blocks of a twisted list. -/
theorem realInducedBlockAt_map_complexTwist (s : ℂ) : ∀ (ds : List RealBlock) (p : ℕ),
    realInducedBlockAt (ds.map (realBlockComplexTwist s)) p =
      (realInducedBlockAt ds p).map fun d => characterOfParams d.weight (d.exponent + s)
  | [], _ => rfl
  | .character _ :: _, 0 => rfl
  | .character _ :: ds, p + 1 => realInducedBlockAt_map_complexTwist s ds p
  | .induced _ :: _, 0 => rfl
  | .induced _ :: _, 1 => rfl
  | .induced _ :: ds, p + 2 => realInducedBlockAt_map_complexTwist s ds p

end TwistLists

/-! ## Multiplication by `|det|^s` on standard modules -/

section Twist

variable {r : ℕ}

/-- Let `es` be a list of rank `r` whose position characters are those of `ds` times `|·|^s`
and whose induction blocks have the weights of those of `ds`. Then `|det|^s` maps the standard
module of `ds` into that of `es`. -/
theorem detPowMul_mem_realStandardModule {s : ℂ} {ds es : List RealBlock}
    (hχ : ∀ i : Fin r, ∀ x : ℝˣ, realPositionCharacter es i x =
      realPositionCharacter ds i x * ((|(x : ℝ)| : ℝ) : ℂ) ^ s)
    (hind : ∀ p d', realInducedBlockAt es p = some d' →
      ∃ d, realInducedBlockAt ds p = some d ∧ d.weight = d'.weight)
    {f : Langlands.GeneralLinear r ℝ → ℂ} (hf : f ∈ realStandardModule r ds) :
    detPowMul r s f ∈ realStandardModule r es := by
  refine ⟨⟨contMDiff_mul_fun (contMDiff_detPow s) hf.1.1, fun t u g => ?_⟩,
    fun p d' hd' k hk g => ?_⟩
  · have hu : detPow r s (u : Langlands.GeneralLinear r ℝ) = 1 :=
      detPow_of_mem_upperUnipotent _ u.2
    rw [detPowMul_apply, detPowMul_apply, hf.1.2 t u g, detPow_mul, detPow_mul, hu, mul_one,
      detPow_diagonalUnits]
    have hP : principalSeriesCharacter ℝ r (realPositionCharacter es) t =
        principalSeriesCharacter ℝ r (realPositionCharacter ds) t *
          ∏ j, ((|((t j : ℝˣ) : ℝ)| : ℝ) : ℂ) ^ s := by
      unfold principalSeriesCharacter
      rw [← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun j _ => ?_
      rw [hχ j (t j)]
      ring
    rw [hP]
    ring
  · obtain ⟨d, hd, hw⟩ := hind p d' hd'
    rw [blockFourierCoefficient_detPowMul, hf.2 p d hd k (by rw [hw]; exact hk) g, mul_zero]

/-- Multiplication by `|det|^s` from the `O(r)`-finite functions of the standard module of `ds`
to those of `es`, under the hypotheses of `detPowMul_mem_realStandardModule`. -/
def detPowK {s : ℂ} {ds es : List RealBlock}
    (hχ : ∀ i : Fin r, ∀ x : ℝˣ, realPositionCharacter es i x =
      realPositionCharacter ds i x * ((|(x : ℝ)| : ℝ) : ℂ) ^ s)
    (hind : ∀ p d', realInducedBlockAt es p = some d' →
      ∃ d, realInducedBlockAt ds p = some d ∧ d.weight = d'.weight) :
    KFin r ds →ₗ[ℂ] KFin r es :=
  ((detPowMul r s).comp (KFin r ds).subtype).codRestrict _ fun f =>
    ⟨detPowMul_mem_realStandardModule hχ hind f.2.1, detPowMul_mem_kFiniteVectors _ f.2.2⟩

theorem detPowK_apply_coe {s : ℂ} {ds es : List RealBlock}
    (hχ : ∀ i : Fin r, ∀ x : ℝˣ, realPositionCharacter es i x =
      realPositionCharacter ds i x * ((|(x : ℝ)| : ℝ) : ℂ) ^ s)
    (hind : ∀ p d', realInducedBlockAt es p = some d' →
      ∃ d, realInducedBlockAt ds p = some d ∧ d.weight = d'.weight) (f : KFin r ds)
    (g : Langlands.GeneralLinear r ℝ) :
    (detPowK hχ hind f : Langlands.GeneralLinear r ℝ → ℂ) g =
      detPow r s g * (f : Langlands.GeneralLinear r ℝ → ℂ) g :=
  rfl

/-- The hypotheses of `detPowK` for `ds` and its twist `ds.map (realBlockComplexTwist s)`. -/
theorem twist_char (s : ℂ) {ds : List RealBlock} (hr : realRank ds = r) (i : Fin r) (x : ℝˣ) :
    realPositionCharacter (ds.map (realBlockComplexTwist s)) i x =
      realPositionCharacter ds i x * ((|(x : ℝ)| : ℝ) : ℂ) ^ s :=
  realPositionCharacter_map_complexTwist s ds i (hr ▸ i.isLt) x

theorem twist_ind (s : ℂ) (ds : List RealBlock) (p : ℕ) (d' : ComplexCharacterData)
    (hd' : realInducedBlockAt (ds.map (realBlockComplexTwist s)) p = some d') :
    ∃ d, realInducedBlockAt ds p = some d ∧ d.weight = d'.weight := by
  rw [realInducedBlockAt_map_complexTwist, Option.map_eq_some_iff] at hd'
  obtain ⟨d, hd, rfl⟩ := hd'
  exact ⟨d, hd, rfl⟩

theorem untwist_char (s : ℂ) {ds : List RealBlock} (hr : realRank ds = r) (i : Fin r)
    (x : ℝˣ) :
    realPositionCharacter ds i x =
      realPositionCharacter (ds.map (realBlockComplexTwist s)) i x *
        ((|(x : ℝ)| : ℝ) : ℂ) ^ (-s) := by
  rw [twist_char s hr, mul_assoc, ← Complex.cpow_add _ _ (ofReal_abs_units_ne_zero x),
    add_neg_cancel, Complex.cpow_zero, mul_one]

theorem untwist_ind (s : ℂ) (ds : List RealBlock) (p : ℕ) (d : ComplexCharacterData)
    (hd : realInducedBlockAt ds p = some d) :
    ∃ d', realInducedBlockAt (ds.map (realBlockComplexTwist s)) p = some d' ∧
      d'.weight = d.weight :=
  ⟨characterOfParams d.weight (d.exponent + s),
    by rw [realInducedBlockAt_map_complexTwist, hd]; rfl, characterOfParams_weight _ _⟩

end Twist

/-! ## The twist equivalence -/

variable {n : ℕ}

/-- Multiplication by `|det|^s`, with inverse multiplication by `|det|^(-s)`, from the
`O(n)`-finite functions of the standard module of `ds` to those of its twist by `s`. -/
def twistEquiv (s : ℂ) (ds : List RealBlock) (hr : realRank ds = n) :
    KFin n ds ≃ₗ[ℂ] KFin n (ds.map (realBlockComplexTwist s)) where
  toLinearMap := detPowK (twist_char s hr) (twist_ind s ds)
  invFun := detPowK (untwist_char s hr) (untwist_ind s ds)
  left_inv f := by
    apply Subtype.ext
    funext g
    change detPow n (-s) g * (detPow n s g * (f : Langlands.GeneralLinear n ℝ → ℂ) g) =
      (f : Langlands.GeneralLinear n ℝ → ℂ) g
    rw [← mul_assoc, ← detPow_add, neg_add_cancel, detPow_zero, one_mul]
  right_inv f := by
    apply Subtype.ext
    funext g
    change detPow n s g * (detPow n (-s) g * (f : Langlands.GeneralLinear n ℝ → ℂ) g) =
      (f : Langlands.GeneralLinear n ℝ → ℂ) g
    rw [← mul_assoc, ← detPow_add, add_neg_cancel, detPow_zero, one_mul]

theorem twistEquiv_apply (s : ℂ) (ds : List RealBlock) (hr : realRank ds = n)
    (f : KFin n ds) (g : Langlands.GeneralLinear n ℝ) :
    (twistEquiv s ds hr f : Langlands.GeneralLinear n ℝ → ℂ) g =
      detPow n s g * (f : Langlands.GeneralLinear n ℝ → ℂ) g :=
  rfl

theorem twistEquiv_symm_apply (s : ℂ) (ds : List RealBlock) (hr : realRank ds = n)
    (f : KFin n (ds.map (realBlockComplexTwist s))) (g : Langlands.GeneralLinear n ℝ) :
    ((twistEquiv s ds hr).symm f : Langlands.GeneralLinear n ℝ → ℂ) g =
      detPow n (-s) g * (f : Langlands.GeneralLinear n ℝ → ℂ) g :=
  rfl

/-- The inverse twist commutes with right translation by `O(n)`. -/
theorem twistEquiv_symm_rightTranslation (s : ℂ) (ds : List RealBlock) (hr : realRank ds = n)
    {k : Langlands.GeneralLinear n ℝ} (hk : k ∈ unitaryCompact ℝ n)
    (f : KFin n (ds.map (realBlockComplexTwist s)))
    (hf : Whittaker.rightTranslation ℂ (Langlands.GeneralLinear n ℝ) k
      (f : Langlands.GeneralLinear n ℝ → ℂ) ∈ KFin n (ds.map (realBlockComplexTwist s)))
    (hf' : Whittaker.rightTranslation ℂ (Langlands.GeneralLinear n ℝ) k
      ((twistEquiv s ds hr).symm f : Langlands.GeneralLinear n ℝ → ℂ) ∈ KFin n ds) :
    (twistEquiv s ds hr).symm ⟨_, hf⟩ = ⟨_, hf'⟩ := by
  apply Subtype.ext
  funext g
  change detPow n (-s) g * (f : Langlands.GeneralLinear n ℝ → ℂ) (g * k) =
    detPow n (-s) (g * k) * (f : Langlands.GeneralLinear n ℝ → ℂ) (g * k)
  rw [detPow_mul, detPow_of_mem_unitaryCompact _ hk, mul_one]

/-- The real Lie action changes by the scalar derivative of `|det|^s` at the identity. -/
theorem twistEquiv_lie (s : ℂ) (ds : List RealBlock) (hr : realRank ds = n)
    (X : Matrix (Fin n) (Fin n) ℝ) (f : KFin n ds) :
    realStandardLie n (ds.map (realBlockComplexTwist s)) (1 ⊗ₜ X) (twistEquiv s ds hr f) =
      twistEquiv s ds hr (realStandardLie n ds (1 ⊗ₜ X) f) +
        rightDerivative (matrixModel ℝ n) X (detPow n s)
          (1 : Langlands.GeneralLinear n ℝ) • twistEquiv s ds hr f := by
  apply Subtype.ext
  funext g
  rw [realStandardLie_one_tmul_apply_coe]
  change rightDerivative (matrixModel ℝ n) X
    (fun g => detPow n s g * (f : Langlands.GeneralLinear n ℝ → ℂ) g) g = _
  rw [RealPrincipalSeriesDuality.rightDerivative_mul_fun (contMDiff_detPow _)
    (contMDiff_of_mem_realStandardModule f.2.1), RealTemperedTwist.rightDerivative_detPow]
  change _ = detPow n s g *
    (realStandardLie n ds (1 ⊗ₜ X) f : Langlands.GeneralLinear n ℝ → ℂ) g +
      _ * (detPow n s g * (f : Langlands.GeneralLinear n ℝ → ℂ) g)
  rw [realStandardLie_one_tmul_apply_coe]
  ring

/-- The inverse twist carries the right derivative along `X` to the right derivative of the
untwisted function plus the scalar derivative of `|det|^s` at the identity. -/
theorem twistEquiv_symm_rightDerivative (s : ℂ) (ds : List RealBlock) (hr : realRank ds = n)
    (X : Matrix (Fin n) (Fin n) ℝ) (f : KFin n (ds.map (realBlockComplexTwist s)))
    (hf : rightDerivative (matrixModel ℝ n) X (f : Langlands.GeneralLinear n ℝ → ℂ) ∈
      KFin n (ds.map (realBlockComplexTwist s)))
    (hf' : rightDerivative (matrixModel ℝ n) X
      ((twistEquiv s ds hr).symm f : Langlands.GeneralLinear n ℝ → ℂ) ∈ KFin n ds) :
    (twistEquiv s ds hr).symm ⟨_, hf⟩ = ⟨_, hf'⟩ +
      rightDerivative (matrixModel ℝ n) X (detPow n s) (1 : Langlands.GeneralLinear n ℝ) •
        (twistEquiv s ds hr).symm f := by
  have h1 : (⟨_, hf⟩ : KFin n (ds.map (realBlockComplexTwist s))) =
      realStandardLie n (ds.map (realBlockComplexTwist s)) (1 ⊗ₜ X) f :=
    Subtype.ext (realStandardLie_one_tmul_apply_coe _ _ X f).symm
  have h2 : (⟨_, hf'⟩ : KFin n ds) =
      realStandardLie n ds (1 ⊗ₜ X) ((twistEquiv s ds hr).symm f) :=
    Subtype.ext (realStandardLie_one_tmul_apply_coe _ _ X _).symm
  have h3 := twistEquiv_lie s ds hr X ((twistEquiv s ds hr).symm f)
  rw [LinearEquiv.apply_symm_apply] at h3
  rw [h1, h2, h3, map_add, map_smul, LinearEquiv.symm_apply_apply]

end RealComplexTwist

end Langlands.Archimedean
