import Langlands.Representation.Archimedean.RealKTypeTransport
import Langlands.Representation.Archimedean.RealBlockLeftDerivative
import Langlands.Representation.Archimedean.RealBlockFrobeniusMap

/-!
# Deforming the exponents of real standard modules

A function in a principal series of `GL_n(ℝ)` is determined by its values on `O(n)`, and the
values on `O(n)` do not see the exponents of the characters. This module compares right
derivatives and intertwiners for two lists of real blocks that differ only in their exponents.

* `rightDerivative_eq_of_eqOn`: if `F` and `F'` lie in the principal series of characters with
  exponents `τ` and `τ'` and agree on `O(n)`, then at `k ∈ O(n)`
  `R(X) F (k) = R(X) F' (k) + (∑ᵢ (τᵢ - τ'ᵢ) (k X kᵀ)ᵢᵢ) F(k)`.
* `exists_eqOn`: an `O(n)`-finite function of the standard module of `ds` agrees on `O(n)` with
  one of the standard module of `ds'`, when `ds'` has the same signs and no larger induction
  windows (`IsShapeCompatible`).
* `isRealStandardIntertwiner_of_tendsto`: a family `S z` of linear maps between two fixed
  standard modules, weakly continuous at `z = 0` along a filter `L ≤ 𝓝 0`, whose members for
  `z` eventually in `L` agree on `O(n)` with actual intertwiners between the standard modules
  with exponents moved by `z a` and `z b`, has an intertwiner `S 0` as its value at `0`.
  `isRealStandardIntertwiner_of_modulo_bot` turns an intertwiner modulo `⊥` into such an
  intertwiner.
* `blockFrobMap_eqOn`: the values on `O(n)` of a block multiplier map depend only on the
  values of its input on `O(n)` and on the multiplier.
-/

noncomputable section

open scoped Manifold ContDiff Matrix.Norms.Operator TensorProduct Topology
open Filter

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Archimedean

open Langlands.LocalFactor.Archimedean

namespace RealExponentDeformation

open RealBlockDerivative PrincipalSeriesExtension GramFormula

variable {n : ℕ}

/-- The `O(n)`-finite functions of the real standard module of `ds`. -/
abbrev KF (n : ℕ) (ds : List RealBlock) :=
  kFiniteFunctions (realStandardModule n ds) (unitaryCompact ℝ n)

/-! ## Right derivatives of principal series functions agreeing on `O(n)` -/

/-- `∑ᵢ cᵢ (k X kᵀ)ᵢᵢ`. -/
def diagWeight (c : Fin n → ℂ) (X : Matrix (Fin n) (Fin n) ℝ)
    (k : Langlands.GeneralLinear n ℝ) : ℂ :=
  ∑ i, c i * ((((k : Matrix (Fin n) (Fin n) ℝ) * X *
    star (k : Matrix (Fin n) (Fin n) ℝ)) i i : ℝ) : ℂ)

theorem diagWeight_of_eq_mul {c c' : Fin n → ℂ} {w : ℂ} (h : ∀ i, c i = w * c' i)
    (X : Matrix (Fin n) (Fin n) ℝ) (k : Langlands.GeneralLinear n ℝ) :
    diagWeight c X k = w * diagWeight c' X k := by
  unfold diagWeight
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by rw [h i, mul_assoc]

theorem unitsExtension_of_mem {F : Langlands.GeneralLinear n ℝ → ℂ}
    {M : Matrix (Fin n) (Fin n) ℝ} (hM : M ∈ Matrix.unitaryGroup (Fin n) ℝ) :
    unitsExtension F M = F (Unitary.toUnits ⟨M, hM⟩) :=
  unitsExtension_val F (Unitary.toUnits ⟨M, hM⟩)

/-- Along an antisymmetric direction `Z k` at `k ∈ O(n)`, the derivative of a smooth function
only depends on its values on `O(n)`. -/
theorem fderiv_skew_eq {F F' : Langlands.GeneralLinear n ℝ → ℂ}
    (hF : ContMDiff (matrixModel ℝ n) 𝓘(ℝ, ℂ) ∞ F)
    (hF' : ContMDiff (matrixModel ℝ n) 𝓘(ℝ, ℂ) ∞ F')
    (heq : Set.EqOn F F' (unitaryCompact ℝ n))
    {g : Langlands.GeneralLinear n ℝ} (hg : g ∈ unitaryCompact ℝ n)
    {Z : Matrix (Fin n) (Fin n) ℝ} (hZ : Z ∈ skewAdjoint (Matrix (Fin n) (Fin n) ℝ)) :
    fderiv ℝ (unitsExtension F) (g : Matrix (Fin n) (Fin n) ℝ)
        (Z * (g : Matrix (Fin n) (Fin n) ℝ)) =
      fderiv ℝ (unitsExtension F') (g : Matrix (Fin n) (Fin n) ℝ)
        (Z * (g : Matrix (Fin n) (Fin n) ℝ)) := by
  have hγd : HasDerivAt (fun t : ℝ => NormedSpace.exp (t • Z) * (g : Matrix (Fin n) (Fin n) ℝ))
      (Z * (g : Matrix (Fin n) (Fin n) ℝ)) 0 :=
    (RealPrincipalSeriesDuality.hasDerivAt_exp_smul_zero Z).mul_const _
  have hmem : ∀ t : ℝ, NormedSpace.exp (t • Z) * (g : Matrix (Fin n) (Fin n) ℝ) ∈
      Matrix.unitaryGroup (Fin n) ℝ := fun t =>
    Submonoid.mul_mem _
      (NormedSpace.exp_mem_unitary_of_mem_skewAdjoint (skewAdjoint.smul_mem t hZ)) hg
  have hfun : (fun t : ℝ => unitsExtension F
        (NormedSpace.exp (t • Z) * (g : Matrix (Fin n) (Fin n) ℝ))) =
      fun t : ℝ => unitsExtension F'
        (NormedSpace.exp (t • Z) * (g : Matrix (Fin n) (Fin n) ℝ)) := by
    funext t
    rw [unitsExtension_of_mem (hmem t), unitsExtension_of_mem (hmem t)]
    exact heq (show Unitary.toUnits ⟨_, hmem t⟩ ∈ unitaryCompact ℝ n from hmem t)
  have hd : ∀ {G : Langlands.GeneralLinear n ℝ → ℂ},
      ContMDiff (matrixModel ℝ n) 𝓘(ℝ, ℂ) ∞ G →
        HasDerivAt (fun t : ℝ => unitsExtension G
            (NormedSpace.exp (t • Z) * (g : Matrix (Fin n) (Fin n) ℝ)))
          (fderiv ℝ (unitsExtension G) (g : Matrix (Fin n) (Fin n) ℝ)
            (Z * (g : Matrix (Fin n) (Fin n) ℝ))) 0 := by
    intro G hG
    have hdiff : HasFDerivAt (unitsExtension G)
        (fderiv ℝ (unitsExtension G) (g : Matrix (Fin n) (Fin n) ℝ))
        (NormedSpace.exp ((0 : ℝ) • Z) * (g : Matrix (Fin n) (Fin n) ℝ)) := by
      rw [zero_smul, NormedSpace.exp_zero, one_mul]
      exact (differentiableAt_unitsExtension hG (Units.isUnit g)).hasFDerivAt
    exact hdiff.comp_hasDerivAt (0 : ℝ) hγd
  have h1 := hd hF
  rw [hfun] at h1
  exact h1.unique (hd hF')

/-- **Exponent change in right derivatives.** If `F` and `F'` lie in the principal series of
characters with `χᵢ(eˣ) = e^{τᵢ x}` and `χ'ᵢ(eˣ) = e^{τ'ᵢ x}` and agree on `O(n)`, then at
`k ∈ O(n)`: `R(X) F (k) = R(X) F' (k) + (∑ᵢ (τᵢ - τ'ᵢ) (k X kᵀ)ᵢᵢ) F(k)`. -/
theorem rightDerivative_eq_of_eqOn {χ χ' : ℕ → ℝˣ → ℂ} {τ τ' : Fin n → ℂ}
    (hχ : ∀ (i : Fin n) (x : ℝ),
      χ i (Units.mk0 (Real.exp x) (Real.exp_pos x).ne') = Complex.exp (τ i * x))
    (hχ' : ∀ (i : Fin n) (x : ℝ),
      χ' i (Units.mk0 (Real.exp x) (Real.exp_pos x).ne') = Complex.exp (τ' i * x))
    {F F' : Langlands.GeneralLinear n ℝ → ℂ} (hF : F ∈ principalSeries ℝ n χ)
    (hF' : F' ∈ principalSeries ℝ n χ') (heq : Set.EqOn F F' (unitaryCompact ℝ n))
    (X : Matrix (Fin n) (Fin n) ℝ) {g : Langlands.GeneralLinear n ℝ}
    (hg : g ∈ unitaryCompact ℝ n) :
    rightDerivative (matrixModel ℝ n) X F g =
      rightDerivative (matrixModel ℝ n) X F' g +
        diagWeight (fun i => τ i - τ' i) X g * F g := by
  rw [rightDerivative_eq_fderiv hF.1, rightDerivative_eq_fderiv hF'.1]
  have hkk : star (g : Matrix (Fin n) (Fin n) ℝ) * (g : Matrix (Fin n) (Fin n) ℝ) = 1 :=
    Matrix.mem_unitaryGroup_iff'.mp hg
  obtain ⟨Y, hY⟩ : ∃ Y : Matrix (Fin n) (Fin n) ℝ,
      Y = (g : Matrix (Fin n) (Fin n) ℝ) * X * star (g : Matrix (Fin n) (Fin n) ℝ) :=
    ⟨_, rfl⟩
  have hsplit : (g : Matrix (Fin n) (Fin n) ℝ) * X =
      RealJacquetFrobenius.upperPart Y * (g : Matrix (Fin n) (Fin n) ℝ) +
        RealJacquetFrobenius.skewPart Y * (g : Matrix (Fin n) (Fin n) ℝ) := by
    rw [← add_mul, RealJacquetFrobenius.upperPart_add_skewPart, hY,
      mul_assoc ((g : Matrix (Fin n) (Fin n) ℝ) * X), hkk, mul_one]
  have hdiag : ∀ i, RealJacquetFrobenius.upperPart Y i i = Y i i := by
    intro i
    change Y i i - RealJacquetFrobenius.skewPart Y i i = Y i i
    simp [RealJacquetFrobenius.skewPart_apply]
  have hU := RealJacquetFrobenius.upperPart_isUpperTriangular Y
  have e1 := fderiv_upperTriangular_of_isExpEquivariant hF.1
    (isExpEquivariant_of_mem_principalSeries hχ hF) g hU
  have e2 := fderiv_upperTriangular_of_isExpEquivariant hF'.1
    (isExpEquivariant_of_mem_principalSeries hχ' hF') g hU
  have e3 := fderiv_skew_eq hF.1 hF'.1 heq hg (RealJacquetFrobenius.skewPart_mem Y)
  have hsum : (∑ i, (τ i + ((n : ℂ) - 1) / 2 - ((i : ℕ) : ℂ)) *
        ((RealJacquetFrobenius.upperPart Y i i : ℝ) : ℂ)) =
      (∑ i, (τ' i + ((n : ℂ) - 1) / 2 - ((i : ℕ) : ℂ)) *
        ((RealJacquetFrobenius.upperPart Y i i : ℝ) : ℂ)) +
        diagWeight (fun i => τ i - τ' i) X g := by
    unfold diagWeight
    rw [← hY, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by rw [hdiag i]; ring
  rw [hsplit, map_add, map_add, e1, e2, e3, ← heq hg, hsum]
  ring

/-- `rightDerivative_eq_of_eqOn` for the position characters of two lists of real blocks. -/
theorem rightDerivative_eq_of_eqOn_realPosition {ds ds' : List RealBlock}
    {F F' : Langlands.GeneralLinear n ℝ → ℂ}
    (hF : F ∈ principalSeries ℝ n (realPositionCharacter ds))
    (hF' : F' ∈ principalSeries ℝ n (realPositionCharacter ds'))
    (heq : Set.EqOn F F' (unitaryCompact ℝ n))
    (X : Matrix (Fin n) (Fin n) ℝ) {g : Langlands.GeneralLinear n ℝ}
    (hg : g ∈ unitaryCompact ℝ n) :
    rightDerivative (matrixModel ℝ n) X F g =
      rightDerivative (matrixModel ℝ n) X F' g +
        diagWeight (fun i => realPositionExponent ds i - realPositionExponent ds' i) X g * F g :=
  rightDerivative_eq_of_eqOn (τ := fun i => realPositionExponent ds i)
    (τ' := fun i => realPositionExponent ds' i)
    (fun i x => RealKTypeTransport.realPositionCharacter_exp ds i x)
    (fun i x => RealKTypeTransport.realPositionCharacter_exp ds' i x) hF hF' heq X hg

/-- For exponents moved by `z a`: `R(X) F' (k) = R(X) F (k) + z (∑ᵢ aᵢ (k X kᵀ)ᵢᵢ) F(k)`. -/
theorem rightDerivative_eq_of_exponent_shift {ds ds' : List RealBlock} {a : Fin n → ℂ} {z : ℂ}
    (hexp : ∀ i : Fin n, realPositionExponent ds' i = realPositionExponent ds i + z * a i)
    {F F' : Langlands.GeneralLinear n ℝ → ℂ}
    (hF : F ∈ principalSeries ℝ n (realPositionCharacter ds))
    (hF' : F' ∈ principalSeries ℝ n (realPositionCharacter ds'))
    (heq : Set.EqOn F' F (unitaryCompact ℝ n))
    (X : Matrix (Fin n) (Fin n) ℝ) {g : Langlands.GeneralLinear n ℝ}
    (hg : g ∈ unitaryCompact ℝ n) :
    rightDerivative (matrixModel ℝ n) X F' g =
      rightDerivative (matrixModel ℝ n) X F g + z * diagWeight a X g * F g := by
  rw [rightDerivative_eq_of_eqOn_realPosition hF' hF heq X hg,
    diagWeight_of_eq_mul (c' := a) (w := z) (fun i => by simp only [hexp i]; ring), heq hg]

/-! ## Transfer between exponents -/

/-- The block Fourier coefficients on `O(n)` only depend on the values on `O(n)`. -/
theorem blockFourierCoefficient_eq_of_eqOn {f f' : Langlands.GeneralLinear n ℝ → ℂ}
    (h : Set.EqOn f f' (unitaryCompact ℝ n)) (p : ℕ) (j : ℤ) {g : Langlands.GeneralLinear n ℝ}
    (hg : g ∈ unitaryCompact ℝ n) :
    blockFourierCoefficient n p j f g = blockFourierCoefficient n p j f' g := by
  unfold blockFourierCoefficient
  refine intervalIntegral.integral_congr fun θ _ => ?_
  rw [h ((unitaryCompact ℝ n).mul_mem (blockRotation_mem_unitaryCompact n p θ) hg)]

/-- `ds'` has the same signs as `ds` at every position, and each induction block of `ds'` sits
at the position of an induction block of `ds` of at least the same absolute weight. -/
def IsShapeCompatible (ds ds' : List RealBlock) : Prop :=
  (∀ l : ℕ, realPositionCharacter ds' l (-1) = realPositionCharacter ds l (-1)) ∧
    ∀ (p : ℕ) (d' : ComplexCharacterData), realInducedBlockAt ds' p = some d' →
      ∃ d : ComplexCharacterData, realInducedBlockAt ds p = some d ∧ |d'.weight| ≤ |d.weight|

theorem realPositionCharacter_signUnit_eq {ds ds' : List RealBlock}
    (h : IsShapeCompatible ds ds') (l : ℕ) (x : ℝˣ) :
    realPositionCharacter ds' l (signUnit x) = realPositionCharacter ds l (signUnit x) := by
  unfold signUnit
  split_ifs
  · rw [RealStrictCharacterLanglandsQuotient.realPositionCharacter_one,
      RealStrictCharacterLanglandsQuotient.realPositionCharacter_one]
  · exact h.1 l

theorem isSignCompatible_one {ds ds' : List RealBlock} (h : IsShapeCompatible ds ds') :
    RealKTypeTransport.IsSignCompatible (n := n) 1 (realPositionCharacter ds)
      (realPositionCharacter ds') := by
  intro a
  refine ⟨a, by rw [one_mul, mul_one], ?_⟩
  unfold principalSeriesCharacter
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [realPositionCharacter_signUnit_eq h]

theorem eqOn_extension_transport (f : Langlands.GeneralLinear n ℝ → ℂ) (s : Fin n → ℂ) :
    Set.EqOn (extension s (RealKTypeTransport.transport 1 f)) f (unitaryCompact ℝ n) := by
  intro k hk
  rw [← RealKTypeCount.toUnits_mk hk, extension_unitary, RealKTypeTransport.transport_apply,
    one_mul]

/-- **Transfer.** For `ds'` shape compatible with `ds`, every `O(n)`-finite function of the
standard module of `ds` agrees on `O(n)` with one of the standard module of `ds'`. -/
theorem exists_eqOn {ds ds' : List RealBlock} (hr : realRank ds' = n)
    (h : IsShapeCompatible ds ds') (f : KF n ds) :
    ∃ f' : KF n ds', Set.EqOn (f' : Langlands.GeneralLinear n ℝ → ℂ) f (unitaryCompact ℝ n) := by
  have hmem := RealKTypeTransport.extension_transport_mem (V := realStandardModule n ds)
    (χ' := realPositionCharacter ds') (e' := realPositionExponent ds') (fun _ hf => hf.1)
    (isSignCompatible_one h) (realPositionCharacter_eq_signUnit_mul ds') f.2
  have hEq := eqOn_extension_transport (n := n) f (shiftedExponent n (realPositionExponent ds'))
  have hstd : extension (shiftedExponent n (realPositionExponent ds'))
      (RealKTypeTransport.transport 1 f) ∈ realStandardModule n ds' := by
    refine RealKTypeTransport.mem_realStandardModule_of_unitaryCompact hr hmem.1
      fun p d' hd' j hj k hk => ?_
    obtain ⟨d, hd, hw⟩ := h.2 p d' hd'
    rw [blockFourierCoefficient_eq_of_eqOn hEq p j hk]
    exact f.2.1.2 p d hd j (lt_of_lt_of_le hj hw) k
  exact ⟨⟨_, hstd, hmem.2⟩, hEq⟩

/-- Same constructor, same parity for characters and same weight for inductions. -/
def SameShape : RealBlock → RealBlock → Prop
  | .character c, .character c' => c.parity = c'.parity
  | .induced d, .induced d' => d.weight = d'.weight
  | _, _ => False

theorem SameShape.symm : ∀ {x y : RealBlock}, SameShape x y → SameShape y x
  | .character _, .character _, h => Eq.symm h
  | .induced _, .induced _, h => Eq.symm h
  | .character _, .induced _, h => False.elim h
  | .induced _, .character _, h => False.elim h

theorem realRank_eq_of_forall₂ {ds ds' : List RealBlock} (h : List.Forall₂ SameShape ds ds') :
    realRank ds' = realRank ds := by
  induction h with
  | nil => rfl
  | @cons x y xs ys hxy _ ih =>
    rw [realRank_cons, realRank_cons, ih]
    cases x <;> cases y <;> first | rfl | exact False.elim hxy

theorem isShapeCompatible_of_forall₂ {ds ds' : List RealBlock}
    (h : List.Forall₂ SameShape ds ds') : IsShapeCompatible ds ds' := by
  induction h with
  | nil => exact ⟨fun l => rfl, fun p d' h => by simp [realInducedBlockAt] at h⟩
  | @cons x y xs ys hxy _ ih =>
    cases x with
    | character c =>
      cases y with
      | character c' =>
        have hp : c.parity = c'.parity := hxy
        refine ⟨fun l => ?_, fun p d' hd => ?_⟩
        · rcases l with _ | l
          · show (c'.character (-1) : ℂ) = (c.character (-1) : ℂ)
            rw [c.character_eq, c'.character_eq, hp]
            simp
          · exact ih.1 l
        · rcases p with _ | p
          · simp [realInducedBlockAt] at hd
          · exact ih.2 p d' hd
      | induced _ => exact False.elim hxy
    | induced d =>
      cases y with
      | character _ => exact False.elim hxy
      | induced d' =>
        have hw : d.weight = d'.weight := hxy
        refine ⟨fun l => ?_, fun p d'' hd => ?_⟩
        · rcases l with _ | _ | l
          · simp [realPositionCharacter, realInducedFirstCharacter, hw]
          · simp [realPositionCharacter, realInducedSecondCharacter]
          · exact ih.1 l
        · rcases p with _ | _ | p
          · simp only [realInducedBlockAt, Option.some.injEq] at hd
            subst hd
            exact ⟨d, rfl, le_of_eq (by rw [hw])⟩
          · simp [realInducedBlockAt] at hd
          · exact ih.2 p d'' hd

/-! ## Limits of intertwiners -/

/-- The list `ds'` has rank `n`, has the shape of `ds` in both directions, and its position
exponents are those of `ds` moved by `z a`. -/
structure IsExponentShift (n : ℕ) (ds ds' : List RealBlock) (a : Fin n → ℂ) (z : ℂ) : Prop where
  rank : realRank ds = n
  rank' : realRank ds' = n
  forward : IsShapeCompatible ds ds'
  backward : IsShapeCompatible ds' ds
  exponent : ∀ i : Fin n, realPositionExponent ds' i = realPositionExponent ds i + z * a i

theorem IsExponentShift.of_forall₂ {ds ds' : List RealBlock} {a : Fin n → ℂ} {z : ℂ}
    (hr : realRank ds = n) (h : List.Forall₂ SameShape ds ds')
    (hexp : ∀ i : Fin n, realPositionExponent ds' i = realPositionExponent ds i + z * a i) :
    IsExponentShift n ds ds' a z where
  rank := hr
  rank' := (realRank_eq_of_forall₂ h).trans hr
  forward := isShapeCompatible_of_forall₂ h
  backward := isShapeCompatible_of_forall₂ (h.flip.imp fun _ _ hxy => SameShape.symm hxy)
  exponent := hexp

/-- Evaluation at a point, as a linear functional. -/
def evalAt (ds : List RealBlock) (g : Langlands.GeneralLinear n ℝ) : KF n ds →ₗ[ℂ] ℂ :=
  (LinearMap.proj (R := ℂ) (φ := fun _ : Langlands.GeneralLinear n ℝ => ℂ) g).comp
    (KF n ds).subtype

@[simp]
theorem evalAt_apply (ds : List RealBlock) (g : Langlands.GeneralLinear n ℝ) (f : KF n ds) :
    evalAt ds g f = (f : Langlands.GeneralLinear n ℝ → ℂ) g :=
  rfl

theorem ext_of_eqOn {ds : List RealBlock} {f f' : KF n ds}
    (h : Set.EqOn (f : Langlands.GeneralLinear n ℝ → ℂ) f' (unitaryCompact ℝ n)) : f = f' :=
  Subtype.ext (eq_of_eqOn_unitaryCompact_of_mem_principalSeries f.2.1.1 f'.2.1.1
    fun _ hk => h hk)

/-- An intertwiner modulo `⊥` between two standard modules is an intertwiner into the target
standard module. -/
theorem isRealStandardIntertwiner_of_modulo_bot {ds es : List RealBlock}
    {q : KF n ds →ₗ[ℂ] KF n es} (hq : IsRealIntertwinerModulo n ds es ⊥ q) :
    IsRealStandardIntertwiner n (realStandardRep n es) (realStandardLie n es) ds q := by
  refine ⟨fun k f => ?_, fun X f => ?_⟩
  · obtain ⟨hf, hg, hmem⟩ := hq.1 k f
    refine ⟨hf, ?_⟩
    rw [Submodule.mem_bot, sub_eq_zero] at hmem
    rw [hmem]
    apply Subtype.ext
    rw [realStandardRep_apply_coe, RealKTypeCount.toUnits_mk k.2]
  · obtain ⟨hf, hg, hmem⟩ := hq.2 X f
    refine ⟨hf, ?_⟩
    rw [Submodule.mem_bot, sub_eq_zero] at hmem
    rw [hmem]
    apply Subtype.ext
    rw [realStandardLie_one_tmul_apply_coe]

/-- **Limits of intertwiners.** Let `S z` be linear maps between the `O(n)`-finite functions of
the standard modules of two fixed lists `ds` and `es`, such that every scalar coordinate of
`S z f` tends to that of `S 0 f` along a nontrivial filter `L ≤ 𝓝 0`. Suppose that for `z`
eventually in `L`, `z ≠ 0`, the lists `ds' z` and `es' z` are exponent shifts of `ds` and `es`
by `z a` and `z b`, and `S z` agrees on `O(n)` with an intertwiner `T` from `ds' z` to `es' z`
(on inputs agreeing on `O(n)`). Then `S 0` is an intertwiner from `ds` to `es`. -/
theorem isRealStandardIntertwiner_of_tendsto {ds es : List RealBlock}
    {ds' es' : ℂ → List RealBlock} {a b : Fin n → ℂ} {L : Filter ℂ} [L.NeBot]
    (hL : L ≤ 𝓝 0) (S : ℂ → KF n ds →ₗ[ℂ] KF n es)
    (hS : ∀ (f : KF n ds) (ℓ : KF n es →ₗ[ℂ] ℂ),
      Tendsto (fun z => ℓ (S z f)) L (𝓝 (ℓ (S 0 f))))
    (hev : ∀ᶠ z in L, z ≠ 0 ∧ IsExponentShift n ds (ds' z) a z ∧
      IsExponentShift n es (es' z) b z ∧
      ∃ T : KF n (ds' z) →ₗ[ℂ] KF n (es' z),
        IsRealStandardIntertwiner n (realStandardRep n (es' z)) (realStandardLie n (es' z))
          (ds' z) T ∧
        ∀ (f : KF n ds) (f' : KF n (ds' z)),
          Set.EqOn (f' : Langlands.GeneralLinear n ℝ → ℂ) f (unitaryCompact ℝ n) →
            Set.EqOn (T f' : Langlands.GeneralLinear n ℝ → ℂ) (S z f) (unitaryCompact ℝ n)) :
    IsRealStandardIntertwiner n (realStandardRep n es) (realStandardLie n es) ds (S 0) := by
  have hlim : ∀ (f : KF n ds) (g : Langlands.GeneralLinear n ℝ),
      Tendsto (fun z => (S z f : Langlands.GeneralLinear n ℝ → ℂ) g) L
        (𝓝 ((S 0 f : Langlands.GeneralLinear n ℝ → ℂ) g)) :=
    fun f g => hS f (evalAt es g)
  have hlimD : ∀ (f : KF n ds) (X : Matrix (Fin n) (Fin n) ℝ) (g : Langlands.GeneralLinear n ℝ),
      Tendsto (fun z => rightDerivative (matrixModel ℝ n) X
          (S z f : Langlands.GeneralLinear n ℝ → ℂ) g) L
        (𝓝 (rightDerivative (matrixModel ℝ n) X (S 0 f : Langlands.GeneralLinear n ℝ → ℂ) g)) := by
    intro f X g
    have := hS f ((evalAt es g).comp (realStandardLie n es (1 ⊗ₜ X)))
    simpa only [LinearMap.comp_apply, evalAt_apply, realStandardLie_one_tmul_apply_coe] using this
  have hz : Tendsto (fun z : ℂ => z) L (𝓝 0) := tendsto_id.mono_left hL
  refine ⟨fun k f => ⟨rightTranslation_mem_kFiniteFunctions_realStandardModule n ds f.2 k.2, ?_⟩,
    fun X f => ⟨rightDerivative_mem_kFiniteFunctions_realStandardModule n ds f.2 X, ?_⟩⟩
  · -- compact equivariance
    apply ext_of_eqOn
    intro g hg
    have hR : ((realStandardRep n es ⟨((k : Langlands.GeneralLinear n ℝ) :
          Matrix (Fin n) (Fin n) ℝ), k.2⟩ (S 0 f) : KF n es) :
          Langlands.GeneralLinear n ℝ → ℂ) g =
        (S 0 f : Langlands.GeneralLinear n ℝ → ℂ) (g * k) := by
      rw [realStandardRep_apply_coe, RealKTypeCount.toUnits_mk k.2]
      rfl
    rw [hR]
    refine tendsto_nhds_unique_of_eventuallyEq (hlim _ g) (hlim f (g * k)) ?_
    filter_upwards [hev] with z hz'
    obtain ⟨-, hd, -, T, hT, hST⟩ := hz'
    obtain ⟨f', hf'⟩ := exists_eqOn hd.rank' hd.forward f
    obtain ⟨hk', hTk⟩ := hT.1 k f'
    have hagree : Set.EqOn ((⟨_, hk'⟩ : KF n (ds' z)) : Langlands.GeneralLinear n ℝ → ℂ)
        ((⟨_, rightTranslation_mem_kFiniteFunctions_realStandardModule n ds f.2 k.2⟩ :
          KF n ds) : Langlands.GeneralLinear n ℝ → ℂ) (unitaryCompact ℝ n) :=
      fun x hx => hf' ((unitaryCompact ℝ n).mul_mem hx k.2)
    refine (hST _ _ hagree hg).symm.trans ?_
    rw [hTk, realStandardRep_apply_coe, RealKTypeCount.toUnits_mk k.2]
    exact hST f f' hf' ((unitaryCompact ℝ n).mul_mem hg k.2)
  · -- Lie equivariance
    apply ext_of_eqOn
    intro g hg
    rw [realStandardLie_one_tmul_apply_coe]
    suffices key : ∀ RXf : KF n ds, (RXf : Langlands.GeneralLinear n ℝ → ℂ) =
        rightDerivative (matrixModel ℝ n) X f →
          (S 0 RXf : Langlands.GeneralLinear n ℝ → ℂ) g =
            rightDerivative (matrixModel ℝ n) X (S 0 f : Langlands.GeneralLinear n ℝ → ℂ) g from
      key _ rfl
    intro RXf hRXf
    -- the correction term `P = (∑ᵢ aᵢ (k X kᵀ)ᵢᵢ) f` on `O(n)`
    obtain ⟨P, hP⟩ : ∃ P : KF n ds, Set.EqOn (P : Langlands.GeneralLinear n ℝ → ℂ)
        (fun x => diagWeight a X x * (f : Langlands.GeneralLinear n ℝ → ℂ) x)
        (unitaryCompact ℝ n) := by
      obtain ⟨z₀, hz₀, hd₀, -⟩ := hev.exists
      obtain ⟨f₀, hf₀⟩ := exists_eqOn hd₀.rank' hd₀.forward f
      obtain ⟨g₀, hg₀⟩ := exists_eqOn hd₀.rank hd₀.backward
        (⟨_, rightDerivative_mem_kFiniteFunctions_realStandardModule n (ds' z₀) f₀.2 X⟩ :
          KF n (ds' z₀))
      refine ⟨z₀⁻¹ • (g₀ - RXf), fun x hx => ?_⟩
      have e := rightDerivative_eq_of_exponent_shift hd₀.exponent f.2.1.1 f₀.2.1.1 hf₀ X hx
      have e' : (g₀ : Langlands.GeneralLinear n ℝ → ℂ) x =
          rightDerivative (matrixModel ℝ n) X f₀ x := hg₀ hx
      have e'' : (RXf : Langlands.GeneralLinear n ℝ → ℂ) x =
          rightDerivative (matrixModel ℝ n) X f x := by rw [hRXf]
      show z₀⁻¹ * ((g₀ : Langlands.GeneralLinear n ℝ → ℂ) x -
        (RXf : Langlands.GeneralLinear n ℝ → ℂ) x) = _
      rw [e', e'', e]
      field_simp
      ring
    have hR : Tendsto (fun z => (S z RXf : Langlands.GeneralLinear n ℝ → ℂ) g +
          z * (S z P : Langlands.GeneralLinear n ℝ → ℂ) g -
          z * diagWeight b X g * (S z f : Langlands.GeneralLinear n ℝ → ℂ) g) L
        (𝓝 ((S 0 RXf : Langlands.GeneralLinear n ℝ → ℂ) g +
          0 * (S 0 P : Langlands.GeneralLinear n ℝ → ℂ) g -
          0 * diagWeight b X g * (S 0 f : Langlands.GeneralLinear n ℝ → ℂ) g)) :=
      ((hlim RXf g).add (hz.mul (hlim P g))).sub
        ((hz.mul tendsto_const_nhds).mul (hlim f g))
    have key := tendsto_nhds_unique_of_eventuallyEq (hlimD f X g) hR ?_
    · rw [key]
      ring
    filter_upwards [hev] with z hz'
    obtain ⟨-, hd, he, T, hT, hST⟩ := hz'
    obtain ⟨f', hf'⟩ := exists_eqOn hd.rank' hd.forward f
    -- the target: `R(X) (T f') = R(X) (S z f) + z q_b (S z f)` on `O(n)`
    have e1 := rightDerivative_eq_of_exponent_shift he.exponent (S z f).2.1.1 (T f').2.1.1
      (hST f f' hf') X hg
    -- `T` intertwines the right derivatives
    obtain ⟨hX', hTX⟩ := hT.2 X f'
    have e2 : rightDerivative (matrixModel ℝ n) X (T f' : Langlands.GeneralLinear n ℝ → ℂ) g =
        (T ⟨_, hX'⟩ : Langlands.GeneralLinear n ℝ → ℂ) g := by
      rw [hTX, realStandardLie_one_tmul_apply_coe]
    -- the source: `R(X) f' = R(X) f + z P` on `O(n)`
    have hagree : Set.EqOn ((⟨_, hX'⟩ : KF n (ds' z)) : Langlands.GeneralLinear n ℝ → ℂ)
        ((RXf + z • P : KF n ds) : Langlands.GeneralLinear n ℝ → ℂ) (unitaryCompact ℝ n) := by
      intro x hx
      have e := rightDerivative_eq_of_exponent_shift hd.exponent f.2.1.1 f'.2.1.1 hf' X hx
      show rightDerivative (matrixModel ℝ n) X f' x =
        (RXf : Langlands.GeneralLinear n ℝ → ℂ) x + z * (P : Langlands.GeneralLinear n ℝ → ℂ) x
      rw [e, hRXf, hP hx]
      ring
    have e3 := hST _ _ hagree hg
    simp only [map_add, map_smul, Submodule.coe_add, Submodule.coe_smul, Pi.add_apply,
      Pi.smul_apply, smul_eq_mul] at e3
    linear_combination -e1 + e2 + e3

/-! ## Block multiplier maps on `O(n)` -/

/-- The values on `O(n)` of a block multiplier map depend only on the multiplier and on the
values of the input on `O(n)`; the lists, parities and signs may differ. -/
theorem blockFrobMap_eqOn {ds es ds' es' : List RealBlock} {p : ℕ} {ε ε' : ℤ} {σ σ' : ℂ}
    {μ : ℤ → ℂ} (h : RealBlockFrobeniusMap.IsBlockFrobData n ds es p ε σ μ)
    (h' : RealBlockFrobeniusMap.IsBlockFrobData n ds' es' p ε' σ' μ)
    {f : KF n ds} {f' : KF n ds'}
    (hf : Set.EqOn (f' : Langlands.GeneralLinear n ℝ → ℂ) f (unitaryCompact ℝ n)) :
    Set.EqOn (RealBlockFrobeniusMap.blockFrobMap h' f' : Langlands.GeneralLinear n ℝ → ℂ)
      (RealBlockFrobeniusMap.blockFrobMap h f) (unitaryCompact ℝ n) := by
  intro g hg
  rw [RealBlockFrobeniusMap.blockFrobMap_apply_of_mem h' f' hg,
    RealBlockFrobeniusMap.blockFrobMap_apply_of_mem h f hg]
  congr 1
  refine finsum_congr fun i => ?_
  rw [blockFourierCoefficient_eq_of_eqOn hf p i hg]

end RealExponentDeformation
end Langlands.Archimedean
