import Langlands.Representation.Induction.SplitKernelEquivariant

/-!
# Split-kernel value integrals over a fixed intersection subgroup

For a split retraction `r : G →* L` with section `s`, a closed subgroup `H`
containing `s(L)`, a smooth `σ : Representation ℂ H V` and a linear map
`T : V →ₗ[ℂ] W` killing the action of `H ∩ ker r`, this file integrates
`n ↦ T (f n)` over the left quotient `I \ ker r` of a supplied subgroup `I` of
`ker r` with the same points as `H ∩ ker r`.

The integration domain depends only on `I`, not on `H`. Two inducing subgroups
with the same kernel intersection therefore integrate over literally the same
quotient with the same measure.
-/

noncomputable section

namespace Langlands.Induction

open MeasureTheory MeasureTheory.Measure
open QuotientIntegration HarmonicAnalysis
open scoped NNReal ENNReal

universe uG uL uV uW

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {L : Type uL} [Group L]
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
variable {W : Type uW} [AddCommGroup W] [Module ℂ W]

section Function

variable (r : G →* L) (H : Subgroup G) (I : Subgroup r.ker)
  (hI : ∀ n : r.ker, n ∈ I ↔ (n : G) ∈ H)
  (σ : Representation ℂ H V) (T : V →ₗ[ℂ] W)
  (hT : ∀ h : H, (h : G) ∈ r.ker → ∀ v, T (σ h v) = T v)

include hI hT in
/-- Covariance and the invariance of `T` make `n ↦ T (f n)` left `I`-invariant. -/
theorem splitKernelValue_left_mul (f : CompactFunctions H σ) (i : I) (n : r.ker) :
    T (eval H σ f.val (((i : r.ker) * n : r.ker) : G)) = T (eval H σ f.val (n : G)) := by
  have hi : ((i : r.ker) : G) ∈ H := (hI i).mp i.property
  have hcov := eval_covariant H σ f.val ⟨((i : r.ker) : G), hi⟩ (n : G)
  change T (eval H σ f.val (((i : r.ker) : G) * (n : G))) = _
  rw [hcov]
  exact hT ⟨((i : r.ker) : G), hi⟩ (i : r.ker).property _

/-- The function `I n ↦ T (f n)` on the fixed quotient `I \ ker r`. -/
def splitKernelValueFunction (f : CompactFunctions H σ) : LeftQuotient I → W :=
  descend I (fun n : r.ker => T (eval H σ f.val (n : G)))
    (splitKernelValue_left_mul r H I hI σ T hT f)

@[simp] theorem splitKernelValueFunction_mk (f : CompactFunctions H σ) (n : r.ker) :
    splitKernelValueFunction r H I hI σ T hT f (quotientMap I n) =
      T (eval H σ f.val (n : G)) := rfl

/-- Local constancy descends through the quotient topology. -/
theorem splitKernelValueFunction_isLocallyConstant (f : CompactFunctions H σ) :
    IsLocallyConstant (splitKernelValueFunction r H I hI σ T hT f) := by
  intro S
  apply (isQuotientMap_quotient_mk' (s := QuotientGroup.rightRel I)).isCoinducing.isOpen_preimage.mp
  exact (((eval_isLocallyConstant H σ f.val).comp_continuous continuous_subtype_val).comp T) S

/-- Right translation by a kernel element moves the value function by the
actual quotient right translation. -/
theorem splitKernelValueFunction_translate (n : r.ker) (f : CompactFunctions H σ)
    (q : LeftQuotient I) :
    splitKernelValueFunction r H I hI σ T hT (compactInduced H σ (n : G) f) q =
      splitKernelValueFunction r H I hI σ T hT f (rightTranslate I n q) := by
  induction q using Quotient.inductionOn with
  | h x => rfl

variable [TopologicalSpace L] (s : L →* G) (hrs : ∀ l, r (s l) = l)
  (hr : Continuous r) (hs : Continuous s) (hsH : ∀ l, s l ∈ H)

include hrs hr hs hsH in
/-- Compact support, from the published compactness of the actual kernel
restriction; the fixed subgroup is identified with the intersection. -/
theorem splitKernelValueFunction_hasCompactSupport (f : CompactFunctions H σ) :
    HasCompactSupport (splitKernelValueFunction r H I hI σ T hT f) := by
  have hc := isCompact_quotientSupport_splitKernel_restrict r s hrs hr hs H hsH σ f
  obtain rfl : I = H.comap r.ker.subtype := Subgroup.ext hI
  apply hc.of_isClosed_subset isClosed_closure
  apply closure_minimal _
    (isClosed_quotientSupport _ _ (splitKernelCompactRestrict r s hrs hr hs H hsH σ f).val)
  intro q hq
  obtain ⟨n, rfl⟩ := Quotient.exists_rep q
  refine ⟨n, ?_, rfl⟩
  intro h0
  apply hq
  change T (eval H σ f.val (n : G)) = 0
  change eval H σ f.val (n : G) = 0 at h0
  rw [h0, map_zero]

variable [MeasurableSpace (LeftQuotient I)] [BorelSpace (LeftQuotient I)]

/-- The value function as an actual finite-image simple function. -/
def splitKernelValueSimple (f : CompactFunctions H σ) : SimpleFunc (LeftQuotient I) W :=
  compactlySupportedSimpleFunc (splitKernelValueFunction r H I hI σ T hT f)
    (splitKernelValueFunction_isLocallyConstant r H I hI σ T hT f)
    (splitKernelValueFunction_hasCompactSupport r H I hI σ T hT s hrs hr hs hsH f)

@[simp] theorem splitKernelValueSimple_apply (f : CompactFunctions H σ) (q : LeftQuotient I) :
    splitKernelValueSimple r H I hI σ T hT s hrs hr hs hsH f q =
      splitKernelValueFunction r H I hI σ T hT f q := rfl

theorem splitKernelValueSimple_add (f k : CompactFunctions H σ) :
    splitKernelValueSimple r H I hI σ T hT s hrs hr hs hsH (f + k) =
      splitKernelValueSimple r H I hI σ T hT s hrs hr hs hsH f +
        splitKernelValueSimple r H I hI σ T hT s hrs hr hs hsH k := by
  ext q
  induction q using Quotient.inductionOn with
  | h x =>
    change T (eval H σ f.val (x : G) + eval H σ k.val (x : G)) = _
    exact map_add T _ _

theorem splitKernelValueSimple_smul (c : ℂ) (f : CompactFunctions H σ) :
    splitKernelValueSimple r H I hI σ T hT s hrs hr hs hsH (c • f) =
      c • splitKernelValueSimple r H I hI σ T hT s hrs hr hs hsH f := by
  ext q
  induction q using Quotient.inductionOn with
  | h x =>
    change T (c • eval H σ f.val (x : G)) = _
    exact map_smul T _ _

variable (ν : Measure (LeftQuotient I)) [IsFiniteMeasureOnCompacts ν]

theorem splitKernelValueSimple_finMeasSupp (f : CompactFunctions H σ) :
    (splitKernelValueSimple r H I hI σ T hT s hrs hr hs hsH f).FinMeasSupp ν :=
  compactlySupportedSimpleFunc_finMeasSupp ν _ _ _

/-- The value integral `f ↦ ∫_{I \ ker r} T (f n) dν`. -/
def splitKernelValueIntegral : CompactFunctions H σ →ₗ[ℂ] W where
  toFun f := AlgebraicIntegral.integral ν (splitKernelValueSimple r H I hI σ T hT s hrs hr hs hsH f)
  map_add' f k := by
    rw [splitKernelValueSimple_add]
    exact AlgebraicIntegral.integral_add _ _
      (splitKernelValueSimple_finMeasSupp r H I hI σ T hT s hrs hr hs hsH ν f)
      (splitKernelValueSimple_finMeasSupp r H I hI σ T hT s hrs hr hs hsH ν k)
  map_smul' c f := by
    rw [splitKernelValueSimple_smul]
    exact AlgebraicIntegral.integral_smul c _
      (splitKernelValueSimple_finMeasSupp r H I hI σ T hT s hrs hr hs hsH ν f)

theorem splitKernelValueIntegral_apply (f : CompactFunctions H σ) :
    splitKernelValueIntegral r H I hI σ T hT s hrs hr hs hsH ν f =
      AlgebraicIntegral.integral ν (splitKernelValueSimple r H I hI σ T hT s hrs hr hs hsH f) :=
  rfl

include hT in
/-- Right invariance of the quotient measure gives invariance under the kernel. -/
theorem splitKernelValueIntegral_translate
    (hν : ∀ n : r.ker, MeasurePreserving (rightTranslate I n) ν ν)
    (n : r.ker) (f : CompactFunctions H σ) :
    splitKernelValueIntegral r H I hI σ T hT s hrs hr hs hsH ν (compactInduced H σ (n : G) f) =
      splitKernelValueIntegral r H I hI σ T hT s hrs hr hs hsH ν f := by
  have he : splitKernelValueSimple r H I hI σ T hT s hrs hr hs hsH (compactInduced H σ (n : G) f) =
      (splitKernelValueSimple r H I hI σ T hT s hrs hr hs hsH f).comp (rightTranslate I n)
        (hν n).measurable := by
    ext q
    exact splitKernelValueFunction_translate r H I hI σ T hT n f q
  rw [splitKernelValueIntegral_apply, he]
  exact AlgebraicIntegral.integral_comp_measurePreserving _ _ (hν n)

/-- If the values of a second inducing datum over the same fixed quotient are
the images of the values of the first under a linear map `A`, then so are the
value integrals. -/
theorem splitKernelValueIntegral_map_of_eval {H' : Subgroup G}
    (hI' : ∀ n : r.ker, n ∈ I ↔ (n : G) ∈ H')
    {V' : Type*} [AddCommGroup V'] [Module ℂ V'] (σ' : Representation ℂ H' V')
    {W' : Type*} [AddCommGroup W'] [Module ℂ W']
    (T' : V' →ₗ[ℂ] W') (hT' : ∀ h : H', (h : G) ∈ r.ker → ∀ v, T' (σ' h v) = T' v)
    (hsH' : ∀ l, s l ∈ H') (A : W →ₗ[ℂ] W') (f : CompactFunctions H σ)
    (f' : CompactFunctions H' σ')
    (hff' : ∀ n : r.ker, T' (eval H' σ' f'.val (n : G)) = A (T (eval H σ f.val (n : G)))) :
    splitKernelValueIntegral r H' I hI' σ' T' hT' s hrs hr hs hsH' ν f' =
      A (splitKernelValueIntegral r H I hI σ T hT s hrs hr hs hsH ν f) := by
  have he : splitKernelValueSimple r H' I hI' σ' T' hT' s hrs hr hs hsH' f' =
      (splitKernelValueSimple r H I hI σ T hT s hrs hr hs hsH f).map A := by
    ext q
    induction q using Quotient.inductionOn with
    | h x => exact hff' x
  rw [splitKernelValueIntegral_apply, splitKernelValueIntegral_apply, he]
  exact AlgebraicIntegral.integral_linearMap _
    (splitKernelValueSimple_finMeasSupp r H I hI σ T hT s hrs hr hs hsH ν f) A

/-- Pointwise agreement of values gives equal value integrals, for two inducing
data over the same fixed quotient and measure. -/
theorem splitKernelValueIntegral_eq_of_eval {H' : Subgroup G}
    (hI' : ∀ n : r.ker, n ∈ I ↔ (n : G) ∈ H')
    {V' : Type*} [AddCommGroup V'] [Module ℂ V'] (σ' : Representation ℂ H' V')
    (T' : V' →ₗ[ℂ] W) (hT' : ∀ h : H', (h : G) ∈ r.ker → ∀ v, T' (σ' h v) = T' v)
    (hsH' : ∀ l, s l ∈ H') (f : CompactFunctions H σ) (f' : CompactFunctions H' σ')
    (hff' : ∀ n : r.ker, T' (eval H' σ' f'.val (n : G)) = T (eval H σ f.val (n : G))) :
    splitKernelValueIntegral r H' I hI' σ' T' hT' s hrs hr hs hsH' ν f' =
      splitKernelValueIntegral r H I hI σ T hT s hrs hr hs hsH ν f :=
  splitKernelValueIntegral_map_of_eval r H I hI σ T hT s hrs hr hs hsH ν hI' σ' T' hT' hsH'
    LinearMap.id f f' hff'

end Function

section Descent

variable (r : G →* L) (H : Subgroup G) (σ : Representation ℂ H V) (T : V →ₗ[ℂ] W)
  (hT : ∀ h : H, (h : G) ∈ r.ker → ∀ v, T (σ h v) = T v)

/-- The coefficient map descended to the coinvariants of `σ` restricted to
`H ∩ ker r`. It does not depend on the choice of the integration subgroup. -/
def splitKernelValueDescent :
    Representation.Coinvariants (σ.comp (r.ker.subtype.subgroupComap H)) →ₗ[ℂ] W :=
  Representation.Coinvariants.lift _ T fun i =>
    LinearMap.ext fun v => hT _ (i : r.ker).property v

omit [TopologicalSpace G] [IsTopologicalGroup G] in
@[simp] theorem splitKernelValueDescent_mk (v : V) :
    splitKernelValueDescent r H σ T hT
        (Representation.Coinvariants.mk (σ.comp (r.ker.subtype.subgroupComap H)) v) = T v :=
  rfl

omit [TopologicalSpace G] [IsTopologicalGroup G] in
theorem splitKernelValueDescent_surjective (hTs : Function.Surjective T) :
    Function.Surjective (splitKernelValueDescent r H σ T hT) := by
  intro w
  obtain ⟨v, rfl⟩ := hTs w
  exact ⟨Representation.Coinvariants.mk _ v, rfl⟩

variable (s : L →* G) (hsH : ∀ l, s l ∈ H)

/-- The descended coefficient map carries the section action on coinvariants
to a supplied action `τ` when `T` intertwines the section values with `τ`. -/
theorem splitKernelValueDescent_coefficientAction {τ : Representation ℂ L W}
    (hTτ : ∀ l v, T (σ (splitKernelSection s H hsH l) v) = τ l (T v)) (l : L)
    (z : Representation.Coinvariants (σ.comp (r.ker.subtype.subgroupComap H))) :
    splitKernelValueDescent r H σ T hT (splitKernelCoefficientAction r s H hsH σ l z) =
      τ l (splitKernelValueDescent r H σ T hT z) := by
  obtain ⟨v, rfl⟩ := Representation.Coinvariants.mk_surjective _ z
  exact hTτ l v

variable [TopologicalSpace L] [LocallyCompactSpace G] (hrs : ∀ l, r (s l) = l)
  (hr : Continuous r) (hs : Continuous s) (hH : IsClosed (H : Set G)) (hσ : IsSmooth σ)

/-- For the intersection subgroup itself, the value integral is the descended
coefficient map applied to the published relative integral. -/
theorem splitKernelValueIntegral_eq_descent
    (hI : ∀ n : r.ker, n ∈ H.comap r.ker.subtype ↔ (n : G) ∈ H)
    [MeasurableSpace (LeftQuotient (H.comap r.ker.subtype))]
    [BorelSpace (LeftQuotient (H.comap r.ker.subtype))]
    (ν : Measure (LeftQuotient (H.comap r.ker.subtype))) [IsFiniteMeasureOnCompacts ν]
    (f : CompactFunctions H σ) :
    splitKernelValueIntegral r H (H.comap r.ker.subtype) hI σ T hT s hrs hr hs hsH ν f =
      splitKernelValueDescent r H σ T hT
        (splitKernelCompactIntegral r s hrs hr hs H hH hsH σ hσ ν f) := by
  have he : splitKernelValueSimple r H (H.comap r.ker.subtype) hI σ T hT s hrs hr hs hsH f =
      (quotientCoinvariantSimple (H.comap r.ker.subtype)
        (σ.comp (r.ker.subtype.subgroupComap H))
        (splitKernelCompactEquiv r s hrs hr hs H hH hsH σ hσ f)).map
          (splitKernelValueDescent r H σ T hT) := by
    ext q
    induction q using Quotient.inductionOn with
    | h x => rfl
  rw [splitKernelValueIntegral_apply, he]
  exact AlgebraicIntegral.integral_linearMap _ (compactlySupportedSimpleFunc_finMeasSupp ν _ _ _) _

end Descent

section Section

variable (r : G →* L) (H : Subgroup G) (I : Subgroup r.ker)
  (hI : ∀ n : r.ker, n ∈ I ↔ (n : G) ∈ H)
  (σ : Representation ℂ H V) (T : V →ₗ[ℂ] W)
  (hT : ∀ h : H, (h : G) ∈ r.ker → ∀ v, T (σ h v) = T v)
  (s : L →* G) (hsH : ∀ l, s l ∈ H)

include hI hsH in
/-- Inverse conjugation by a section value preserves the fixed subgroup. -/
theorem splitKernelValue_conjugation_mem (l : L) (n : r.ker) :
    splitKernelConjugation r s l n ∈ I ↔ n ∈ I := by
  rw [hI, hI]
  exact splitKernelConjugation_mem r s H hsH l n

/-- The positive ratio of the Haar moduli of inverse conjugation by a section
value on the fixed subgroup `I` and on `ker r`. For `I = H ∩ ker r` it is the
value of `splitKernelHaarRatio`. -/
def splitKernelValueRatio [LocallyCompactSpace r.ker] [MeasurableSpace r.ker]
    [BorelSpace r.ker] [LocallyCompactSpace I] [MeasurableSpace I] [BorelSpace I]
    (l : L) : ℝ≥0 :=
  mulEquivHaarChar (subgroupAutomorphism I (splitKernelConjugation r s l)
      (splitKernelValue_conjugation_mem r H I hI s hsH l)) /
    mulEquivHaarChar (splitKernelConjugation r s l)

variable [TopologicalSpace L] [LocallyCompactSpace G] [T2Space G] (hrs : ∀ l, r (s l) = l)
  (hr : Continuous r) (hs : Continuous s) (hH : IsClosed (H : Set G)) (hσ : IsSmooth σ)
  [LocallyCompactSpace r.ker] [MeasurableSpace r.ker] [BorelSpace r.ker]
  [MeasurableSpace I] [BorelSpace I]
  [MeasurableSpace (LeftQuotient I)] [BorelSpace (LeftQuotient I)]
  (ν : Measure (LeftQuotient I)) [IsFiniteMeasureOnCompacts ν]

include hH hσ in
/-- Section law: translating by a section value multiplies the value integral
by the Haar ratio and applies `τ`, when `T` intertwines the section values. -/
theorem splitKernelValueIntegral_section [LocallyCompactSpace I]
    {μN : Measure r.ker} {μI : Measure I} [IsHaarMeasure μN] [μN.Regular]
    [IsHaarMeasure μI] [μI.Regular] [IsMulRightInvariant μI]
    (hCompatible : IsCompatible I μN μI ν) {τ : Representation ℂ L W}
    (hTτ : ∀ l v, T (σ (splitKernelSection s H hsH l) v) = τ l (T v))
    (l : L) (f : CompactFunctions H σ) :
    splitKernelValueIntegral r H I hI σ T hT s hrs hr hs hsH ν (compactInduced H σ (s l) f) =
      ((splitKernelValueRatio r H I hI s hsH l : ℝ) : ℂ) •
        τ l (splitKernelValueIntegral r H I hI σ T hT s hrs hr hs hsH ν f) := by
  obtain rfl : I = H.comap r.ker.subtype := Subgroup.ext hI
  rw [splitKernelValueIntegral_eq_descent r H σ T hT s hsH hrs hr hs hH hσ hI ν,
    splitKernelValueIntegral_eq_descent r H σ T hT s hsH hrs hr hs hH hσ hI ν,
    splitKernelCompactIntegral_section r s H hsH σ hrs hr hs hH hσ ν hCompatible l f,
    map_smul, splitKernelValueDescent_coefficientAction r H σ T hT s hsH hTτ]
  rfl

variable (hBasis : ∀ O : Set r.ker, IsOpen O → (1 : r.ker) ∈ O →
    ∃ K : OpenSubgroup r.ker, IsCompact (K : Set r.ker) ∧ (K : Set r.ker) ⊆ O)
  (μN : Measure r.ker) (μI : Measure I)
  [IsHaarMeasure μN] [μN.Regular] [IsMulRightInvariant μN]
  [IsHaarMeasure μI] [μI.Regular] [IsMulRightInvariant μI]
  (hCompatible : IsCompatible I μN μI ν)

include hH hσ hBasis hCompatible in
/-- A surjective coefficient map gives a surjective value integral. -/
theorem splitKernelValueIntegral_surjective (hTs : Function.Surjective T) :
    Function.Surjective (splitKernelValueIntegral r H I hI σ T hT s hrs hr hs hsH ν) := by
  obtain rfl : I = H.comap r.ker.subtype := Subgroup.ext hI
  intro w
  obtain ⟨v, rfl⟩ := hTs w
  obtain ⟨z, hz⟩ := (splitKernelCompactCoinvariantDesc_bijective r s hrs hr hs H hH hsH σ hσ ν
    hBasis μN μI hCompatible).2 (Representation.Coinvariants.mk _ v)
  obtain ⟨f, rfl⟩ := Representation.Coinvariants.mk_surjective _ z
  refine ⟨f, ?_⟩
  rw [splitKernelValueIntegral_eq_descent r H σ T hT s hsH hrs hr hs hH hσ hI ν]
  change splitKernelValueDescent r H σ T hT
    (splitKernelCompactCoinvariantDesc r s hrs hr hs H hH hsH σ hσ ν
      hCompatible.right_invariant (Representation.Coinvariants.mk _ f)) = T v
  rw [hz]
  rfl

include hH hσ hBasis hCompatible in
/-- An injective descended coefficient map forces the kernel of the value
integral into the span of the kernel relations `n · f - f`. -/
theorem splitKernelValueIntegral_mem_ker
    (hinj : Function.Injective (splitKernelValueDescent r H σ T hT))
    (f : CompactFunctions H σ)
    (hf : splitKernelValueIntegral r H I hI σ T hT s hrs hr hs hsH ν f = 0) :
    f ∈ Representation.Coinvariants.ker ((compactInduced H σ).comp r.ker.subtype) := by
  obtain rfl : I = H.comap r.ker.subtype := Subgroup.ext hI
  rw [splitKernelValueIntegral_eq_descent r H σ T hT s hsH hrs hr hs hH hσ hI ν,
    ← map_zero (splitKernelValueDescent r H σ T hT)] at hf
  have h0 := hinj hf
  rw [← Representation.Coinvariants.mk_eq_zero]
  apply (splitKernelCompactCoinvariantDesc_bijective r s hrs hr hs H hH hsH σ hσ ν
    hBasis μN μI hCompatible).1
  rw [map_zero]
  exact h0

end Section

end Langlands.Induction
