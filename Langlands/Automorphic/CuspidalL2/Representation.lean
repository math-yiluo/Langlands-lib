import Langlands.Automorphic.CuspidalL2.Decay
import Langlands.Automorphic.OperatorRealization
import Langlands.Automorphic.SliceFinitenessProof
import Langlands.Global.ArchimedeanFiniteUniformGrowthProof

/-! # Rapid decay of the vectors of a cuspidal operator realization along maximal blocks -/

noncomputable section
universe u
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Classical Topology
open NumberField

namespace Langlands.Automorphic.OperatorRealization

open Langlands.Global ContinuousRationalFunctions

variable {F : Type u} [Field F] [NumberField F] {n : ℕ} (S : OperatorRealization F n)

local instance cuspidalL2AddCommGroupRationalInvariant :
    AddCommGroup (RationalInvariantFunctions F n) := Submodule.addCommGroup _
local instance cuspidalL2AddCommGroupContinuousRational :
    AddCommGroup (ContinuousRationalFunctions F n) := Submodule.addCommGroup _
local instance cuspidalL2AddCommGroupFiniteSmoothRational :
    AddCommGroup (FiniteSmoothRationalFunctions F n) := Submodule.addCommGroup _
local instance cuspidalL2AddCommGroupAutomorphicForms :
    AddCommGroup (AutomorphicForms F n) := Submodule.addCommGroup _
local instance cuspidalL2AddCommGroupStableAutomorphic :
    AddCommGroup (StableAutomorphicFunctions F n) := Submodule.addCommGroup _
local instance cuspidalL2AddCommGroupSpace : AddCommGroup S.Space := Submodule.addCommGroup _

variable (F n) in
/-- The enveloping-algebra generator of the `k`-th real basis direction `ArchimedeanGL.lieDirection F n k`. -/
def basisGenerator (k : Fin (Module.finrank ℝ (ArchimedeanMatrix F n))) : ArchimedeanGL.EnvelopingAlgebra F n :=
  ArchimedeanGL.envelopingGenerator F n (ArchimedeanGL.complexify F n (ArchimedeanGL.lieDirection F n k))

/-- The finite-smooth ambient function underlying a realized vector. -/
abbrev ambient (f : S.Space) : FiniteSmoothRationalFunctions F n := f.val.val

theorem evaluate_toContinuous (f : S.Space) (x : AdelicGL F n) :
    evaluate F n (S.toContinuous f) x = evaluate F n (S.ambient f).val x := rfl

theorem ambient_envelopingAction (u : ArchimedeanGL.EnvelopingAlgebra F n) (f : S.Space) :
    S.ambient (S.envelopingAction u f) = finiteSmoothEnvelopingAction F n u (S.ambient f) := rfl

theorem isAutomorphicForm_ambient (f : S.Space) :
    IsAutomorphicForm F n (finiteSmoothInclusion F n (S.ambient f)) :=
  (mem_automorphicSubrepresentation F n _).mp
    (operatorCore_le F n (automorphicSubrepresentation F n).toSubmodule f.val.property)

theorem pair_eq_ofInfinite_mul_ofFinite (a : InfiniteAdelicGL F n) (b : FiniteAdelicGL F n) :
    AdelicGL.pair F n a b = AdelicGL.ofInfinite F n a * AdelicGL.ofFinite F n b :=
  AdelicGL.ext_infinite_finite F n
    (by rw [AdelicGL.infinite_pair, map_mul, AdelicGL.infinite_ofInfinite,
      AdelicGL.infinite_ofFinite, mul_one])
    (by rw [AdelicGL.finite_pair, map_mul, AdelicGL.finite_ofInfinite,
      AdelicGL.finite_ofFinite, one_mul])

/-- All enveloping derivatives of a realized vector share one open finite level. -/
theorem exists_level (f : S.Space) :
    ∃ L : Subgroup (FiniteAdelicGL F n), IsOpen (L : Set (FiniteAdelicGL F n)) ∧
      ∀ (u : ArchimedeanGL.EnvelopingAlgebra F n) (g : AdelicGL F n), ∀ l ∈ L,
        evaluate F n (S.toContinuous (S.envelopingAction u f)) (g * AdelicGL.ofFinite F n l) =
          evaluate F n (S.toContinuous (S.envelopingAction u f)) g := by
  have hf : HasFiniteLevel F n (finiteSmoothInclusion F n (S.ambient f)).val :=
    (S.isAutomorphicForm_ambient f).1
  obtain ⟨L, hLo, -, hL⟩ := hf
  refine ⟨L, hLo, fun u g l hl => ?_⟩
  have h : continuousRightAction F n (AdelicGL.ofFinite F n l)
      (finiteSmoothEnvelopingAction F n u (S.ambient f)).val =
      (finiteSmoothEnvelopingAction F n u (S.ambient f)).val :=
    finiteSmoothEnvelopingAction_preserves_level F n u ⟨L, hLo⟩ (S.ambient f) hL ⟨l, hl⟩
  exact congrArg (fun G : ContinuousRationalFunctions F n => evaluate F n G g) h

theorem finiteSmoothSlice_ambient_apply (f : S.Space) (y : FiniteAdelicGL F n)
    (g : InfiniteAdelicGL F n) :
    (finiteSmoothSlice F n y (S.ambient f)).val g =
      evaluate F n (S.toContinuous f) (AdelicGL.ofInfinite F n g * AdelicGL.ofFinite F n y) := by
  rw [S.evaluate_toContinuous, ← pair_eq_ofInfinite_mul_ofFinite]
  exact finiteSmoothSlice_apply F n y (S.ambient f) g

/-- The archimedean slices of the enveloping derivatives, with their basis derivatives. -/
theorem slice_data (f : S.Space) (u : ArchimedeanGL.EnvelopingAlgebra F n)
    (y : FiniteAdelicGL F n) :
    ∃ s : ArchimedeanGL.SmoothFunctions F n,
      (∀ g, s.val g = evaluate F n (S.toContinuous (S.envelopingAction u f))
        (AdelicGL.ofInfinite F n g * AdelicGL.ofFinite F n y)) ∧
      ∀ k g, (ArchimedeanGL.smoothDifferential F n (ArchimedeanGL.lieDirection F n k) s).val g =
        evaluate F n (S.toContinuous (S.envelopingAction (basisGenerator F n k * u) f))
          (AdelicGL.ofInfinite F n g * AdelicGL.ofFinite F n y) := by
  refine ⟨finiteSmoothSlice F n y (S.ambient (S.envelopingAction u f)),
    fun g => S.finiteSmoothSlice_ambient_apply _ y g, fun k g => ?_⟩
  have e1 := congrArg (finiteSmoothSlice F n y)
    (S.ambient_envelopingAction (basisGenerator F n k) (S.envelopingAction u f))
  have e2 := finiteSmoothSlice_envelopingAction F n (basisGenerator F n k)
    (S.ambient (S.envelopingAction u f)) y
  have e3 : ArchimedeanGL.envelopingAction F n (basisGenerator F n k) =
      ArchimedeanGL.smoothDifferential F n (ArchimedeanGL.lieDirection F n k) :=
    ArchimedeanGL.envelopingAction_real_generator F n (ArchimedeanGL.lieDirection F n k)
  have e4 := (e1.trans e2).trans
    (congrArg (fun T : Module.End ℂ (ArchimedeanGL.SmoothFunctions F n) =>
      T (finiteSmoothSlice F n y (S.ambient (S.envelopingAction u f)))) e3)
  have e5 : S.envelopingAction (basisGenerator F n k * u) f =
      S.envelopingAction (basisGenerator F n k) (S.envelopingAction u f) :=
    LinearMap.congr_fun (map_mul S.envelopingAction (basisGenerator F n k) u) f
  have e6 := S.finiteSmoothSlice_ambient_apply
    (S.envelopingAction (basisGenerator F n k) (S.envelopingAction u f)) y g
  rw [e5]
  exact (congrArg (fun s : ArchimedeanGL.SmoothFunctions F n => s.val g) e4).symm.trans e6

/-- Vanishing constant terms give the mean-value form of cuspidality used by the decay
induction. -/
theorem norm_le_of_cuspidal [CompactSpace (AdeleQuotient F)] (hS : S.IsCuspidal) {a b : ℕ}
    (h : a + b = n) (ha : 0 < a) (hb : 0 < b) (f : S.Space) (g : AdelicGL F n) (M : ℝ)
    (hM : ∀ Y : Matrix (Fin a) (Fin b) (Adeles F),
      ‖evaluate F n (S.toContinuous f) (GeneralLinear.blockUnipotent h Y * g) -
        evaluate F n (S.toContinuous f) g‖ ≤ M) :
    ‖evaluate F n (S.toContinuous f) g‖ ≤ M := by
  have h0 := S.constantTerm_eq_zero hS h ha hb f g
  have hint := integrable_constantTermIntegrand h (S.toContinuous f) g
  have key : evaluate F n (S.toContinuous f) g =
      ∫ X, (evaluate F n (S.toContinuous f) g -
        constantTermIntegrand F n h (S.toContinuous f) g X) ∂(matrixQuotientHaar F a b) := by
    rw [MeasureTheory.integral_sub (MeasureTheory.integrable_const _) hint,
      MeasureTheory.integral_const]
    unfold constantTerm at h0
    rw [h0]
    simp
  rw [key]
  calc _ ≤ M * (matrixQuotientHaar F a b).real Set.univ :=
        MeasureTheory.norm_integral_le_of_norm_le_const
          (Filter.Eventually.of_forall fun X => by
            rw [norm_sub_rev]
            exact hM (matrixLift X))
    _ = M := by simp

theorem finiteSmoothSlice_eq_smoothInfiniteSlice (f : S.Space) (y : FiniteAdelicGL F n) :
    finiteSmoothSlice F n y (S.ambient f) =
      smoothInfiniteSlice F n y (finiteSmoothInclusion F n (S.ambient f)) := rfl

/-- Each archimedean slice of a realized vector is `K`-finite, center-finite and of moderate
growth. -/
theorem slice_properties (f : S.Space) (y : FiniteAdelicGL F n) :
    Langlands.FiniteVectors.IsFiniteVector
      ((ArchimedeanGL.smoothRightAction F n).comp (standardInfiniteCompact F n).subtype)
      (finiteSmoothSlice F n y (S.ambient f)) ∧
    ArchimedeanGL.IsCenterFinite F n (finiteSmoothSlice F n y (S.ambient f)) ∧
    ∃ C : ℝ, 0 ≤ C ∧ ∃ d : ℕ, ∀ g,
      ‖(finiteSmoothSlice F n y (S.ambient f)).val g‖ ≤ C * ArchimedeanGL.matrixHeight F n g ^ d := by
  rw [S.finiteSmoothSlice_eq_smoothInfiniteSlice]
  have hf := S.isAutomorphicForm_ambient f
  have hfin : IsInfiniteFinite F n (standardInfiniteCompact F n)
      (finiteSmoothInclusion F n (S.ambient f)).val := hf.2.1
  have hcen : IsCenterFinite F n (finiteSmoothInclusion F n (S.ambient f)) := hf.2.2.1
  have hgro : HasPolynomialGrowth F n (finiteSmoothInclusion F n (S.ambient f)).val :=
    hf.2.2.2
  exact ⟨(SliceFinitenessProof.sliceFiniteness F n).2 (standardInfiniteCompact F n)
      (finiteSmoothInclusion F n (S.ambient f)) hfin y,
    (SliceFinitenessProof.sliceFiniteness F n).1
      (smoothSliceFamily F n (finiteSmoothInclusion F n (S.ambient f))) hcen y, hgro y⟩

/-- Derivatives of a slice keep a growth exponent of the slice. -/
theorem slice_derivative_growth (f : S.Space) (y : FiniteAdelicGL F n) (C : ℝ) (hC : 0 ≤ C)
    (d : ℕ) (hg : ∀ g, ‖(finiteSmoothSlice F n y (S.ambient f)).val g‖ ≤
      C * ArchimedeanGL.matrixHeight F n g ^ d) (u : ArchimedeanGL.EnvelopingAlgebra F n) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ g, ‖(finiteSmoothSlice F n y (S.ambient (S.envelopingAction u f))).val g‖ ≤
      D * ArchimedeanGL.matrixHeight F n g ^ d := by
  obtain ⟨hk, hz, -⟩ := S.slice_properties f y
  have e : finiteSmoothSlice F n y (S.ambient (S.envelopingAction u f)) =
      ArchimedeanGL.envelopingAction F n u (finiteSmoothSlice F n y (S.ambient f)) :=
    (congrArg (finiteSmoothSlice F n y) (S.ambient_envelopingAction u f)).trans
      (finiteSmoothSlice_envelopingAction F n u (S.ambient f) y)
  rw [e]
  exact ArchimedeanGL.finiteUniformDifferentialGrowth _ hk hz C hC d hg u

/-- Finitely many slices share one growth exponent. -/
theorem exists_uniform_slice_exponent (f : S.Space) (t : Finset (FiniteAdelicGL F n)) :
    ∃ d : ℕ, ∀ y ∈ t, ∃ C : ℝ, 0 ≤ C ∧ ∀ g,
      ‖(finiteSmoothSlice F n y (S.ambient f)).val g‖ ≤ C * ArchimedeanGL.matrixHeight F n g ^ d := by
  have h := fun y => (S.slice_properties f y).2.2
  choose C hC d hd using h
  refine ⟨t.sup d, fun y hy => ⟨C y, hC y, fun g => (hd y g).trans ?_⟩⟩
  exact mul_le_mul_of_nonneg_left
    (pow_le_pow_right₀ (ArchimedeanGL.one_le_matrixHeight F n g) (Finset.le_sup hy)) (hC y)

/-- Finitely many left cosets of an open subgroup cover the finite parts of a compact set. -/
theorem exists_finite_level_cover (L : Subgroup (FiniteAdelicGL F n))
    (hLo : IsOpen (L : Set (FiniteAdelicGL F n))) (Q : Set (AdelicGL F n)) (hQ : IsCompact Q) :
    ∃ t : Finset (FiniteAdelicGL F n), ∀ q ∈ Q, ∃ y ∈ t, y⁻¹ * AdelicGL.finite F n q ∈ L := by
  have hQf : IsCompact (AdelicGL.finite F n '' Q) := hQ.image (map_continuous _)
  obtain ⟨t, -, ht⟩ := hQf.elim_nhds_subcover (fun y => (fun z => y⁻¹ * z) ⁻¹' (L : Set _))
    (fun y _ => (hLo.preimage (continuous_const.mul continuous_id)).mem_nhds
      (show y⁻¹ * y ∈ L from (inv_mul_cancel y).symm ▸ L.one_mem))
  refine ⟨t, fun q hq => ?_⟩
  obtain ⟨y, hy, hyq⟩ := Set.mem_iUnion₂.mp (ht ⟨q, hq, rfl⟩)
  exact ⟨y, hy, hyq⟩

/-- One growth exponent, valid for every enveloping derivative of a realized vector on every
compact set whose finite parts lie in the finitely many level cosets meeting `Q`. -/
theorem exists_uniform_growth (f : S.Space) (L : Subgroup (FiniteAdelicGL F n))
    (hLo : IsOpen (L : Set (FiniteAdelicGL F n)))
    (hlevel : ∀ (u : ArchimedeanGL.EnvelopingAlgebra F n) (g : AdelicGL F n), ∀ l ∈ L,
      evaluate F n (S.toContinuous (S.envelopingAction u f)) (g * AdelicGL.ofFinite F n l) =
        evaluate F n (S.toContinuous (S.envelopingAction u f)) g)
    (Q : Set (AdelicGL F n)) (hQ : IsCompact Q) :
    ∃ (d : ℕ) (F₀ : Set (FiniteAdelicGL F n)), (∀ q ∈ Q, AdelicGL.finite F n q ∈ F₀) ∧
      ∀ (u : ArchimedeanGL.EnvelopingAlgebra F n) (Q' : Set (AdelicGL F n)), IsCompact Q' →
        (∀ q ∈ Q', AdelicGL.finite F n q ∈ F₀) → ∃ C : ℝ, ∀ x, ∀ q ∈ Q',
          ‖evaluate F n (S.toContinuous (S.envelopingAction u f))
              (AdelicGL.ofInfinite F n (torInf F n x) * q)‖ ≤
            C * ArchimedeanGL.matrixHeight F n (torInf F n x) ^ d := by
  refine (exists_finite_level_cover L hLo Q hQ).elim fun t ht => ?_
  refine (S.exists_uniform_slice_exponent f t).elim fun d hd => ?_
  refine ⟨d, {z | ∃ y ∈ t, y⁻¹ * z ∈ L}, ht, fun u Q' hQ' hQ'F => ?_⟩
  have hD : ∀ y ∈ t, ∃ D : ℝ, 0 ≤ D ∧ ∀ g,
      ‖(finiteSmoothSlice F n y (S.ambient (S.envelopingAction u f))).val g‖ ≤
        D * ArchimedeanGL.matrixHeight F n g ^ d := fun y hy =>
    (hd y hy).elim fun C hC => S.slice_derivative_growth f y C hC.1 d hC.2 u
  choose! D hD0 hD using hD
  have hMex : ∃ M : ℝ, ∀ q ∈ Q',
      ArchimedeanGL.matrixHeight F n (AdelicGL.infinite F n q) ≤ M :=
    (hQ'.image ((ArchimedeanGL.continuous_matrixHeight F n).comp
      (map_continuous (AdelicGL.infinite F n)))).bddAbove.elim
      fun M hM => ⟨M, fun q hq => hM ⟨q, hq, rfl⟩⟩
  refine hMex.elim fun M hM => ⟨(∑ y ∈ t, D y) * M ^ d, fun x q hq => ?_⟩
  have hmem : ∃ y ∈ t, y⁻¹ * AdelicGL.finite F n q ∈ L := hQ'F q hq
  refine hmem.elim fun y hy' => ?_
  have hy : y ∈ t := hy'.1
  have hyq : y⁻¹ * AdelicGL.finite F n q ∈ L := hy'.2
  have hq1 := AdelicGL.eq_ofInfinite_mul_ofFinite F n q
  have hsplit : AdelicGL.ofInfinite F n (torInf F n x) * q =
      AdelicGL.pair F n (torInf F n x * AdelicGL.infinite F n q) y *
        AdelicGL.ofFinite F n (y⁻¹ * AdelicGL.finite F n q) := by
    calc AdelicGL.ofInfinite F n (torInf F n x) * q
        = AdelicGL.ofInfinite F n (torInf F n x) * (AdelicGL.ofInfinite F n
            (AdelicGL.infinite F n q) * AdelicGL.ofFinite F n (AdelicGL.finite F n q)) :=
          congrArg _ hq1
      _ = AdelicGL.ofInfinite F n (torInf F n x) * AdelicGL.ofInfinite F n
            (AdelicGL.infinite F n q) * (AdelicGL.ofFinite F n y *
              AdelicGL.ofFinite F n (y⁻¹ * AdelicGL.finite F n q)) := by
          rw [← map_mul (AdelicGL.ofFinite F n), mul_inv_cancel_left, mul_assoc]
      _ = _ := by
          rw [pair_eq_ofInfinite_mul_ofFinite, map_mul (AdelicGL.ofInfinite F n),
            mul_assoc (_ * _) (AdelicGL.ofFinite F n y)]
  have hH1 : 1 ≤ ArchimedeanGL.matrixHeight F n (AdelicGL.infinite F n q) :=
    ArchimedeanGL.one_le_matrixHeight F n _
  have hM0 : 0 ≤ M := le_trans zero_le_one (hH1.trans (hM q hq))
  have heq : evaluate F n (S.toContinuous (S.envelopingAction u f))
      (AdelicGL.ofInfinite F n (torInf F n x) * q) =
      (finiteSmoothSlice F n y (S.ambient (S.envelopingAction u f))).val
        (torInf F n x * AdelicGL.infinite F n q) :=
    (congrArg (evaluate F n (S.toContinuous (S.envelopingAction u f))) hsplit).trans
      ((hlevel u _ _ hyq).trans
        ((congrArg (evaluate F n (S.toContinuous (S.envelopingAction u f)))
          (pair_eq_ofInfinite_mul_ofFinite _ _)).trans
          (S.finiteSmoothSlice_ambient_apply _ y _).symm))
  have hDy := hD y hy (torInf F n x * AdelicGL.infinite F n q)
  have hHt : 0 ≤ ArchimedeanGL.matrixHeight F n (torInf F n x) :=
    le_trans zero_le_one (ArchimedeanGL.one_le_matrixHeight F n _)
  calc _ = _ := congrArg norm heq
    _ ≤ D y * ArchimedeanGL.matrixHeight F n (torInf F n x * AdelicGL.infinite F n q) ^ d := hDy
    _ ≤ D y * (ArchimedeanGL.matrixHeight F n (torInf F n x) * M) ^ d := by
        refine mul_le_mul_of_nonneg_left (pow_le_pow_left₀ ?_ ?_ d) (hD0 y hy)
        · exact le_trans zero_le_one (ArchimedeanGL.one_le_matrixHeight F n _)
        · exact (ArchimedeanGL.matrixHeight_mul_le F n _ _).trans
            (mul_le_mul_of_nonneg_left (hM q hq) hHt)
    _ = D y * M ^ d * ArchimedeanGL.matrixHeight F n (torInf F n x) ^ d := by
        rw [mul_pow]; ring
    _ ≤ (∑ y ∈ t, D y) * M ^ d * ArchimedeanGL.matrixHeight F n (torInf F n x) ^ d := by
        refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ?_ (pow_nonneg hM0 d))
          (pow_nonneg hHt d)
        exact Finset.single_le_sum (fun z hz => hD0 z hz) hy

/-- **Rapid decay along a maximal block for an actual cuspidal realization.** For a vector
`f` of a cuspidal operator realization and a compact set `Q`, there is one exponent `d` such
that along every maximal block `(a, b)` and for every `N`, `f (torInf x * q)` is bounded by
`C * exp (-N ℓ) * H(torInf x)^d` whenever every across-the-block gap `x_r - x_p` is at most
`-ℓ ≤ 0`. -/
theorem exists_blockDecay [CompactSpace (AdeleQuotient F)] (hS : S.IsCuspidal) (f : S.Space)
    (Q : Set (AdelicGL F n)) (hQ : IsCompact Q) :
    ∃ d : ℕ, ∀ {a b : ℕ} (h : a + b = n), 0 < a → 0 < b → ∀ N : ℕ, ∃ C : ℝ,
      ∀ (x : Fin n → ℝ) (ℓ : ℝ), 0 ≤ ℓ →
        (∀ p r, x (finSumFinEquiv.trans (finCongr h) (Sum.inr r)) -
          x (finSumFinEquiv.trans (finCongr h) (Sum.inl p)) ≤ -ℓ) →
        ∀ q ∈ Q, ‖evaluate F n (S.toContinuous f)
            (AdelicGL.ofInfinite F n (torInf F n x) * q)‖ ≤
          C * Real.exp (-(N * ℓ)) * ArchimedeanGL.matrixHeight F n (torInf F n x) ^ d := by
  obtain ⟨L, hLo, hlevel⟩ := S.exists_level f
  obtain ⟨d, F₀, hQF, hgrowth⟩ := S.exists_uniform_growth f L hLo hlevel Q hQ
  refine ⟨d, fun {a b} h ha hb N => ?_⟩
  obtain ⟨C, hC⟩ := blockDecay_of_cuspidal F n h
    (fun u => evaluate F n (S.toContinuous (S.envelopingAction u f)))
    (fun k u => basisGenerator F n k * u)
    (fun u γ g => evaluate_rational F n _ γ g)
    L hLo hlevel (fun u y => S.slice_data f u y)
    (fun u g M hM => S.norm_le_of_cuspidal hS h ha hb _ g M hM)
    F₀ (fun x => ArchimedeanGL.matrixHeight F n (torInf F n x) ^ d)
    (fun u Q' hQ' hQ'F => hgrowth u Q' hQ' hQ'F) N 1 Q hQ hQF
  refine ⟨C, fun x ℓ hℓ hx q hq => ?_⟩
  have := hC x ℓ hℓ hx q hq
  simpa only [map_one, Module.End.one_apply] using this

end Langlands.Automorphic.OperatorRealization
