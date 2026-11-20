import Langlands.Automorphic.ConstantTerm
import Langlands.Automorphic.CuspidalL2.Representation
import Langlands.Global.AdelesLocallyCompactProof

/-! # Polynomial growth of the adelic two-block constant term -/

noncomputable section
universe u

open scoped BigOperators Topology
set_option autoImplicit false

namespace Langlands.Automorphic

open Langlands.Global Langlands.GeneralLinear ArchimedeanGL ContinuousRationalFunctions
open MeasureTheory Set

variable (F : Type u) [Field F] [NumberField F]
variable [CompactSpace (AdeleQuotient F)] {a b n : ℕ} (h : a + b = n)

local notation "A" => Matrix (Fin a) (Fin b) (Adeles F)
local notation "Q" => Matrix (Fin a) (Fin b) (AdeleQuotient F)

local instance constantTermGrowthRationalAddCommGroup :
    AddCommGroup (RationalInvariantFunctions F n) := Submodule.addCommGroup _

local instance constantTermGrowthContinuousAddCommGroup :
    AddCommGroup (ContinuousRationalFunctions F n) := Submodule.addCommGroup _

private theorem exists_matrixQuotient_compact_representatives :
    ∃ K : Set A, IsCompact K ∧ ∀ q : Q, ∃ X ∈ K, matrixQuotientMap X = q := by
  classical
  let : LocallyCompactSpace (Adeles F) := adeles_locallyCompactSpace F
  let : LocallyCompactSpace A :=
    inferInstanceAs (LocallyCompactSpace (Fin a → Fin b → Adeles F))
  let p : A → Q := matrixQuotientMap
  have hp := isOpenQuotientMap_matrixQuotientMap (K := F) a b
  choose K hK hnh using fun q : Q => exists_compact_mem_nhds (matrixLift q)
  have hcover (q : Q) : p '' K q ∈ 𝓝 q := by
    simpa only [p, matrixQuotientMap_matrixLift] using hp.isOpenMap.image_mem_nhds (hnh q)
  obtain ⟨t, _, ht⟩ := (isCompact_univ : IsCompact (univ : Set Q)).elim_nhds_subcover
    (fun q => p '' K q) (fun q _ => hcover q)
  refine ⟨⋃ q ∈ t, K q, t.finite_toSet.isCompact_biUnion (fun q _ => hK q), ?_⟩
  intro q
  obtain ⟨q', hq', X, hX, he⟩ := mem_iUnion₂.mp (ht (mem_univ q))
  exact ⟨X, mem_iUnion₂.mpr ⟨q', hq', hX⟩, he⟩

/-- A compact set of representatives for the matrix quotient used to take the constant term. -/
def matrixQuotientCompactRepresentatives (F : Type u) [Field F] [NumberField F]
    [CompactSpace (AdeleQuotient F)] (a b : ℕ) :
    Set (Matrix (Fin a) (Fin b) (Adeles F)) :=
  Classical.choose (exists_matrixQuotient_compact_representatives (a := a) (b := b) F)

theorem isCompact_matrixQuotientCompactRepresentatives :
    IsCompact (matrixQuotientCompactRepresentatives F a b) :=
  (Classical.choose_spec
    (exists_matrixQuotient_compact_representatives (a := a) (b := b) F)).1

theorem exists_mem_matrixQuotientCompactRepresentatives (q : Q) :
    ∃ X ∈ matrixQuotientCompactRepresentatives F a b, matrixQuotientMap X = q :=
  (Classical.choose_spec
    (exists_matrixQuotient_compact_representatives (a := a) (b := b) F)).2 q

local instance constantTermGrowthMeasurableSpace : MeasurableSpace Q := borel _
local instance constantTermGrowthBorelSpace : BorelSpace Q := ⟨rfl⟩

set_option maxHeartbeats 600000 in
/-- At a fixed finite argument, the constant term has polynomial growth in the
ambient archimedean group. -/
theorem constantTerm_hasPolynomialGrowth
    (f : ContinuousRationalFunctions F n) (L : OpenSubgroup (FiniteAdelicGL F n))
    (hfL : f ∈ levelSubmodule F n L.toSubgroup)
    (hf : HasPolynomialGrowth F n f) (d : FiniteAdelicGL F n) :
    ArchimedeanGL.HasPolynomialGrowth F n
      (fun g => constantTerm F n h f (AdelicGL.pair F n g d)) := by
  classical
  let w (X : A) : AdelicGL F n := blockUnipotent h X * AdelicGL.ofFinite F n d
  let K := matrixQuotientCompactRepresentatives F a b
  let W := w '' K
  have hW : IsCompact W :=
    (isCompact_matrixQuotientCompactRepresentatives F).image
      ((continuous_blockUnipotent h).mul continuous_const)
  obtain ⟨t, ht⟩ :=
    OperatorRealization.exists_finite_level_cover L.toSubgroup L.isOpen W hW
  choose C hC e he using hf
  let E := t.sup e
  let D := ∑ y ∈ t, C y
  have hD : 0 ≤ D := Finset.sum_nonneg fun y _ => hC y
  have hc : Continuous (fun q : AdelicGL F n => matrixHeight F n (AdelicGL.infinite F n q)) :=
    (continuous_matrixHeight F n).comp (AdelicGL.infinite F n).continuous
  obtain ⟨B, hB⟩ := hW.bddAbove_image hc.continuousOn
  let B' := max 1 B
  have hB' : 0 ≤ B' := zero_le_one.trans (le_max_left _ _)
  refine ⟨D * B'^E, mul_nonneg hD (pow_nonneg hB' _), E, fun g => ?_⟩
  have hnorm (q : Q) :
      ‖constantTermIntegrand F n h f (AdelicGL.pair F n g d) q‖ ≤
        (D * B'^E) * matrixHeight F n g ^ E := by
    obtain ⟨X, hX, rfl⟩ := exists_mem_matrixQuotientCompactRepresentatives F q
    have hw : w X ∈ W := ⟨X, hX, rfl⟩
    obtain ⟨y, hy, hl⟩ := ht (w X) hw
    let l : L := ⟨y⁻¹ * AdelicGL.finite F n (w X), hl⟩
    let x := AdelicGL.infinite F n (w X) * g
    have hp : blockUnipotent h X * AdelicGL.pair F n g d =
        AdelicGL.pair F n x y * AdelicGL.ofFinite F n l.val := by
      apply (AdelicGL.split F n).injective
      change (AdelicGL.infinite F n _, AdelicGL.finite F n _) =
        (AdelicGL.infinite F n _, AdelicGL.finite F n _)
      simp only [x, w, l, map_mul, AdelicGL.ofFinite_eq_pair, AdelicGL.infinite_pair,
        AdelicGL.finite_pair, mul_one, mul_inv_cancel_left]
    have hfixed := congrArg (fun f' => evaluate F n f' (AdelicGL.pair F n x y)) (hfL l)
    change evaluate F n f (AdelicGL.pair F n x y * AdelicGL.ofFinite F n l.val) =
      evaluate F n f (AdelicGL.pair F n x y) at hfixed
    rw [constantTermIntegrand_mk, hp, hfixed]
    have hCy : C y ≤ D := Finset.single_le_sum (fun y _ => hC y) hy
    have hh : matrixHeight F n x ≤ B' * matrixHeight F n g :=
      (matrixHeight_mul_le F n _ _).trans (mul_le_mul_of_nonneg_right
        ((hB ⟨w X, hw, rfl⟩).trans (le_max_right _ _)) (matrixHeight_nonneg F n g))
    calc
      _ ≤ C y * matrixHeight F n x ^ e y := he y x
      _ ≤ D * matrixHeight F n x ^ E :=
        mul_le_mul hCy (pow_le_pow_right₀ (one_le_matrixHeight F n x) (Finset.le_sup hy))
          (pow_nonneg (matrixHeight_nonneg F n x) _) hD
      _ ≤ D * (B' * matrixHeight F n g) ^ E :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (matrixHeight_nonneg F n x) hh _) hD
      _ = (D * B'^E) * matrixHeight F n g ^ E := by rw [mul_pow, mul_assoc]
  simpa only [constantTerm, Measure.real_def, matrixQuotientHaar_univ, ENNReal.toReal_one, mul_one] using
    (norm_integral_le_of_norm_le_const (μ := matrixQuotientHaar F a b)
      (Filter.Eventually.of_forall hnorm))

end Langlands.Automorphic
