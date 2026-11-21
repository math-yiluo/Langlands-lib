import Langlands.Global.AdelicGLTransport
import Langlands.Global.AdelicFunctoriality.UnramifiedUnitNorm
import Langlands.Global.FiniteAdelicGL.PadicComparison
import Langlands.Representation.RankinSelberg.FieldTransport.Padic
import Langlands.Representation.Unramified.HeckeOperators

/-! # Arithmetic transport of the standard spherical double cosets and Haar measure -/

noncomputable section

namespace Langlands.Global.FiniteAdelicGL

open AdelicFunctoriality AdelicGLTransport CompletionPadic Correspondence Unramified
open GeneralLinear.Iwasawa (diagonalUnits_val diagonalUnits_mem)
open scoped WithZero

universe uK uL

set_option autoImplicit false

variable {K : Type uK} {L : Type uL} [Field K] [NumberField K] [Field L] [NumberField L]

/-- Corresponding finite completions have the same canonical residue cardinality. -/
theorem residueCardinality_finitePlaceEquiv (a : L ≃+* K) (v : FinitePlace K) :
    (padicField (finitePlaceEquiv a v)).canonicalTopologicalData.residueCardinality =
      (padicField v).canonicalTopologicalData.residueCardinality := by
  let w := finitePlaceEquiv a v
  let e := finiteCompletionEquiv a v
  have h (x : FiniteCompletion L w) :
      x ∈ (padicField w).canonicalTopologicalData.Integers ↔
        e x ∈ (padicField v).canonicalTopologicalData.Integers := by
    rw [← mem_localIntegers_iff_canonical L w, ← mem_localIntegers_iff_canonical K v]
    exact (finiteCompletionEquiv_integral a v x).symm
  let integersEquiv : (padicField w).canonicalTopologicalData.Integers ≃+*
      (padicField v).canonicalTopologicalData.Integers :=
    { toEquiv := e.toEquiv.subtypeEquiv h
      map_mul' := fun x y => Subtype.ext (e.map_mul (x : FiniteCompletion L w) y)
      map_add' := fun x y => Subtype.ext (e.map_add (x : FiniteCompletion L w) y) }
  exact Nat.card_congr (IsLocalRing.ResidueField.mapEquiv integersEquiv).toEquiv

/-- The canonical uniformizer of the completion has valuation `exp (-1)`. -/
theorem completion_uniformizer_value (v : FinitePlace K) :
    (Valued.v : Valuation (FiniteCompletion K v) ℤᵐ⁰)
      ((padicField v).canonicalTopologicalData.uniformizerUnit : FiniteCompletion K v) =
        WithZero.exp (-1) := by
  rw [← discreteValuation_eq_of_vle (padicField v).canonicalTopologicalData Valued.v
    (topologicalData_vle v) (v.valuedAdicCompletion_surjective K)]
  simpa only [zpow_one] using
    LocalFactor.PadicAbelian.uniformizerUnit_zpow_value (padicField v).canonicalTopologicalData 1

private theorem localEquiv_diagonalUnits (a : L ≃+* K) (v : FinitePlace K) (n : ℕ)
    (d : Fin n → (FiniteCompletion L (finitePlaceEquiv a v))ˣ) :
    localEquiv n a v (GeneralLinear.Iwasawa.diagonalUnits d) =
      GeneralLinear.Iwasawa.diagonalUnits
        (fun j => Units.map (finiteCompletionEquiv a v).toMonoidHom (d j)) := by
  apply Units.ext
  apply Matrix.ext
  intro i j
  change finiteCompletionEquiv a v ((GeneralLinear.Iwasawa.diagonalUnits d).val i j) = _
  simp only [diagonalUnits_val, Matrix.diagonal_apply]
  split_ifs <;> simp

private theorem localEquiv_standardDiagonal_mem (a : L ≃+* K) (v : FinitePlace K)
    (r : ℕ) (i : Fin (r + 2)) :
    localEquiv (r + 1) a v (standardDiagonal (padicField (finitePlaceEquiv a v)) r i) ∈
      DoubleCoset.doubleCoset (standardDiagonal (padicField v) r i)
        (sphericalSubgroup (padicField v) r) (sphericalSubgroup (padicField v) r) := by
  let w := finitePlaceEquiv a v
  let e := finiteCompletionEquiv a v
  let sourceUniformizer := (padicField w).canonicalTopologicalData.uniformizerUnit
  let targetUniformizer := (padicField v).canonicalTopologicalData.uniformizerUnit
  let ratio := Units.map e.toMonoidHom sourceUniformizer * targetUniformizer⁻¹
  have hratio : (Valued.v : Valuation (FiniteCompletion K v) ℤᵐ⁰) (ratio : FiniteCompletion K v) =
      1 := by
    change Valued.v (e (sourceUniformizer : FiniteCompletion L w) *
      ((targetUniformizer⁻¹ : (FiniteCompletion K v)ˣ) : FiniteCompletion K v)) = 1
    rw [Units.val_inv_eq_inv_val, map_mul, map_inv₀, finiteCompletionEquiv_valuation,
      completion_uniformizer_value, completion_uniformizer_value]
    exact mul_inv_cancel₀ WithZero.exp_ne_zero
  let d : Fin (r + 1) → (FiniteCompletion K v)ˣ :=
    fun j => if j.val < i.val then ratio else 1
  have hd : GeneralLinear.Iwasawa.diagonalUnits d ∈ sphericalSubgroup (padicField v) r := by
    let := (padicField v).canonicalTopologicalData.valuativeRel
    change GeneralLinear.Iwasawa.diagonalUnits d ∈
      Conductor.integralSubgroup (ValuativeRel.valuation (FiniteCompletion K v)).integer r
    apply diagonalUnits_mem
    intro j
    have he := valuativeRel_valuation_isEquiv (padicField v).canonicalTopologicalData Valued.v
      (topologicalData_vle v)
    rw [he.eq_one_iff_eq_one]
    by_cases hj : j.val < i.val
    · simpa only [d, ite_eq_left hj] using hratio
    · simp [d, hj]
  rw [DoubleCoset.mem_doubleCoset]
  refine ⟨GeneralLinear.Iwasawa.diagonalUnits d, hd, 1, one_mem _, ?_⟩
  rw [mul_one]
  unfold standardDiagonal
  rw [localEquiv_diagonalUnits, ← map_mul]
  congr 1
  funext j
  by_cases hj : j.val < i.val <;> simp [d, ratio, hj, Pi.mul_apply, e, sourceUniformizer,
    targetUniformizer, w]

/-- The local arithmetic isomorphism preserves and reflects spherical subgroup membership. -/
theorem localEquiv_mem_sphericalSubgroup_iff (a : L ≃+* K) (v : FinitePlace K)
    (r : ℕ) (g : FiniteLocalGL L (r + 1) (finitePlaceEquiv a v)) :
    localEquiv (r + 1) a v g ∈ sphericalSubgroup (padicField v) r ↔
      g ∈ sphericalSubgroup (padicField (finitePlaceEquiv a v)) r := by
  rw [← localIntegral_eq_sphericalSubgroup K v r,
    ← localIntegral_eq_sphericalSubgroup L (finitePlaceEquiv a v) r]
  exact localEquiv_mem_localIntegral_iff (r + 1) a v g

/-- Arithmetic transport preserves and reflects membership in each standard spherical double
coset, including the identity coset and the scalar uniformizer coset. -/
theorem localEquiv_mem_standardDoubleCoset_iff (a : L ≃+* K) (v : FinitePlace K)
    (r : ℕ) (i : Fin (r + 2)) (g : FiniteLocalGL L (r + 1) (finitePlaceEquiv a v)) :
    localEquiv (r + 1) a v g ∈
        DoubleCoset.doubleCoset (standardDiagonal (padicField v) r i)
          (sphericalSubgroup (padicField v) r) (sphericalSubgroup (padicField v) r) ↔
      g ∈ DoubleCoset.doubleCoset (standardDiagonal (padicField (finitePlaceEquiv a v)) r i)
        (sphericalSubgroup (padicField (finitePlaceEquiv a v)) r)
        (sphericalSubgroup (padicField (finitePlaceEquiv a v)) r) := by
  let w := finitePlaceEquiv a v
  let f := localEquiv (r + 1) a v
  let source := sphericalSubgroup (padicField w) r
  let target := sphericalSubgroup (padicField v) r
  let t := standardDiagonal (padicField w) r i
  change f g ∈ DoubleCoset.doubleCoset (standardDiagonal (padicField v) r i) target target ↔
    g ∈ DoubleCoset.doubleCoset t source source
  have hsub (x : FiniteLocalGL L (r + 1) w) : f x ∈ target ↔ x ∈ source :=
    localEquiv_mem_sphericalSubgroup_iff a v r x
  have ht : f t ∈ DoubleCoset.doubleCoset (standardDiagonal (padicField v) r i) target target :=
    localEquiv_standardDiagonal_mem a v r i
  rw [← DoubleCoset.doubleCoset_eq_of_mem ht]
  simp only [DoubleCoset.mem_doubleCoset]
  constructor
  · rintro ⟨x, hx, y, hy, h⟩
    obtain ⟨x, rfl⟩ := f.surjective x
    obtain ⟨y, rfl⟩ := f.surjective y
    exact ⟨x, (hsub x).mp hx, y, (hsub y).mp hy, f.injective (by
      simpa only [map_mul] using h)⟩
  · rintro ⟨x, hx, y, hy, rfl⟩
    exact ⟨f x, (hsub x).mpr hx, f y, (hsub y).mpr hy, by
      simp only [map_mul]⟩

section Haar

open MeasureTheory

private def localEquivCanonical (a : L ≃+* K) (v : FinitePlace K) (n : ℕ) :
    @ContinuousMulEquiv (FiniteLocalGL L n (finitePlaceEquiv a v))
      ((padicField (finitePlaceEquiv a v)).canonicalGeneralLinearTopology n)
      (FiniteLocalGL K n v)
      ((padicField v).canonicalGeneralLinearTopology n) _ _ := by
  let f := localEquiv n a v
  refine @ContinuousMulEquiv.mk (FiniteLocalGL L n (finitePlaceEquiv a v))
    ((padicField (finitePlaceEquiv a v)).canonicalGeneralLinearTopology n)
    (FiniteLocalGL K n v) ((padicField v).canonicalGeneralLinearTopology n) _ _
    f.toMulEquiv ?_ ?_
  · change @Continuous _ _
      ((padicField (finitePlaceEquiv a v)).canonicalGeneralLinearTopology n)
      ((padicField v).canonicalGeneralLinearTopology n) (fun g => f g)
    rw [← localGL_topology_eq L (finitePlaceEquiv a v) n, ← localGL_topology_eq K v n]
    exact f.continuous
  · change @Continuous _ _
      ((padicField v).canonicalGeneralLinearTopology n)
      ((padicField (finitePlaceEquiv a v)).canonicalGeneralLinearTopology n) (fun g => f.symm g)
    rw [← localGL_topology_eq K v n, ← localGL_topology_eq L (finitePlaceEquiv a v) n]
    exact f.symm.continuous

local instance sphericalArithmeticTopology {F : Type*} [Field F] [NumberField F]
    (v : FinitePlace F) (n : ℕ) : TopologicalSpace (FiniteLocalGL F n v) :=
  (padicField v).canonicalGeneralLinearTopology n

local instance sphericalArithmeticTopologicalGroup {F : Type*} [Field F] [NumberField F]
    (v : FinitePlace F) (n : ℕ) : IsTopologicalGroup (FiniteLocalGL F n v) :=
  (padicField v).canonicalGeneralLinearTopologicalGroup n

local instance sphericalArithmeticMeasurable {F : Type*} [Field F] [NumberField F]
    (v : FinitePlace F) (n : ℕ) : MeasurableSpace (FiniteLocalGL F n v) :=
  borel _

local instance sphericalArithmeticBorel {F : Type*} [Field F] [NumberField F]
    (v : FinitePlace F) (n : ℕ) : BorelSpace (FiniteLocalGL F n v) :=
  ⟨rfl⟩

/-- The local arithmetic isomorphism preserves Haar measure normalized to give the spherical
subgroup mass one. The two measurable spaces are the canonical p-adic Borel spaces. -/
theorem measurePreserving_localEquiv_sphericalHaar (a : L ≃+* K) (v : FinitePlace K) (r : ℕ) :
    MeasurePreserving
      (fun g : FiniteLocalGL L (r + 1) (finitePlaceEquiv a v) => localEquiv (r + 1) a v g)
      (sphericalHaar (padicField (finitePlaceEquiv a v)) r) (sphericalHaar (padicField v) r) := by
  let f := localEquivCanonical a v (r + 1)
  refine ⟨f.continuous.measurable, ?_⟩
  exact RankinSelberg.FieldTransport.normalizedCompactOpenHaar_map f
    (sphericalOpenSubgroup (padicField (finitePlaceEquiv a v)) r)
    (sphericalOpenSubgroup_isCompact (padicField (finitePlaceEquiv a v)) r)
    (sphericalOpenSubgroup (padicField v) r) (sphericalOpenSubgroup_isCompact (padicField v) r)
    (localEquiv_mem_sphericalSubgroup_iff a v r)

end Haar

end Langlands.Global.FiniteAdelicGL
