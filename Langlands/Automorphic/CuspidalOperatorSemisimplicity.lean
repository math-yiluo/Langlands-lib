import Langlands.Automorphic.CuspidalAdmissible.SymmetricKernelSeparation
import Langlands.Automorphic.CuspidalAdmissible.Separation
import Langlands.Automorphic.CuspidalAdmissible.AdmissibilityReduction
import Langlands.Automorphic.ContragredientHeckeTransfer
import Langlands.Automorphic.OperatorRealizationCountable
import Langlands.Automorphic.OperatorSubquotient
import Langlands.Global.AdelicGLSiegelFinitenessProof
import Langlands.Global.HeckeCharacter
import Mathlib.RepresentationTheory.Semisimple

/-! Algebraic semisimplicity of actual cuspidal realizations at unitary central character. -/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

namespace Langlands.Automorphic.CuspidalAdmissible

open Global NumberField MeasureTheory Polynomial FiniteVectors
open OperatorDeterminantSlice

attribute [local instance] subquotientRationalGroup subquotientContinuousGroup
  subquotientSmoothGroup subquotientFormGroup subquotientStableGroup subquotientRealizationGroup

private theorem invariantForm_orthogonal_stable
    {G V : Type*} [Group G] [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    {ρ : Representation ℂ G V} (b : InvariantPositiveForm ρ)
    (hb : ∀ x y, inner ℂ x y = b.inner x y)
    (U : Submodule ℂ V) (hU : ∀ g v, v ∈ U → ρ g v ∈ U) :
    ∀ g v, v ∈ Uᗮ → ρ g v ∈ Uᗮ := by
  intro g v hv
  apply (U.mem_orthogonal' _).mpr
  intro y hy
  have hy' : ρ g (ρ g⁻¹ y) = y := by
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one]
    rfl
  calc
    inner ℂ (ρ g v) y = inner ℂ (ρ g v) (ρ g (ρ g⁻¹ y)) := by rw [hy']
    _ = inner ℂ v (ρ g⁻¹ y) := by simpa only [hb] using b.invariant g v (ρ g⁻¹ y)
    _ = 0 := (U.mem_orthogonal' _).mp hv _ (hU g⁻¹ y hy)

variable {F : Type u} [Field F] [NumberField F] {n : ℕ} (S : OperatorRealization F n)

private theorem exists_compactCasimir_annihilator_vector (v : S.Space) :
    ∃ p : ℂ[X], p ≠ 0 ∧ aeval (compactCasimirOperator S) p v = 0 := by
  let Z := orbitSpan S.compactRepresentation v
  have : Module.Finite ℂ Z := S.compactRepresentation_isFiniteVector v
  let W : Submodule ℂ (Unit → S.Space) := Submodule.pi Set.univ (fun _ => Z)
  have hW (k : standardInfiniteCompact F n) : IsPiStable (S.compactRepresentation k) W := by
    intro w hw
    apply Submodule.mem_pi.mpr
    intro i hi
    exact (orbitSubrepresentation S.compactRepresentation v).apply_mem_toSubmodule k
      (Submodule.mem_pi.mp hw i hi)
  have hZ : ∀ z ∈ Z, compactCasimirOperator S z ∈ Z := by
    intro z hz
    have hw : (fun _ : Unit => z) ∈ W := Submodule.mem_pi.mpr fun _ _ => hz
    have h := isPiStable_compactSquareOperator S.compactDualDerivative W hW _ hw
    rw [compactCasimirOperator_eq]
    exact Submodule.mem_pi.mp h () (Set.mem_univ ())
  exact exists_aeval_apply_eq_zero _ Z hZ (self_mem_orbitSpan _ v)

set_option maxHeartbeats 650000 in
private theorem isSemisimpleRepresentation_of_finite_casimirKernels (b : S.UnitaryForm)
    (hfinite : ∀ L q p, q ≠ 0 → p ≠ 0 → FiniteDimensional ℂ
      (fixedPolynomialKernels S.finiteRepresentation (casimirOperator S)
        (compactCasimirOperator S) L q p)) :
    S.representation.IsSemisimpleRepresentation := by
  let _ : NormedAddCommGroup S.Space := b.finiteForm.toInnerProductCore.toNormedAddCommGroup
  let _ : InnerProductSpace ℂ S.Space :=
    InnerProductSpace.ofCore b.finiteForm.toInnerProductCore.toCore
  refine ⟨fun U => ?_⟩
  let P := U.toSubmodule
  have hPfinite (g : FiniteAdelicGL F n) (v : S.Space) (hv : v ∈ P) :
      S.finiteRepresentation g v ∈ P := U.apply_mem_toSubmodule (finiteOperator F n g) hv
  have hPcompact (k : standardInfiniteCompact F n) (v : S.Space) (hv : v ∈ P) :
      S.compactRepresentation k v ∈ P := U.apply_mem_toSubmodule (compactOperator F n k) hv
  have hPenv (a : ArchimedeanGL.EnvelopingAlgebra F n) (v : S.Space) (hv : v ∈ P) :
      S.envelopingAction a v ∈ P := U.apply_mem_toSubmodule (differentialOperator F n a) hv
  have hlevels (v : S.Space) : ∃ L : OpenSubgroup (FiniteAdelicGL F n),
      IsCompact (L : Set (FiniteAdelicGL F n)) ∧ v ∈ fixedVectors S.finiteRepresentation L.toSubgroup := by
    obtain ⟨K, hK⟩ := S.finiteRepresentation_isSmooth v
    obtain ⟨L, hLK, hLc⟩ := OperatorRealization.exists_compact_openSubgroup_le K
    exact ⟨L, hLc, fun l => hK ⟨l.val, hLK l.property⟩⟩
  have hcompl : IsCompl P Pᗮ :=
    isCompl_orthogonal_of_finite_fixedPolynomialKernels S.finiteRepresentation
      (casimirOperator S) (compactCasimirOperator S) S.finiteRepresentation_isSmooth
      b.finiteForm (fun _ _ => rfl) hlevels
      (isCoreSymm_casimirOperator b) (isCoreSymm_compactCasimirOperator b)
      (exists_casimir_annihilator_vector S) (exists_compactCasimir_annihilator_vector S)
      (finiteRepresentation_casimirOperator S)
      (fun g => S.finiteRepresentation_envelopingAction g (ArchimedeanGL.compactCartanSquareSum F n))
      (envelopingAction_casimirOperator S (ArchimedeanGL.compactCartanSquareSum F n))
      hfinite P hPfinite (hPenv (ArchimedeanGL.matrixCasimir F n))
      (hPenv (ArchimedeanGL.compactCartanSquareSum F n))
  have hPerpLie (X : ArchimedeanGL.RealLieAlgebra F n) (v : S.Space) (hv : v ∈ Pᗮ) :
      S.lieAction X v ∈ Pᗮ := by
    apply (P.mem_orthogonal' _).mpr
    intro y hy
    have h0 := (P.mem_orthogonal' _).mp hv (realOperator S X y)
      (hPenv (ArchimedeanGL.realEnvelopingGenerator F n X) y hy)
    exact (isCoreSkew_realOperator b X v y).trans (by rw [h0, neg_zero])
  let Pperp : Subrepresentation S.representation :=
    { toSubmodule := Pᗮ
      apply_mem_toSubmodule := fun a v hv => S.representation_mem_of_stable _
        (invariantForm_orthogonal_stable b.finiteForm (fun _ _ => rfl) _ hPfinite)
        (invariantForm_orthogonal_stable b.compactForm (fun _ _ => rfl) _ hPcompact)
        (S.envelopingAction_mem_of_lieAction _ hPerpLie) a v hv }
  refine ⟨Pperp, IsCompl.of_eq ?_ ?_⟩
  · apply Subrepresentation.toSubmodule_injective
    exact hcompl.inf_eq_bot
  · apply Subrepresentation.toSubmodule_injective
    exact hcompl.sup_eq_top

section Band

variable [CompactSpace (AdeleQuotient F)]

private theorem memLp_cuspidalBand (hS : S.IsCuspidal) (f : S.Space) :
    MemLp (toQuotient F n S f) 2 ((quotientHaarMeasure F n).restrict (band F n)) := by
  let : MeasurableSpace (AdelicGL F n) := borel _
  have : BorelSpace (AdelicGL F n) := ⟨rfl⟩
  obtain ⟨t, ht, hcover, hfinite⟩ := S.exists_band_cover hS (lo := 1) (hi := 2) one_pos
  exact memLp_band_of_cover F n S t ht (fun x hx => hcover x hx.1 hx.2) f (hfinite _ f)

/-- The determinant-band unitary form on any actual cuspidal realization at
a fixed unitary central character. -/
def cuspidalBandUnitaryForm (hn : n ≠ 0) (hS : S.IsCuspidal) (χ : HeckeCharacter F)
    (hχ : χ.IsUnitary) (hSχ : S.HasCentralCharacter χ) : S.UnitaryForm :=
  unitaryForm F n S hn hS χ hχ hSχ (memLp_cuspidalBand S hS)

set_option maxHeartbeats 650000 in
/-- Joint polynomial kernels of the two Casimirs at any open finite level
are finite-dimensional for a cuspidal realization at unitary central character. -/
theorem finiteDimensional_fixedCasimirKernels
    (hn : n ≠ 0) (hS : S.IsCuspidal) (χ : HeckeCharacter F)
    (hχ : χ.IsUnitary) (hSχ : S.HasCentralCharacter χ)
    (L : OpenSubgroup (FiniteAdelicGL F n)) (q p : ℂ[X]) (hq : q ≠ 0) (hp : p ≠ 0) :
    FiniteDimensional ℂ (fixedPolynomialKernels S.finiteRepresentation (casimirOperator S)
      (compactCasimirOperator S) L q p) := by
  let : MeasurableSpace (AdelicGL F n) := borel _
  have : BorelSpace (AdelicGL F n) := ⟨rfl⟩
  let b := cuspidalBandUnitaryForm S hn hS χ hχ hSχ
  obtain ⟨d, lam, hlam⟩ := separating_of_bandNorm S PrimitiveAdelicHeight.siegelSetGLFiniteness
    hn hS χ hχ hSχ b (bandNorm_eq_ofReal_inner S hn hS χ hχ hSχ (memLp_cuspidalBand S hS))
    L ((rootBound q : ℝ) + 2 * rootBound p)
  refine finiteDimensional_of_separating _ lam (fun e he hz => ?_)
  exact hlam e (fun l hl => he.1.1 ⟨l, hl⟩) (energy_le b hq hp he.1.2 he.2) hz

/-- The full operator representation of a cuspidal realization with a
fixed unitary central character is algebraically semisimple. -/
theorem isSemisimpleRepresentation_of_cuspidal_of_unitaryCentralCharacter
    (hn : n ≠ 0) (hS : S.IsCuspidal) (χ : HeckeCharacter F)
    (hχ : χ.IsUnitary) (hSχ : S.HasCentralCharacter χ) :
    S.representation.IsSemisimpleRepresentation :=
  isSemisimpleRepresentation_of_finite_casimirKernels S
    (cuspidalBandUnitaryForm S hn hS χ hχ hSχ)
    (finiteDimensional_fixedCasimirKernels S hn hS χ hχ hSχ)

end Band

end Langlands.Automorphic.CuspidalAdmissible
