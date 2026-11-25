import Langlands.BaseChange.CyclicProductUnitReduction
import Langlands.TraceFormula.LocalCyclicProductCoordinates
import Langlands.Global.AdelicFunctoriality.UnramifiedUnitNorm
import Langlands.Global.Factors.RelativeWeilLocalEulerBridge

/-! # Unit concordance on the actual unramified finite-place algebra -/

noncomputable section

open MeasureTheory Topology
open scoped BigOperators

namespace Langlands.TraceFormula

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open BaseChange Correspondence Langlands.Global Langlands.Global.AdelicFunctoriality Unramified
open Langlands.Global.AdelicFunctoriality.FiniteExtension
open scoped NumberField FiniteExtension TensorProduct PlaceCompletion

universe u

attribute [local instance] heckeFieldTopology heckeFieldValuativeRel heckeFieldLocalField
  heckeGeneralLinearTopology heckeGeneralLinearTopologicalGroup heckeGeneralLinearT2
  heckeGeneralLinearMeasurable heckeGeneralLinearBorel

variable (K L : Type u) [Field K] [Field L] [NumberField K] [NumberField L]
  [Algebra K L] [FiniteDimensional K L] (v : Langlands.Global.FinitePlace K)

local notation "Kᵥ" => v.adicCompletion K
local notation "Eᵥ" => LocalBaseChangeAlgebra K L (Sum.inr v)
local notation "Places" => FinitePlacesAbove L v

private local instance : Algebra Kᵥ Eᵥ := LocalBaseChangeAlgebra.algebra K L (.inr v)

private local instance {A : Type u} [CommRing A] [TopologicalSpace A] (n : ℕ) :
    MeasurableSpace (GeneralLinear n A) := borel _
private local instance {A : Type u} [CommRing A] [TopologicalSpace A] (n : ℕ) :
    BorelSpace (GeneralLinear n A) := ⟨rfl⟩

omit [FiniteDimensional K L] in
private theorem tower_ramificationIndex_eq (q : Places)
    (h : q.1.asIdeal.ramificationIdx (𝓞 K) = 1) :
    (towerPadicField v q.1).canonicalTopologicalData.ramificationIndex =
      (CompletionPadic.padicField v).canonicalTopologicalData.ramificationIndex := by
  have htop : towerTopologicalData v q.1 = (towerPadicField v q.1).canonicalTopologicalData :=
    LocalFactor.PadicAbelian.topologicalData_ext (tower_topology_eq v q.1) rfl
  simpa only [htop, CompletionPadic.topologicalData_eq_canonicalTopologicalData v] using
    (ramificationIndex_eq_of_ramificationIdx_eq_one v q.1 h).symm

omit [FiniteDimensional K L] in
private theorem mem_towerIntegers_iff (q : Places) (x : q.1.adicCompletion L) :
    x ∈ (towerPadicField v q.1).canonicalTopologicalData.Integers ↔
      x ∈ q.1.adicCompletionIntegers L := by
  rw [← (towerPadicField v q.1).canonicalTopologicalData.canonicalNorm_le_one_iff_mem_integers,
    mem_adicCompletionIntegers, ← PadicField.canonicalValuation_coe, NNReal.coe_le_one]
  exact (tower_valued_isEquiv v q.1).le_one_iff_le_one.symm

omit [FiniteDimensional K L] in
private theorem mem_towerSphericalSubgroup_iff (q : Places) (r : ℕ)
    (x : GeneralLinear (r + 1) (q.1.adicCompletion L)) :
    x ∈ sphericalSubgroup (towerPadicField v q.1) r ↔
      (∀ i j, x i j ∈ q.1.adicCompletionIntegers L) ∧
      (∀ i j, x⁻¹ i j ∈ q.1.adicCompletionIntegers L) := by
  change x ∈ Conductor.integralSubgroup (towerPadicField v q.1).canonicalTopologicalData.Integers r ↔ _
  rw [Conductor.mem_integralSubgroup]
  simp only [mem_towerIntegers_iff K L v q]

/-- With the p-adic normalization on the base completion, the field unit
lemma implies unit concordance at every unramified finite place. -/
def LocalUnramifiedUnitConcordanceStatement : Prop :=
  UnitFundamentalLemmaStatement.{u, u} →
    ∀ (K L : Type u) [Field K] [Field L] [NumberField K] [NumberField L]
      [Algebra K L] [FiniteDimensional K L] (v : Langlands.Global.FinitePlace K)
      (σ : L ≃ₐ[K] L) (l r : ℕ), IsCyclicAlgebra σ l →
      (∀ q : FinitePlacesAbove L v, q.1.asIdeal.ramificationIdx (𝓞 K) = 1) →
      let F := CompletionPadic.padicField v
      letI : TopologicalSpace F.Carrier := F.canonicalTopologicalData.topology
      letI := heckeFieldValuativeRel F
      letI := heckeFieldLocalField F
      let E := LocalBaseChangeAlgebra K L (.inr v)
      let σᵥ : E ≃ₐ[F.Carrier] E := localGalois K L σ (.inr v)
      let S := GeneralLinearGroup.integralSubgroup (Fin (r + 1)) (localIntegers K L v)
      ∀ (μE : Measure (GeneralLinear (r + 1) E)) [μE.IsHaarMeasure], μE S = 1 →
        AreConcordant σᵥ l (sphericalHaar F r) μE ((S : Set _).indicator (fun _ ↦ 1))
          (↑(1 : SphericalHeckeAlgebra F r))

theorem localUnramifiedUnitConcordance : LocalUnramifiedUnitConcordanceStatement := by
  intro hunit K L _ _ _ _ _ _ v σ l r hσ hunram
  dsimp only
  intro μE _ hmass
  obtain ⟨q, m, d, τ, c, hl, hτ, hc, hc', hshift, hwrap, hint⟩ :=
    exists_localCyclicProductCoordinates K L v σ l hσ
  subst l
  let F := CompletionPadic.padicField v
  let P := towerPadicField v q.1
  let E := LocalBaseChangeAlgebra K L (Sum.inr v)
  let : Algebra F.Carrier E := LocalBaseChangeAlgebra.algebra K L (.inr v)
  let := F.algebra
  let := P.algebra
  let : IsScalarTower (Padic (CompletionPadic.residuePrime v)) F.Carrier P.Carrier :=
    IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  let : TopologicalSpace F.Carrier := F.canonicalTopologicalData.topology
  let : TopologicalSpace P.Carrier := P.canonicalTopologicalData.topology
  let := heckeFieldValuativeRel P
  let := heckeFieldLocalField P
  let : IsModuleTopology F.Carrier E := by
    change @IsModuleTopology F.Carrier F.canonicalTopologicalData.topology E _ _ _
    rw [← CompletionPadic.completion_topology_eq v]
    exact LocalBaseChangeAlgebra.isModuleTopology K L (.inr v)
  have hc₁ : Continuous c := by
    change Continuous[_, @Pi.topologicalSpace _ _ (fun _ ↦ P.canonicalTopologicalData.topology)] c
    rw [← tower_topology_eq v q.1]
    exact hc
  have hc₂ : Continuous c.symm := by
    change Continuous[@Pi.topologicalSpace _ _ (fun _ ↦ P.canonicalTopologicalData.topology), _] c.symm
    rw [← tower_topology_eq v q.1]
    exact hc'
  have hcE : IsCyclicAlgebra (localGalois K L σ (.inr v) : E ≃ₐ[F.Carrier] E) ((m + 1) * d) :=
    isCyclicAlgebra_localGalois K L σ ((m + 1) * d) (.inr v) hσ
  have hmatch := cyclicProductUnitReduction hunit (CompletionPadic.residuePrime v) F P E
    (localGalois K L σ (.inr v)) τ m d r hcE hτ
    (tower_ramificationIndex_eq K L v q (hunram q)) c hc₁ hc₂ hshift hwrap
  let n := r + 1
  let H := GeneralLinear n E
  let G := GeneralLinear n P.Carrier
  let κ := cyclicProductGLCoordinates (n := n) c hc₁ hc₂
  let S := GeneralLinearGroup.integralSubgroup (Fin n) (localIntegers K L v)
  let S' := Set.pi Set.univ (fun _ : Fin (m + 1) ↦ (sphericalSubgroup P r : Set G))
  have hmem (x : H) : x ∈ S ↔ κ x ∈ S' := by
    rw [GeneralLinearGroup.mem_integralSubgroup]
    simp only [S', Set.mem_pi, Set.mem_univ, true_implies]
    constructor
    · intro hx j
      refine (mem_towerSphericalSubgroup_iff K L v q r _).mpr ⟨?_, ?_⟩
      · intro a b
        rw [cyclicProductGLCoordinates_apply_apply]
        exact (hint _).mp (hx.1 a b) j
      · intro a b
        rw [← Pi.inv_apply, ← map_inv, cyclicProductGLCoordinates_apply_apply]
        exact (hint _).mp (hx.2 a b) j
    · intro hx
      refine ⟨fun a b ↦ (hint _).mpr (fun j ↦ ?_), fun a b ↦ (hint _).mpr (fun j ↦ ?_)⟩
      · rw [← cyclicProductGLCoordinates_apply_apply c hc₁ hc₂]
        exact ((mem_towerSphericalSubgroup_iff K L v q r _).mp (hx j)).1 a b
      · rw [← cyclicProductGLCoordinates_apply_apply c hc₁ hc₂, map_inv, Pi.inv_apply]
        exact ((mem_towerSphericalSubgroup_iff K L v q r _).mp (hx j)).2 a b
  let μ := sphericalHaar P r
  let μprod : Measure (Fin (m + 1) → G) := Measure.pi fun _ ↦ μ
  let μ₀ : Measure H := Measure.map κ.symm μprod
  let : LocallyCompactSpace G := LocalFieldTopology.generalLinear_locallyCompactSpace P.Carrier n
  let : SecondCountableTopology G := LocalFieldTopology.generalLinear_secondCountableTopology P.Carrier n
  let : μ.IsHaarMeasure := sphericalHaar_isHaar P r
  let : μprod.IsHaarMeasure := Measure.pi.isHaarMeasure (fun _ : Fin (m + 1) ↦ μ)
  let : LocallyCompactSpace H := κ.toHomeomorph.isClosedEmbedding.locallyCompactSpace
  let : SecondCountableTopology H := κ.toHomeomorph.secondCountableTopology
  let : μ₀.IsHaarMeasure := κ.symm.isHaarMeasure_map μprod
  have hopen : IsOpen (S : Set H) :=
    GeneralLinearGroup.isOpen_integralSubgroup _ _ (isOpen_localIntegers K L v)
  have hvol : μ₀ S = 1 := by
    have hpre : (κ.symm : (Fin (m + 1) → G) → H) ⁻¹' (S : Set H) = S' := by
      ext x
      change κ.symm x ∈ S ↔ x ∈ S'
      rw [hmem, ContinuousMulEquiv.apply_symm_apply]
    change Measure.map κ.symm μprod (S : Set H) = 1
    have hcont : Measurable (κ.symm : (Fin (m + 1) → G) → H) := κ.symm.continuous.measurable
    rw [Measure.map_apply hcont hopen.measurableSet, hpre]
    change (Measure.pi fun _ : Fin (m + 1) ↦ μ)
      (Set.pi Set.univ fun _ ↦ (sphericalOpenSubgroup P r : Set G)) = 1
    rw [Measure.pi_pi]
    have hone : μ (sphericalOpenSubgroup P r : Set G) = 1 := sphericalHaar_self P r
    simp only [hone, Finset.prod_const_one]
  have hμ : μE = μ₀ := by
    have h := Measure.isMulLeftInvariant_eq_smul μE μ₀
    have hscale : Measure.haarScalarFactor μE μ₀ = 1 := by
      have hx := congrArg (fun ν : Measure H ↦ ν (S : Set H)) h
      have hmass' : μE (S : Set H) = 1 := hmass
      simp only [hmass', hvol, Measure.smul_apply, ENNReal.smul_def, smul_eq_mul, mul_one] at hx
      exact_mod_cast hx.symm
    rw [h, hscale, one_smul]
  have hφ : (fun x : H ↦ S'.indicator (fun _ ↦ (1 : ℂ)) (κ x)) =
      (S : Set H).indicator (fun _ ↦ (1 : ℂ)) := by
    funext x
    classical
    simp only [Set.indicator_apply, ← hmem]
    rfl
  rw [hμ]
  rw [← hφ]
  exact hmatch

end Langlands.TraceFormula
