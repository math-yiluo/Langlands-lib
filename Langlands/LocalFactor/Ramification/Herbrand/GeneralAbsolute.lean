import Langlands.LocalFactor.Ramification.Herbrand.GeneralFinite
import Langlands.Galois.Local.AbsoluteDefinitions
import Mathlib.FieldTheory.Galois.Profinite
import Mathlib.FieldTheory.IsSepClosed
import Mathlib.Topology.Algebra.Group.Subgroup
import Mathlib.Algebra.Group.Subgroup.Pointwise

/-!
# Absolute upper ramification over a complete ultrametric base

Finite restriction preimages define the upper filtration of a separable
closure. Its closed positive upper limit is the named wild inertia subgroup.
The local-field specialization uses the existing norm adapter.
-/

noncomputable section

namespace Langlands.Ramification.Local

universe u₀ uK uΩ

section Restriction

variable (K : Type uK) (Ω : Type uΩ) [Field K] [Field Ω] [Algebra K Ω]

/-- Actual finite restriction with the existing Krull topologies. -/
def absoluteFiniteRestriction (L : FiniteGaloisIntermediateField K Ω) :
    (Ω ≃ₐ[K] Ω) →ₜ* Gal(L/K) where
  toMonoidHom := AlgEquiv.restrictNormalHom (F := K) (K₁ := Ω) L
  continuous_toFun := InfiniteGalois.restrictNormalHom_continuous L.toIntermediateField

end Restriction

section Spectral

variable (K₀ : Type u₀) [NontriviallyNormedField K₀] [IsUltrametricDist K₀]
  [CompleteSpace K₀] [ValuativeRel K₀] [LocallyCompactSpace K₀]
  (K : Type uK) [Field K] [Algebra K₀ K] [FiniteDimensional K₀ K]
  (Ω : Type uΩ) [Field Ω] [Algebra K Ω] [Algebra K₀ Ω]
  [IsScalarTower K₀ K Ω]
  (hbase : ∀ a b : K₀, ‖a‖ ≤ ‖b‖ ↔ ValuativeRel.vle a b)

private instance finiteGalois_finiteDimensional
    (L : FiniteGaloisIntermediateField K Ω) : FiniteDimensional K₀ L :=
  FiniteDimensional.trans K₀ K L

/-- The intersection of the finite upper groups in the actual separable
closure automorphism group. Every finite integer ring uses the same base norm. -/
def absoluteUpperRamificationGroup [IsSepClosure K Ω] (v : ℝ) :
    Subgroup (Ω ≃ₐ[K] Ω) :=
  ⨅ L : FiniteGaloisIntermediateField K Ω,
    (canonicalUpperRamificationGroup K₀ L hbase K v).comap
      (absoluteFiniteRestriction K Ω L).toMonoidHom

variable [IsSepClosure K Ω]

/-- Exact elementwise meaning of the intersection. -/
theorem mem_absoluteUpperRamificationGroup_iff (v : ℝ) (σ : Ω ≃ₐ[K] Ω) :
    σ ∈ absoluteUpperRamificationGroup K₀ K Ω hbase v ↔
      ∀ L : FiniteGaloisIntermediateField K Ω,
        absoluteFiniteRestriction K Ω L σ ∈
          canonicalUpperRamificationGroup K₀ L hbase K v := by
  simp only [absoluteUpperRamificationGroup, Subgroup.mem_iInf, Subgroup.mem_comap]
  rfl

/-- Finite evaluation at the ceiling of the inverse Herbrand parameter. -/
theorem mem_absoluteUpperRamificationGroup_iff_lower (v : ℝ) (σ : Ω ≃ₐ[K] Ω) :
    σ ∈ absoluteUpperRamificationGroup K₀ K Ω hbase v ↔
      ∀ L : FiniteGaloisIntermediateField K Ω,
        absoluteFiniteRestriction K Ω L σ ∈
          lowerRamificationGroupInt (LocalField.canonicalTopologicalData K₀ L hbase) K
            ⌈herbrandPsi (LocalField.canonicalTopologicalData K₀ L hbase) K v⌉ :=
  mem_absoluteUpperRamificationGroup_iff K₀ K Ω hbase v σ

/-- The defining bound at any one finite Galois subextension. -/
theorem absoluteUpperRamificationGroup_le_comap (v : ℝ)
    (L : FiniteGaloisIntermediateField K Ω) :
    absoluteUpperRamificationGroup K₀ K Ω hbase v ≤
      (canonicalUpperRamificationGroup K₀ L hbase K v).comap
        (absoluteFiniteRestriction K Ω L).toMonoidHom :=
  iInf_le _ L

/-- Elementary image containment in every finite upper group. -/
theorem absoluteUpperRamificationGroup_map_restriction_le (v : ℝ)
    (L : FiniteGaloisIntermediateField K Ω) :
    (absoluteUpperRamificationGroup K₀ K Ω hbase v).map
        (absoluteFiniteRestriction K Ω L).toMonoidHom ≤
      canonicalUpperRamificationGroup K₀ L hbase K v :=
  Subgroup.map_le_iff_le_comap.mpr
    (absoluteUpperRamificationGroup_le_comap K₀ K Ω hbase v L)

instance absoluteUpperRamificationGroup_normal (v : ℝ) :
    (absoluteUpperRamificationGroup K₀ K Ω hbase v).Normal := by
  apply Subgroup.normal_iInf_normal
  intro L
  exact Subgroup.Normal.comap
    (upperRamificationGroup_normal
      (LocalField.canonicalTopologicalData K₀ L hbase) K v) _

/-- Each finite target is discrete, so each restriction preimage is closed. -/
theorem absoluteUpperRamificationGroup_isClosed (v : ℝ) :
    IsClosed (absoluteUpperRamificationGroup K₀ K Ω hbase v : Set (Ω ≃ₐ[K] Ω)) := by
  unfold absoluteUpperRamificationGroup
  rw [Subgroup.coe_iInf]
  apply isClosed_iInter
  intro L
  exact (isClosed_discrete _).preimage (absoluteFiniteRestriction K Ω L).continuous

/-- The real-indexed absolute upper filtration is decreasing. -/
theorem absoluteUpperRamificationGroup_antitone :
    Antitone (absoluteUpperRamificationGroup K₀ K Ω hbase) := by
  intro v w hvw σ hσ
  rw [mem_absoluteUpperRamificationGroup_iff] at hσ ⊢
  intro L
  exact upperRamificationGroup_antitone
    (LocalField.canonicalTopologicalData K₀ L hbase) K hvw (hσ L)

@[simp] theorem absoluteUpperRamificationGroup_neg_one :
    absoluteUpperRamificationGroup K₀ K Ω hbase (-1) = ⊤ := by
  simp [absoluteUpperRamificationGroup, canonicalUpperRamificationGroup]

/-- The existing constant extension below Serre's domain is retained. -/
theorem absoluteUpperRamificationGroup_of_le_neg_one {v : ℝ} (hv : v ≤ -1) :
    absoluteUpperRamificationGroup K₀ K Ω hbase v = ⊤ := by
  apply top_unique
  simpa using absoluteUpperRamificationGroup_antitone K₀ K Ω hbase hv

/-- Wild inertia is the closed positive upper limit in the Krull topology. -/
def wildInertia : Subgroup (Ω ≃ₐ[K] Ω) :=
  (⨆ (v : ℝ) (_ : 0 < v),
    absoluteUpperRamificationGroup K₀ K Ω hbase v).topologicalClosure

instance wildInertia_normal : (wildInertia K₀ K Ω hbase).Normal := by
  unfold wildInertia
  exact Subgroup.is_normal_topologicalClosure _

end Spectral

section LocalField

variable (K : Type uK) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  (Ω : Type uΩ) [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]

local instance : NontriviallyNormedField K := LocalGalois.localNormedField K
local instance : IsUltrametricDist K := LocalGalois.localNormedField_ultrametric K
local instance : CompleteSpace K := LocalGalois.localNormedField_complete K

private theorem localBaseNorm_compatible (a b : K) :
    ‖a‖ ≤ ‖b‖ ↔ ValuativeRel.vle a b :=
  (LocalGalois.localNormedField_le K a b).trans
    (ValuativeRel.valuation K).vle_iff_le.symm

/-- The upper filtration for any nonarchimedean local field, in either
characteristic, on the automorphisms of its specified separable closure. -/
def localAbsoluteUpperRamificationGroup (v : ℝ) : Subgroup (Ω ≃ₐ[K] Ω) :=
  absoluteUpperRamificationGroup K K Ω (localBaseNorm_compatible K) v

/-- Wild inertia for a nonarchimedean local field and its separable closure. -/
def localWildInertia : Subgroup (Ω ≃ₐ[K] Ω) :=
  wildInertia K K Ω (localBaseNorm_compatible K)

instance localAbsoluteUpperRamificationGroup_normal (v : ℝ) :
    (localAbsoluteUpperRamificationGroup K Ω v).Normal :=
  absoluteUpperRamificationGroup_normal K K Ω (localBaseNorm_compatible K) v

theorem localAbsoluteUpperRamificationGroup_isClosed (v : ℝ) :
    IsClosed (localAbsoluteUpperRamificationGroup K Ω v : Set (Ω ≃ₐ[K] Ω)) :=
  absoluteUpperRamificationGroup_isClosed K K Ω (localBaseNorm_compatible K) v

theorem localAbsoluteUpperRamificationGroup_antitone :
    Antitone (localAbsoluteUpperRamificationGroup K Ω) :=
  absoluteUpperRamificationGroup_antitone K K Ω (localBaseNorm_compatible K)

@[simp] theorem localAbsoluteUpperRamificationGroup_neg_one :
    localAbsoluteUpperRamificationGroup K Ω (-1) = ⊤ :=
  absoluteUpperRamificationGroup_neg_one K K Ω (localBaseNorm_compatible K)

theorem localAbsoluteUpperRamificationGroup_of_le_neg_one {v : ℝ} (hv : v ≤ -1) :
    localAbsoluteUpperRamificationGroup K Ω v = ⊤ :=
  absoluteUpperRamificationGroup_of_le_neg_one K K Ω (localBaseNorm_compatible K) hv

instance localWildInertia_normal : (localWildInertia K Ω).Normal :=
  wildInertia_normal K K Ω (localBaseNorm_compatible K)

end LocalField
end Langlands.Ramification.Local
