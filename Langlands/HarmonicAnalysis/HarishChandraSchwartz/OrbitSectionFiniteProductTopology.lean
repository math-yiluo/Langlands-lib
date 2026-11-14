import Langlands.HarmonicAnalysis.HarishChandraSchwartz.SmoothTorusTensorTopology
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.OrbitSectionFixedTensor

/-! # Finite-product level topology and the actual section inductive limit -/

noncomputable section

open Langlands.Aubert.General Langlands.Plancherel Langlands.Induction
open TopologicalSpace
open scoped TensorProduct NNReal

namespace Langlands.HarishChandraSchwartz

universe uG uI uV uJ uB

variable {G : Type uG} [Group G] [TopologicalSpace G] [LocallyCompactSpace G]
  [NonarchimedeanGroup G] {P M U : Subgroup G}
  (h : IsSemidirectDecomposition P M U) (K : OpenSubgroup G)
  (π : IrreducibleAdmissibleRep.{0, uG, uV} (k := ℂ) (G := M))
  {I : Type uI} (ν : I → (M →* ℝ≥0ˣ))
  {J : Type uJ} [Fintype J] [DecidableEq J]
  (e : unitaryUnramifiedCharacters ν ≃* (J → Circle))
  (hU : IsClosed (U : Set G)) (hP : IsClosed (P : Set G))
  (hK : IsCompact (K : Set G)) (hν : ∀ i, Continuous (ν i))
  (hr : Continuous h.projection)
  (hPK : ∀ g : G, ∃ p : P, ∃ k : K, g = (p : G) * (k : G))

section Level

variable (H : OpenSubgroup G) (hHK : H ≤ K)
  {B : Type uB} [Fintype B] [DecidableEq B]
  (b : Module.Basis B ℂ (orbitSectionFixedCoefficients h K π H))

/-- The actual section tensor expressed in a finite coefficient basis. -/
def orbitSectionLevelCoordinates :
    OrbitSectionLevel ν π e h hU K hP hK hν hr hPK H →ₗ[ℂ]
      (B → smoothFiniteTorusFunctions J) :=
  (smoothTensorCoordinates J b).toLinearMap ∘ₗ
    orbitSectionLevelTensor h K π ν e hU hP hK hν hr hPK H hHK

omit [DecidableEq J] in
/-- Each coordinate is the corresponding scalar coordinate of the actual
fixed-valued compact restriction. -/
theorem orbitSectionLevelCoordinates_apply
    (q : OrbitSectionLevel ν π e h hU K hP hK hν hr hPK H)
    (i : B) (z : J → Circle) :
    (orbitSectionLevelCoordinates h K π ν e hU hP hK hν hr hPK H hHK b q i).val z =
      b.coord i (orbitSectionLevelFixedRestriction
        h K π ν e hU hP hK hν hr hPK H hHK q z) := by
  change (smoothTensorCoordinates J b
    (orbitSectionLevelTensor h K π ν e hU hP hK hν hr hPK H hHK q) i).val z = _
  rw [smoothTensorCoordinates_apply]
  apply congrArg (b.coord i)
  apply Subtype.ext
  exact orbitSectionLevelTensor_evaluation h K π ν e hU hP hK hν hr hPK H hHK q z

omit [DecidableEq J] in
/-- The finite coordinates still distinguish actual sections. -/
theorem orbitSectionLevelCoordinates_injective :
    Function.Injective
      (orbitSectionLevelCoordinates h K π ν e hU hP hK hν hr hPK H hHK b) :=
  (smoothTensorCoordinates J b).injective.comp
    (orbitSectionLevelTensor_injective h K π ν e hU hP hK hν hr hPK H hHK)

/-- The topology on the actual level induced from the independent scalar
smooth topology on its finite coordinate product. -/
@[instance_reducible]
def orbitSectionFiniteProductLevelTopology :
    TopologicalSpace (OrbitSectionLevel ν π e h hU K hP hK hν hr hPK H) :=
  induced (orbitSectionLevelCoordinates h K π ν e hU hP hK hν hr hPK H hHK b)
    (smoothTorusProductTopology J B)

/-- The open level comparison, on the same underlying actual section level. -/
def OrbitSectionLevelFiniteProductTopologyStatement : Prop :=
  OrbitSectionLevel.topologicalSpace ν π e h hU K hP hK hν hr hPK H =
    orbitSectionFiniteProductLevelTopology h K π ν e hU hP hK hν hr hPK H hHK b

end Level

section ChosenBasis

/-- A finite coefficient basis selected from an explicit finiteness witness. -/
def orbitSectionFixedBasis (H : OpenSubgroup G)
    (d : FiniteDimensional ℂ (orbitSectionFixedCoefficients h K π H)) :
    Module.Basis (Fin (Module.finrank ℂ (orbitSectionFixedCoefficients h K π H))) ℂ
      (orbitSectionFixedCoefficients h K π H) :=
  letI := d
  Module.finBasis ℂ (orbitSectionFixedCoefficients h K π H)

variable
  (d : ∀ H : {H : OpenSubgroup G // H ≤ K},
    FiniteDimensional ℂ (orbitSectionFixedCoefficients h K π H.1))

/-- Final topology from the independent finite-product fixed-level
topologies, using the existing inclusions into the actual total space. -/
@[instance_reducible]
def orbitSectionFiniteProductOriginalTop :
    TopologicalSpace (OrbitSectionSpace ν π e h hU K hP hK hν hr hPK) :=
  ⨆ H : {H : OpenSubgroup G // H ≤ K},
    coinduced (OrbitSectionSpace.ofLevel ν π e h hU K hP hK hν hr hPK H.1)
      (orbitSectionFiniteProductLevelTopology h K π ν e hU hP hK hν hr hPK H.1 H.2
        (orbitSectionFixedBasis h K π H.1 (d H)))

/-- The locally convex inductive limit of the independently constructed
finite-product levels, with the convention of `OrbitSectionSpace`. -/
@[instance_reducible]
def orbitSectionFiniteProductTopology :
    TopologicalSpace (OrbitSectionSpace ν π e h hU K hP hK hν hr hPK) :=
  sInf {t : TopologicalSpace (OrbitSectionSpace ν π e h hU K hP hK hν hr hPK) |
    orbitSectionFiniteProductOriginalTop h K π ν e hU hP hK hν hr hPK d ≤ t ∧
    @IsTopologicalAddGroup (OrbitSectionSpace ν π e h hU K hP hK hν hr hPK) t _ ∧
    @ContinuousSMul ℂ (OrbitSectionSpace ν π e h hU K hP hK hν hr hPK) _ _ t ∧
    @LocallyConvexSpace ℝ (OrbitSectionSpace ν π e h hU K hP hK hν hr hPK) _ _ _ _ t}

/-- The constructed inductive-limit topology is a topological vector-space
topology locally convex over the reals, as in the original construction. -/
theorem orbitSectionFiniteProductTopology_locallyConvex :
    @IsTopologicalAddGroup (OrbitSectionSpace ν π e h hU K hP hK hν hr hPK)
        (orbitSectionFiniteProductTopology h K π ν e hU hP hK hν hr hPK d) _ ∧
      @ContinuousSMul ℂ (OrbitSectionSpace ν π e h hU K hP hK hν hr hPK) _ _
        (orbitSectionFiniteProductTopology h K π ν e hU hP hK hν hr hPK d) ∧
      @LocallyConvexSpace ℝ (OrbitSectionSpace ν π e h hU K hP hK hν hr hPK) _ _ _ _
        (orbitSectionFiniteProductTopology h K π ν e hU hP hK hν hr hPK d) := by
  exact ⟨isTopologicalAddGroup_sInf fun _ ⟨_, ht, _, _⟩ => ht,
    continuousSMul_sInf fun _ ⟨_, _, ht, _⟩ => ht,
    .sInf fun _ ⟨_, _, _, ht⟩ => ht⟩

/-- Equality with the existing total section topology. -/
def OrbitSectionTotalFiniteProductTopologyStatement : Prop :=
  OrbitSectionSpace.topologicalSpace ν π e h hU K hP hK hν hr hPK =
    orbitSectionFiniteProductTopology h K π ν e hU hP hK hν hr hPK d

end ChosenBasis

/-- Combined target: finiteness is a conclusion, every finite basis gives the
level comparison, and the selected-basis inductive limit gives the total
comparison. No topology comparison is assumed. -/
def OrbitSectionFiniteProductTopologyStatement (_hcofinal : CompactOpenCofinal M) : Prop :=
  ∃ d : ∀ H : {H : OpenSubgroup G // H ≤ K},
      FiniteDimensional ℂ (orbitSectionFixedCoefficients h K π H.1),
    (∀ (H : {H : OpenSubgroup G // H ≤ K})
      (B : Type uB) [Fintype B] [DecidableEq B]
      (b : Module.Basis B ℂ (orbitSectionFixedCoefficients h K π H.1)),
      OrbitSectionLevelFiniteProductTopologyStatement
        h K π ν e hU hP hK hν hr hPK H.1 H.2 b) ∧
    OrbitSectionTotalFiniteProductTopologyStatement h K π ν e hU hP hK hν hr hPK d

end Langlands.HarishChandraSchwartz
