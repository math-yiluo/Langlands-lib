import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalCuspidalSpace
import Langlands.GroupScheme.Rational.StandardAssociatedOppositeTransportProof
import Langlands.GroupScheme.Rational.RelativeWeylCoxeterProof
import Langlands.Representation.Aubert.General.RationalOppositeParabolic
import Langlands.Analysis.Local.QuotientMeasureEquiv

/-! # Intrinsic cuspidality on proper opposite rational radicals

Conjugation transports the all-translates integral kernel to a conjugate
subgroup, with both integrability and vanishing retained. The published
longest-lift transport supplies the opposite radical of each proper standard
cocharacter without a semistandard-kernel comparison premise.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj NNReal
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology
open Langlands.Aubert.General.RationalPointFamily
open Langlands.Group.RelativeWeylIndexing

namespace Langlands.HarishChandraSchwartz

section Generic

variable {Γ : Type*} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
  [MeasurableSpace Γ] [BorelSpace Γ] {U V : Subgroup Γ}

/-- Ambient conjugation restricted to two corresponding closed or nonclosed
subgroups, with their induced topologies. -/
def conjugationSubgroupContinuousMulEquiv (g : Γ)
    (h : ∀ x : Γ, g * x * g⁻¹ ∈ V ↔ x ∈ U) : U ≃ₜ* V :=
  Langlands.QuotientIntegration.subgroupContinuousMulEquiv
    { toMulEquiv := MulAut.conj g
      continuous_toFun := (continuous_const.mul continuous_id).mul continuous_const
      continuous_invFun := (continuous_const.mul continuous_id).mul continuous_const }
    U V h

omit [MeasurableSpace Γ] [BorelSpace Γ] in
@[simp] theorem conjugationSubgroupContinuousMulEquiv_apply (g : Γ)
    (h : ∀ x : Γ, g * x * g⁻¹ ∈ V ↔ x ∈ U) (x : U) :
    (conjugationSubgroupContinuousMulEquiv g h x : Γ) = g * x * g⁻¹ := rfl

/-- All-translates convergence and vanishing, for every Haar measure on `U`,
give the same property for every Haar measure on any conjugate subgroup `V`. -/
theorem isIntegrableUnipotentCuspidal_of_conjugation
    {f : Γ → ℂ} (g : Γ) (e : U ≃ₜ* V)
    (he : ∀ u : U, (e u : Γ) = g * u * g⁻¹)
    (hf : ∀ muU : Measure U, muU.IsHaarMeasure → IsIntegrableUnipotentCuspidal muU f)
    (muV : Measure V) [muV.IsHaarMeasure] :
    IsIntegrableUnipotentCuspidal muV f := by
  let muU : Measure U := muV.map e.symm
  have : muU.IsHaarMeasure := e.symm.isHaarMeasure_map muV
  intro x y
  obtain ⟨hi, hz⟩ := hf muU inferInstance (x * g) (g⁻¹ * y)
  have hfun : (fun u : U => f ((x * g) * u * (g⁻¹ * y))) ∘ e.symm =
      fun v : V => f (x * v * y) := by
    funext v
    have hv : g * (e.symm v : Γ) * g⁻¹ = (v : Γ) := by
      rw [← he, e.apply_symm_apply]
    simp only [Function.comp_apply]
    congr 1
    calc
      x * g * (e.symm v : Γ) * (g⁻¹ * y) =
          x * (g * (e.symm v : Γ) * g⁻¹) * y := by group
      _ = x * (v : Γ) * y := by rw [hv]
  refine ⟨?_, ?_⟩
  · have hi' := (integrable_map_equiv e.symm.toHomeomorph.toMeasurableEquiv _).mp hi
    change Integrable
      ((fun u : U => f ((x * g) * u * (g⁻¹ * y))) ∘ e.symm) muV at hi'
    rwa [hfun] at hi'
  · have hz' := (integral_map_equiv e.symm.toHomeomorph.toMeasurableEquiv
      (fun u : U => f ((x * g) * u * (g⁻¹ * y)))).symm.trans hz
    change (∫ v : V,
      ((fun u : U => f ((x * g) * u * (g⁻¹ * y))) ∘ e.symm) v ∂muV) = 0 at hz'
    rwa [hfun] at hz'

end Generic

attribute [local instance] rationalWeightsIsAffine rationalWeightsTopology
  rationalWeightsTopologicalGroup rationalWeightsT2Field rationalWeightsLocallyCompact
  rationalWeightsMeasurableSpace rationalWeightsBorelSpace

section Rational

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {S : CommGroupScheme (Spec (CommRingCat.of F))}
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom]
  {i : S.toGrp ⟶ G} {ν : cocharacterLattice S}
  {K : OpenSubgroup (rationalPoints G)}
  (hKc : IsCompact (K : Set (rationalPoints G)))
  (hPK : IsIwasawaPair (standardParabolicPoints i ν ∅) K.toSubgroup)
  {N : ℕ} [Nonempty (Fin N)] (ρ : MatrixRepresentation G (Fin N))

/-- Intrinsic standard cuspidality gives absolute convergence and vanishing
along every two-sided translate of a proper standard opposite radical. -/
theorem isIntegrableUnipotentCuspidal_opposite_of_mem_rationalCuspidalSubmodule
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (hν : IsGenericCocharacter i ν)
    (I : Finset (SimpleRoot i ν)) (hI : rootSet i ν I ≠ simpleRelativeRoots i ν)
    (ζ : cocharacterLattice S) (hζ : IsStandardCocharacter i ν (rootSet i ν I) ζ)
    {f : RationalSchwartzSpace hKc hPK ρ}
    (hf : f ∈ rationalCuspidalSubmodule hKc hPK ρ)
    (muV : Measure (oppositeUnipotent i ζ)) [muV.IsHaarMeasure] :
    IsIntegrableUnipotentCuspidal muV (f : rationalPoints G → ℂ) := by
  classical
  have := hi.isSplitSubtorus.mono
  obtain ⟨hWfin, hSfin, CM, cs, hcs⟩ := relativeWeylCoxeter F G hG S i hi ν hν
  let := Fintype.ofFinite (relativeWeylGroup i)
  let := Fintype.ofFinite (SimpleRoot i ν)
  obtain ⟨n, hn⟩ := QuotientGroup.mk_surjective (longestRep cs I)
  have htransport :=
    standardAssociatedOppositeTransport F G hG S i hi ν hν CM cs hcs
  have hproper : rootSet i ν (associatedSubset cs I) ≠ simpleRelativeRoots i ν := by
    intro heq
    have hfull : associatedSubset cs I = Finset.univ := by
      apply Finset.eq_univ_of_forall
      intro a
      exact (val_mem_rootSet i ν _ a).mp (heq.symm ▸ a.property)
    have hcard := (associatedSubsetLaws_proof cs I).2.1
    rw [hfull] at hcard
    have hIfull : I = Finset.univ := Finset.eq_univ_of_card I (by simpa using hcard.symm)
    exact hI (hIfull ▸ rootSet_univ i ν)
  have hconj : ∀ x : rationalPoints G,
      (n : rationalPoints G) * x * (n : rationalPoints G)⁻¹ ∈ oppositeUnipotent i ζ ↔
        x ∈ standardUnipotentPoints i ν (rootSet i ν (associatedSubset cs I)) := by
    intro x
    exact (IsStandardAssociatedOppositeTransport.mem_rationalPoints i ν htransport
      I n hn ζ hζ x).2.symm
  let e := conjugationSubgroupContinuousMulEquiv (n : rationalPoints G) hconj
  exact isIntegrableUnipotentCuspidal_of_conjugation (n : rationalPoints G) e
    (fun u => rfl) (fun muU hmuU => hf (associatedSubset cs I) hproper muU hmuU) muV

end Rational

end Langlands.HarishChandraSchwartz
