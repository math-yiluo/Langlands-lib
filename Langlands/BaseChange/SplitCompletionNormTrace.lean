import Langlands.Automorphic.AssociatedGammaPreservation
import Langlands.BaseChange.CompletionRelativeFieldInvariants
import Langlands.BaseChange.CyclicGlobalizationPlaceComparison
import Langlands.Global.AdelicFunctoriality.AlmostEverywhereSplitNormProof
import Langlands.Global.AdelicFunctoriality.GaloisPlaceCount
import Langlands.Global.Factors.CuspidalPairFactorData
import Langlands.Global.Factors.FiniteEpsilonBaseComparison
import Langlands.Global.Factors.RelativeWeilAssemblyCharacters
import Langlands.Global.Factors.RelativeWeilAssemblyHecke

/-! # Norm characters, standard additive components and epsilon bases at split places -/

noncomputable section

set_option autoImplicit false

universe u uI

namespace Langlands.BaseChange

open Global Global.AdelicFunctoriality Global.CuspidalPairFunctionalEquation
open Global.HeckeFunctionalEquation Global.FunctionalEquationComparison
open scoped NumberField FiniteExtension BigOperators

variable {K L : Type u} [Field K] [Field L] [NumberField K] [NumberField L] [Algebra K L]
    (v : FinitePlace K)

/-- A norm-trivial global character has trivial finite component at a place with
one degree-one upper completion. The completed scalar embedding splits the norm. -/
theorem finiteComponent_eq_one_of_normComp_eq_one_of_localDegree_one
    (w : FinitePlacesAbove L v)
    (hd : Module.finrank (v.adicCompletion K) (w.1.adicCompletion L) = 1)
    (χ : HeckeCharacter K) (hχ : χ.normComp (L := L) = 1) : χ.finiteComponent v = 1 := by
  apply ContinuousMonoidHom.ext
  intro x
  let y := Units.map (FiniteExtension.completionMap v w.1).toMonoidHom x
  have hy : FiniteExtension.localUnitNorm v w.1 y = x :=
    localNorm_units_completionMap_of_finrank_eq_one v w.1 hd x
  have h := χ.normComp_finiteComponent v w y
  rw [hχ, hy, HeckeCharacter.finiteComponent_one] at h
  exact h.symm

/-- The standard adelic additive components agree through the degree-one completion
isomorphism. The relative trace of the actual scalar inclusion is the identity. -/
theorem standardFiniteAdditiveComponent_degreeOneCompletionEquiv
    (w : FinitePlacesAbove L v)
    (hd : Module.finrank (v.adicCompletion K) (w.1.adicCompletion L) = 1)
    (x : v.adicCompletion K) :
    standardFiniteAdditiveComponent L w.1 (degreeOneCompletionEquiv v w hd x) =
      standardFiniteAdditiveComponent K v x := by
  rw [standardFiniteAdditiveComponent_trace v w.1]
  congr 1
  change Algebra.trace (v.adicCompletion K) (w.1.adicCompletion L) (algebraMap _ _ x) = x
  rw [Algebra.trace_algebraMap, hd, one_nsmul]

/-- At completed degree one the relative inertia degree is one. -/
private theorem inertiaDeg_eq_one_of_localDegree_one (w : FinitePlacesAbove L v)
    (hd : Module.finrank (v.adicCompletion K) (w.1.adicCompletion L) = 1) :
    w.1.asIdeal.inertiaDeg (𝓞 K) = 1 := by
  rw [localDegree_eq v w.1] at hd
  exact Nat.dvd_one.mp ⟨_, hd.symm.trans (Nat.mul_comm _ _)⟩

/-- The actual residue cardinalities agree for the degree-one local embedding. -/
theorem residueCardinality_eq_of_localDegree_one (w : FinitePlacesAbove L v)
    (hd : Module.finrank (v.adicCompletion K) (w.1.adicCompletion L) = 1) :
    residueCardinality w.1 = residueCardinality v := by
  rw [residueCardinality, residueCardinality, Langlands.Global.CompletionPadic.canonicalResidueCardinality_eq_absNorm,
    Langlands.Global.CompletionPadic.canonicalResidueCardinality_eq_absNorm, ← Ideal.absNorm_pow_inertiaDeg v.asIdeal w.1.asIdeal,
    inertiaDeg_eq_one_of_localDegree_one v w hd, pow_one]

/-- The two finite fibers count the same number of factors when all local degrees
are one. This uses the global sum of the ramification-inertia products. -/
theorem card_placesAbove_eq_finrank_of_all_localDegrees_one
    (hd : ∀ w : FinitePlacesAbove L v,
      Module.finrank (v.adicCompletion K) (w.1.adicCompletion L) = 1) :
    (RelativeWeilEngine.placesAbove L v).card = Module.finrank K L := by
  have h := Global.AdelicFunctoriality.card_mul_eq_finrank_of_forall (L := L) v 1 fun w =>
    (localDegree_eq v w.1).symm.trans (hd w)
  have he : (RelativeWeilEngine.placesAbove L v).card =
      (Global.AdelicFunctoriality.placesAbove L v).card := by
    simp only [RelativeWeilEngine.placesAbove, Global.AdelicFunctoriality.placesAbove, Finset.card_map]
  rw [he, ← h, mul_one]

/-- At a split finite place, as many upper epsilon factors occur as global norm
characters. If the local exponents coincide, their finite positive bases agree. -/
def SplitCompletionEpsilonBaseStatement : Prop :=
  ∀ (K L : Type u) [Field K] [Field L] [NumberField K] [NumberField L] [Algebra K L]
    (v : FinitePlace K) (σ : L ≃ₐ[K] L) (l : ℕ),
    TraceFormula.IsCyclicShiftSplit K L (v.adicCompletion K) σ l →
    ∀ (I : Type uI) [Fintype I], Fintype.card I = Module.finrank K L →
    ∀ (bF : I → ℂˣ × ℤ) (bE : FinitePlace L → ℂˣ × ℤ) (m : ℤ),
      (∀ i, (bF i).2 = m) →
      (∀ w ∈ RelativeWeilEngine.placesAbove L v, (bE w).2 = m) →
      finiteEpsilonBase Finset.univ (fun _ : I => residueCardinality v) bF =
        finiteEpsilonBase (RelativeWeilEngine.placesAbove L v) residueCardinality bE

set_option maxHeartbeats 850000 in
/-- Every completion above the split place has degree one. Evaluate the two
finite products as powers of the common local residue cardinality. -/
theorem splitCompletionEpsilonBase : SplitCompletionEpsilonBaseStatement.{u, uI} := by
  classical
  intro K L _ _ _ _ _ v σ l hsplit I _ hI bF bE m hF hE
  have hd (w : FinitePlacesAbove L v) :
      Module.finrank (v.adicCompletion K) (w.1.adicCompletion L) = 1 :=
    Algebra.finrank_eq_one_iff_bijective_algebraMap.mpr
      (completionMap_bijective_of_cyclicShiftSplit v σ l hsplit w)
  have hq (w : FinitePlace L) (hw : w ∈ RelativeWeilEngine.placesAbove L v) :
      residueCardinality w = residueCardinality v := by
    have hw' : w ∈ Global.AdelicFunctoriality.placesAbove L v := by
      obtain ⟨a, ha, rfl⟩ := Finset.mem_map.mp hw
      exact Finset.mem_map.mpr ⟨a, ha, rfl⟩
    let x : FinitePlacesAbove L v := ⟨w, Global.AdelicFunctoriality.mem_placesAbove.mp hw'⟩
    exact residueCardinality_eq_of_localDegree_one v x (hd x)
  have hl : finiteEpsilonBase Finset.univ (fun _ : I => residueCardinality v) bF =
      ((residueCardinality v : ℝ) ^ m) ^ Fintype.card I := by
    simp [finiteEpsilonBase, hF]
  have he : finiteEpsilonBase (RelativeWeilEngine.placesAbove L v) residueCardinality bE =
      ((residueCardinality v : ℝ) ^ m) ^ (RelativeWeilEngine.placesAbove L v).card := by
    rw [← Finset.prod_const]
    exact Finset.prod_congr rfl fun w hw => by rw [hq w hw, hE w hw]
  rw [hl, he, hI, card_placesAbove_eq_finrank_of_all_localDegrees_one v hd]

end Langlands.BaseChange
