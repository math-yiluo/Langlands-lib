import Langlands.Geometry.Analytic.WeierstrassSpectrum.Statement
import Langlands.Geometry.Analytic.WeierstrassPresentation
import Langlands.Geometry.Analytic.Spectrum.ResidueField
import Mathlib.Topology.Algebra.Algebra

/-! # Spectrum of the actual Weierstrass quotient -/

noncomputable section

universe u

namespace Langlands.Analytic.WeierstrassPresentation

open StrictTateAlgebra PresentedStrictAffinoidAlgebra BanachSpectrum

variable (K : Type u) [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  (n m : ℕ) (S : Set (StrictTateAlgebra (Fin n) K))
  (f : Fin m → StrictTateAlgebra (Fin n) K)

omit [CompleteSpace K] in
theorem residuePowerBound (x : BanachSpectrum (ofRelations K n S))
    (hx : x ∈ locus K n m S f) (j : Fin m) :
    ∃ C : ℝ, 0 < C ∧ ∀ r : ℕ,
      ‖completedResidueMap K x (presentationMap K (ofRelations K n S) (f j)) ^ r‖ ≤ C := by
  refine ⟨1, zero_lt_one, fun r => ?_⟩
  rw [norm_pow, norm_completedResidueMap]
  exact pow_le_one₀ (apply_nonneg x.toMulRingSeminorm _) (hx j)

/-- A point of the norm locus lifts by evaluation in its actual completed
residue field, where the inequalities give power bounds. -/
def pointLift (x : BanachSpectrum (ofRelations K n S))
    (hx : x ∈ locus K n m S f) : BanachSpectrum (algebra K n m S f) :=
  comap (liftFromBase K n m S f (CompletedResidueField K x)
    (completedResidueMap K x) (residuePowerBound K n m S f x hx)).toBoundedRingHom
    (fieldPoint (CompletedResidueField K x))

theorem comap_pointLift (x : BanachSpectrum (ofRelations K n S))
    (hx : x ∈ locus K n m S f) :
    comap (baseMap K n m S f).toBoundedRingHom (pointLift K n m S f x hx) = x := by
  apply BanachSpectrum.ext
  intro a
  have h := congrArg (fun φ => φ a)
    (liftFromBase_comp_baseMap K n m S f (CompletedResidueField K x)
      (completedResidueMap K x) (residuePowerBound K n m S f x hx))
  change ‖liftFromBase K n m S f (CompletedResidueField K x)
    (completedResidueMap K x) (residuePowerBound K n m S f x hx)
      (baseMap K n m S f a)‖ = x a
  exact (congrArg norm h).trans (norm_completedResidueMap K x a)

/-- The quotient's spectrum has exactly the expected norm-inequality image. -/
theorem range_comap_baseMap :
    Set.range (comap (baseMap K n m S f).toBoundedRingHom) = locus K n m S f := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact comap_mem_locus K n m S f y
  · intro hx
    exact ⟨pointLift K n m S f x hx, comap_pointLift K n m S f x hx⟩

omit [CompleteSpace K] in
private theorem monomial_mem_of_coordinate_mem (T : PresentedStrictAffinoidAlgebra K)
    (C : Subalgebra K T) (hc : ∀ i, coordinate K T i ∈ C)
    (d : Fin T.arity →₀ ℕ) (c : K) :
    presentationMap K T (monomial (Fin T.arity) K d c) ∈ C := by
  rw [map_monomial]
  apply C.mul_mem (C.algebraMap_mem c)
  change (∏ i ∈ d.support, coordinate K T i ^ d i) ∈ C
  exact C.prod_mem fun i _ => C.pow_mem (hc i) _

/-- The base has dense image in the actual Weierstrass quotient: all
coordinates are base images, and Tate monomial expansions converge. -/
theorem denseRange_baseMap : DenseRange (baseMap K n m S f) := by
  let C := (baseMap K n m S f).toAlgHom.range.topologicalClosure
  have hcoord (i : Fin (n + m)) : coordinate K (algebra K n m S f) i ∈ C := by
    apply Subalgebra.le_topologicalClosure
    refine Fin.addCases (fun i => ?_) (fun j => ?_) i
    · exact ⟨coordinate K (ofRelations K n S) i, baseMap_coordinate K n m S f i⟩
    · exact ⟨presentationMap K (ofRelations K n S) (f j),
        (coordinate_equation K n m S f j).symm⟩
  have hmon (d : Fin (n + m) →₀ ℕ) (c : K) :
      presentationMap K (algebra K n m S f) (monomial (Fin (n + m)) K d c) ∈ C :=
    monomial_mem_of_coordinate_mem K (algebra K n m S f) C hcoord d c
  intro a
  obtain ⟨h, rfl⟩ := presentationMap_surjective K (algebra K n m S f) a
  change presentationMap K (algebra K n m S f) h ∈ C
  apply (Subalgebra.isClosed_topologicalClosure _).mem_of_tendsto
    ((hasSum_monomials (Fin (n + m)) K h).mapL
      (presentationMap K (algebra K n m S f)).toContinuousLinearMap)
  exact Filter.Eventually.of_forall fun s => C.sum_mem fun d _ => hmon d _

theorem comap_baseMap_injective :
    Function.Injective (comap (baseMap K n m S f).toBoundedRingHom) := by
  intro x y h
  have hx : Continuous (fun a => x a) := by
    simpa only [norm_completedResidueMap] using (completedResidueMap K x).continuous.norm
  have hy : Continuous (fun a => y a) := by
    simpa only [norm_completedResidueMap] using (completedResidueMap K y).continuous.norm
  have heq : (fun a => x a) = (fun a => y a) :=
    (denseRange_baseMap K n m S f).equalizer hx hy
      (funext fun a => congrArg (fun z : BanachSpectrum (ofRelations K n S) => z a) h)
  exact BanachSpectrum.ext (congrFun heq)

/-- The actual Weierstrass quotient spectrum embeds as a closed subspace. -/
theorem comap_baseMap_closedEmbedding :
    Topology.IsClosedEmbedding (comap (baseMap K n m S f).toBoundedRingHom) :=
  (comapContinuous (baseMap K n m S f).toBoundedRingHom).continuous.isClosedEmbedding
    (comap_baseMap_injective K n m S f)

/-- Dense base image and the exact closed spectrum subspace of the actual
unit-radius Weierstrass quotient. -/
theorem spectrumIdentification : SpectrumIdentificationStatement.{u} := by
  intro K _ _ _ n m S f
  exact ⟨denseRange_baseMap K n m S f, range_comap_baseMap K n m S f,
    comap_baseMap_closedEmbedding K n m S f⟩

end Langlands.Analytic.WeierstrassPresentation
