import Langlands.Geometry.Building.ValuationBuildingAxioms
import Langlands.Geometry.Metric.KPDefinitions
import Langlands.GroupScheme.Rational.RelativeWeylRootPermutation
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! # Euclidean metrics on valuation apartments from actual relative roots -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped BigOperators
open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace

namespace Langlands.Geometry.Building

namespace RootTranslationMetric

variable {F : Type u} [Field F]
  {S : CommGroupScheme (Spec (CommRingCat.of F))}
  {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] (i : S.toGrp ⟶ G)
  [Fintype (relativeRoots i)]

/-- The actual relative roots give linear coordinates on the reduced translation
space, with values in their finite Euclidean coordinate space. -/
def coordinates : TranslationSpace i →ₗ[ℝ] EuclideanSpace ℝ (relativeRoots i) :=
  (WithLp.linearEquiv 2 ℝ (relativeRoots i → ℝ)).symm.toLinearMap ∘ₗ
    LinearMap.pi (rootForm i)

omit [Fintype (relativeRoots i)] in
@[simp] theorem coordinates_apply (v : TranslationSpace i) (α : relativeRoots i) :
    coordinates i v α = rootForm i α v := rfl

omit [Fintype (relativeRoots i)] in
/-- Passing to the quotient by the common kernel makes the root coordinates
injective, including when there are no relative roots. -/
theorem coordinates_injective : Function.Injective (coordinates i) := by
  apply (coordinates i).ker_eq_bot.mp
  apply eq_bot_iff.mpr
  intro v hv
  change v = 0
  change coordinates i v = 0 at hv
  induction v using Submodule.Quotient.induction_on with
  | _ v =>
    apply (Submodule.Quotient.mk_eq_zero _).mpr
    apply mem_rootAnnihilator.mpr
    intro α hα
    have h := congrArg (fun z : EuclideanSpace ℝ (relativeRoots i) => z ⟨α, hα⟩) hv
    exact h

/-- The Euclidean norm pulled back along the injective root-coordinate map. -/
abbrev normedAddCommGroup : NormedAddCommGroup (TranslationSpace i) :=
  NormedAddCommGroup.induced _ _ (coordinates i) (coordinates_injective i)

attribute [local instance] normedAddCommGroup

/-- The scalar multiplication is compatible with the root-coordinate norm. -/
abbrev normedSpace : NormedSpace ℝ (TranslationSpace i) :=
  NormedSpace.induced ℝ _ _ (coordinates i)

/-- The apartment translations carry the pulled-back real inner product. -/
abbrev innerProductSpace : InnerProductSpace ℝ (TranslationSpace i) :=
  InnerProductSpace.induced (coordinates i)

attribute [local instance] normedSpace innerProductSpace

theorem norm_sq (v : TranslationSpace i) :
    ‖v‖ ^ 2 = ∑ α : relativeRoots i, (rootForm i α v) ^ 2 :=
  EuclideanSpace.real_norm_sq_eq (coordinates i v)

/-- The reduced translation space is finite dimensional because it embeds
linearly into the finite root-coordinate space. -/
theorem finiteDimensional : FiniteDimensional ℝ (TranslationSpace i) :=
  FiniteDimensional.of_injective (coordinates i) (coordinates_injective i)

/-- Finite-dimensionality makes this Euclidean translation metric complete. -/
theorem completeSpace : CompleteSpace (TranslationSpace i) := by
  let := finiteDimensional i
  infer_instance

variable [Mono i.hom.hom.left]

omit [Fintype (relativeRoots i)] in
/-- A normalizer element permutes the root coordinates contragrediently. -/
theorem rootForm_translationAction (n : normalizerPoints i) (α : relativeRoots i)
    (v : TranslationSpace i) :
    rootForm i α (translationAction i n v) =
      rootForm i (relativeWeylRootPermutation i (QuotientGroup.mk n⁻¹) α) v := by
  induction v using Submodule.Quotient.induction_on with
  | _ v =>
    exact eval_normalizer_smul i n α v

/-- Every existing normalizer linear action preserves the constructed Euclidean
norm. The proof only permutes the finite sum of squared root coordinates. -/
theorem norm_translationAction (n : normalizerPoints i) (v : TranslationSpace i) :
    ‖translationAction i n v‖ = ‖v‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  simp only [norm_sq, rootForm_translationAction]
  exact Fintype.sum_equiv
    (relativeWeylRootPermutation i (QuotientGroup.mk n⁻¹)) _ _ (fun _ => rfl)

end RootTranslationMetric

namespace ValuationBuildingData

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  (B : ValuationBuildingData G)

/-- Finiteness of the actual relative roots of the supplied maximal split torus,
derived from splitness and finite type of the actual reductive group. -/
@[instance_reducible]
def metricRootFintype : Fintype (relativeRoots B.i) := by
  letI := B.isConnectedReductive.smooth
  exact (B.isMaximalSplitTorus.isSplitSubtorus.1.finite_relativeRoots B.i).fintype

attribute [local instance] metricRootFintype

local instance : NormedAddCommGroup (TranslationSpace B.i) :=
  RootTranslationMetric.normedAddCommGroup B.i

local instance : NormedSpace ℝ (TranslationSpace B.i) :=
  RootTranslationMetric.normedSpace B.i

local instance : InnerProductSpace ℝ (TranslationSpace B.i) :=
  RootTranslationMetric.innerProductSpace B.i

/-- A Euclidean metric on the original supplied apartment, defined by the root
norm of its existing affine difference. -/
abbrev apartmentMetricSpace : MetricSpace B.Apartment :=
  metricSpaceOfNormedAddCommGroupOfAddTorsor (TranslationSpace B.i) B.Apartment

attribute [local instance] apartmentMetricSpace

/-- The original affine structure becomes a normed additive torsor for the
constructed metric. -/
abbrev apartmentNormedAddTorsor : NormedAddTorsor (TranslationSpace B.i) B.Apartment where
  dist_eq_norm' _ _ := rfl

attribute [local instance] apartmentNormedAddTorsor

theorem apartment_dist_eq_norm (x y : B.Apartment) :
    dist x y = ‖(x -ᵥ y : TranslationSpace B.i)‖ := rfl

/-- The apartment distance is the square root of the sum of squared actual
root evaluations of the affine displacement. -/
theorem apartment_dist_sq (x y : B.Apartment) :
    dist x y ^ 2 = ∑ α : relativeRoots B.i, (rootForm B.i α (x -ᵥ y)) ^ 2 :=
  RootTranslationMetric.norm_sq B.i (x -ᵥ y)

/-- The normalizer acts by isometries for the constructed apartment metric. -/
theorem apartment_normalizer_isometry (n : normalizerPoints B.i) :
    Isometry (fun x : B.Apartment => n • x) := by
  apply Isometry.of_dist_eq
  intro x y
  rw [apartment_dist_eq_norm, apartment_dist_eq_norm]
  change ‖(B.normalizerAction n).toAffineMap x -ᵥ
    (B.normalizerAction n).toAffineMap y‖ = _
  rw [← (B.normalizerAction n).toAffineMap.linearMap_vsub]
  exact RootTranslationMetric.norm_translationAction B.i n (x -ᵥ y)

/-- Each original apartment is complete for its constructed Euclidean metric. -/
theorem apartment_completeSpace : CompleteSpace B.Apartment := by
  let := RootTranslationMetric.completeSpace B.i
  exact (IsometryEquiv.vaddConst (Classical.arbitrary B.Apartment)).symm.completeSpace

/-- The Euclidean apartment satisfies the Library's midpoint NPC condition.
This concerns the apartment only, before gluing a metric on the building. -/
theorem apartment_nonpositivelyCurved :
    Langlands.Geometry.Metric.KP.IsNonpositivelyCurved B.Apartment := by
  intro x y
  let e : TranslationSpace B.i ≃ᵢ B.Apartment := IsometryEquiv.vaddConst x
  obtain ⟨m, hm⟩ :=
    Langlands.Geometry.Metric.KP.isNonpositivelyCurved_of_innerProductSpace
      (e.symm x) (e.symm y)
  refine ⟨e m, fun z => ?_⟩
  have h := hm (e.symm z)
  simpa only [← e.dist_eq, e.apply_symm_apply] using h

end ValuationBuildingData

end Langlands.Geometry.Building
