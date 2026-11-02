import Langlands.Global.AdelicGroupNormOne
import Langlands.Global.PrincipalAdelesDiscreteProof
import Mathlib.LinearAlgebra.Countable

/-! # Principal rational points inside actual adelic groups -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain Topology
open scoped CategoryTheory.MonObj

namespace Langlands.Global.AdelicGroupPoints

open Langlands.AlgebraicGeometry.PointTopology

variable (F : Type u) [Field F] [NumberField F]
  (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffine G.X.left]

/-- The actual principal map is injective, since all regular values extend injectively. -/
theorem rational_injective : Function.Injective (rational F G) := by
  intro x y h
  apply G.affinePointEvaluation_injective (CommAlgCat.of F F)
  funext a
  apply AdeleRing.algebraMap_injective (𝓞 F) F
  have hv := congrArg (fun z => G.affinePointEvaluation
    (CommAlgCat.of F (AdeleRing (𝓞 F) F)) z a) h
  change G.affinePointEvaluation _ (G.affinePointMap _ x) a =
    G.affinePointEvaluation _ (G.affinePointMap _ y) a at hv
  exact (G.affinePointEvaluation_map
    (CommAlgCat.ofHom (Algebra.ofId F (AdeleRing (𝓞 F) F))) x a).symm.trans
      (hv.trans (G.affinePointEvaluation_map
        (CommAlgCat.ofHom (Algebra.ofId F (AdeleRing (𝓞 F) F))) y a))

/-- The induced principal map into the genuine norm-one subgroup is also injective. -/
theorem rationalNormOne_injective : Function.Injective (rationalNormOne F G) := by
  intro x y h
  exact rational_injective F G (congrArg Subtype.val h)

/-- A regular function sends an actual principal point to a principal additive adele. -/
def principalCoordinate (a : AffineCoordinateRing (CommRingCat.of F) G.X)
    (x : rationalSubgroup F G) : principalAdeles F :=
  ⟨G.affinePointEvaluation (CommAlgCat.of F (AdeleRing (𝓞 F) F)) x a, by
    rcases x.property with ⟨q, hq⟩
    change ∃ b : F, diagonal F b = _
    refine ⟨G.affinePointEvaluation (CommAlgCat.of F F) q a, ?_⟩
    rw [← hq]
    exact (G.affinePointEvaluation_map
      (CommAlgCat.ofHom (Algebra.ofId F (AdeleRing (𝓞 F) F))) q a).symm⟩

omit [IsAffine G.X.left] in
/-- Regular coordinates on the principal subgroup are continuous in the subspace topologies. -/
theorem continuous_principalCoordinate
    (a : AffineCoordinateRing (CommRingCat.of F) G.X) :
    Continuous (principalCoordinate F G a) := by
  apply continuous_induced_rng.mpr
  exact (G.continuous_affinePointEvaluation
    (CommAlgCat.of F (AdeleRing (𝓞 F) F)) a).comp continuous_subtype_val

variable [LocallyOfFiniteType G.X.hom]

/-- Finite-type actual adelic points embed by finitely many regular values. -/
theorem exists_finiteEvaluationEmbedding :
    ∃ (n : ℕ) (a : Fin n → AffineCoordinateRing (CommRingCat.of F) G.X),
      IsEmbedding (fun (x : AdelicGroupPoints F G) (i : Fin n) =>
        G.affinePointEvaluation (CommAlgCat.of F (AdeleRing (𝓞 F) F)) x (a i)) := by
  obtain ⟨n, f, hf⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.mp
    (inferInstance : Algebra.FiniteType (CommRingCat.of F)
      (AffineCoordinateRing (CommRingCat.of F) G.X))
  refine ⟨n, fun i => f (MvPolynomial.X i), ?_⟩
  have h := ((AlgPoint.polynomialPointHomeomorph (R := CommRingCat.of F)
    (S := AdeleRing (𝓞 F) F) (Fin n)).isEmbedding.comp
      (AlgPoint.isEmbedding_precomp_of_surjective f hf)).comp
        (G.affinePointsAlgebraHomeomorph
          (CommAlgCat.of F (AdeleRing (𝓞 F) F))).isEmbedding
  change IsEmbedding (fun (x : AdelicGroupPoints F G) (i : Fin n) =>
    affineSchemePointEquiv (CommRingCat.of F) G.X
      (CommAlgCat.of F (AdeleRing (𝓞 F) F)) x (f (MvPolynomial.X i))) at h
  simpa only [G.affineSchemePointEquiv_evaluation
    (CommAlgCat.of F (AdeleRing (𝓞 F) F))] using h

/-- Finitely many regular functions inject the rational subgroup into principal adeles. -/
theorem exists_principalCoordinates_injective :
    ∃ (n : ℕ) (a : Fin n → AffineCoordinateRing (CommRingCat.of F) G.X),
      Function.Injective (fun x : rationalSubgroup F G =>
        fun i : Fin n => principalCoordinate F G (a i) x) := by
  obtain ⟨n, a, ha⟩ := exists_finiteEvaluationEmbedding F G
  refine ⟨n, a, ?_⟩
  intro x y h
  apply Subtype.ext
  apply ha.injective
  funext i
  exact congrArg Subtype.val (congrFun h i)

/-- The principal rational subgroup is discrete in the actual adelic group. -/
instance rationalSubgroup_discreteTopology : DiscreteTopology (rationalSubgroup F G) := by
  have : DiscreteTopology (principalAdeles F) := principalAdeles_discreteTopology F
  obtain ⟨n, a, ha⟩ := exists_principalCoordinates_injective F G
  exact DiscreteTopology.of_continuous_injective
    (continuous_pi fun i => continuous_principalCoordinate F G (a i)) ha

/-- The discrete principal subgroup is closed in the Hausdorff adelic group. -/
theorem rationalSubgroup_isClosed :
    IsClosed (rationalSubgroup F G : Set (AdelicGroupPoints F G)) :=
  Subgroup.isClosed_of_discreteTopology

/-- Finite-type rational points over a number field form a countable group. -/
instance rationalGroupPoints_countable : Countable (RationalGroupPoints F G) := by
  have : Countable F := Finsupp.Countable.of_moduleFinite (R := ℚ)
  have : Countable (principalAdeles F) := by
    apply Function.Surjective.countable
      (f := fun x : F => (⟨diagonal F x, ⟨x, rfl⟩⟩ : principalAdeles F))
    rintro ⟨a, x, rfl⟩
    exact ⟨x, rfl⟩
  obtain ⟨n, a, ha⟩ := exists_principalCoordinates_injective F G
  have : Countable (rationalSubgroup F G) := ha.countable
  exact Function.Injective.countable
    (f := fun x => (⟨rational F G x, ⟨x, rfl⟩⟩ : rationalSubgroup F G))
    (fun x y h => rational_injective F G (congrArg Subtype.val h))

/-- The countable principal subgroup is exactly the image of the actual rational map. -/
instance rationalSubgroup_countable : Countable (rationalSubgroup F G) := by
  apply Function.Surjective.countable
    (f := fun x : RationalGroupPoints F G =>
      (⟨rational F G x, ⟨x, rfl⟩⟩ : rationalSubgroup F G))
  rintro ⟨a, x, rfl⟩
  exact ⟨x, rfl⟩

/-- The actual principal subgroup of the norm-one adelic group. -/
def rationalNormOneSubgroup : Subgroup (normOneSubgroup F G) :=
  (rationalNormOne F G).range

/-- Inclusion of principal norm-one points into the full principal subgroup. -/
def rationalNormOneSubgroupInclusion :
    rationalNormOneSubgroup F G →* rationalSubgroup F G where
  toFun x := ⟨x.val.val, by
    rcases x.property with ⟨q, hq⟩
    exact ⟨q, congrArg Subtype.val hq⟩⟩
  map_one' := rfl
  map_mul' _ _ := rfl

omit [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom] in
/-- This inclusion is injective on the actual subgroup carriers. -/
theorem rationalNormOneSubgroupInclusion_injective :
    Function.Injective (rationalNormOneSubgroupInclusion F G) := by
  intro x y h
  apply Subtype.ext
  apply Subtype.ext
  exact congrArg (fun z : rationalSubgroup F G =>
    (z : AdelicGroupPoints F G)) h

omit [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom] in
/-- The inclusion is continuous in the two subgroup topologies. -/
theorem continuous_rationalNormOneSubgroupInclusion :
    Continuous (rationalNormOneSubgroupInclusion F G) := by
  apply continuous_induced_rng.mpr
  change Continuous (fun x : rationalNormOneSubgroup F G =>
    (x.val.val : AdelicGroupPoints F G))
  exact continuous_subtype_val.comp continuous_subtype_val

instance rationalNormOneSubgroup_discreteTopology :
    DiscreteTopology (rationalNormOneSubgroup F G) :=
  DiscreteTopology.of_continuous_injective
    (continuous_rationalNormOneSubgroupInclusion F G)
    (rationalNormOneSubgroupInclusion_injective F G)

theorem rationalNormOneSubgroup_isClosed :
    IsClosed (rationalNormOneSubgroup F G : Set (normOneSubgroup F G)) :=
  Subgroup.isClosed_of_discreteTopology

instance rationalNormOneSubgroup_countable :
    Countable (rationalNormOneSubgroup F G) :=
  (rationalNormOneSubgroupInclusion_injective F G).countable

end Langlands.Global.AdelicGroupPoints
