import Langlands.Algebra.GradedIdealSupportStatement
import Langlands.GroupScheme.Rational.CoordinateSemigroupAlgebra
import Langlands.GroupScheme.Rational.CharacterLatticeProof
import Mathlib.Algebra.GradedMonoid

/-! # Reduction of actual augmentation support to graded ideal generation -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.CoordinateWeights

variable {k : Type u} [Field k]
    {S : CommGroupScheme (Spec (CommRingCat.of k))}
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]

set_option linter.defProp false in
/-- Actual ideal eigenspaces have homogeneous multiplication, without a unit
or a chosen decomposition. This explicit structure is passed to the generic
ideal theorem. -/
@[instance_reducible]
def augmentationGradedMul (b : AutomorphicAction S.toGrp G) :
    SetLike.GradedMul (R := augmentationIdeal G) (augmentationWeightSpace b) where
  mul_mem := by
    intro χ ψ x y hx hy
    exact mul_mem_weightSpace b hx hy

/-- The identity ideal of the actual coordinate algebra is proper. -/
theorem augmentationIdeal_ne_top : augmentationIdeal G ≠ ⊤ := by
  intro h
  have h1 : (1 : CharacterUnits.Coord G) ∈ augmentationIdeal G := h ▸ trivial
  change Lie.coordinateOrigin G 1 = 0 at h1
  exact (one_ne_zero : (1 : k) ≠ 0) (by simpa only [map_one] using h1)

/-- The actual affine coordinate algebra is Noetherian over the ground field. -/
theorem isNoetherianRing_coord [LocallyOfFiniteType G.X.hom] :
    IsNoetherianRing (CharacterUnits.Coord G) := by
  let D := CharacterUnits.Coord G
  have : Algebra.FiniteType (CommRingCat.of k) D := Lie.coordinateAlgebraFiniteType G
  have : IsNoetherianRing (CommRingCat.of k) := inferInstanceAs (IsNoetherianRing k)
  exact Algebra.FiniteType.isNoetherianRing (CommRingCat.of k) D

/-- Same-character quotient lifting identifies the generic lift support with
the actual cotangent support. -/
theorem cotangentLiftSupport_eq (b : AutomorphicAction S.toGrp G)
    (hlift : ∀ χ : characterLattice S,
      (augmentationWeightSpace b χ).map (cotangentMk G) = cotangentWeightSpace b χ) :
    Langlands.Algebra.GradedIdealSupport.cotangentLiftSupport
      (augmentationIdeal G) (augmentationWeightSpace b) = cotangentSupport b := by
  ext χ
  constructor
  · rintro ⟨f, hf, hq⟩
    refine ⟨cotangentMk G f, hq, ?_⟩
    rw [← hlift χ]
    exact ⟨f, hf, rfl⟩
  · rintro ⟨q, hq, hqw⟩
    rw [← hlift χ] at hqw
    obtain ⟨f, hf, rfl⟩ := hqw
    exact ⟨f, hf, hq⟩

open Classical in
/-- The generic proper-ideal theorem gives the actual cotangent semigroup
equality after internal decomposition and same-character lifting. -/
theorem support_eq_closure_cotangent_of_gradedIdeal
    (hgen : Langlands.Algebra.GradedIdealSupport.PositiveGenerationStatement.{u, u, u})
    [Smooth G.X.hom] [ConnectedSpace G.X.left]
    (b : AutomorphicAction S.toGrp G)
    (hW : DirectSum.IsInternal (augmentationWeightSpace b))
    (hlift : ∀ χ : characterLattice S,
      (augmentationWeightSpace b χ).map (cotangentMk G) = cotangentWeightSpace b χ) :
    support b = (AddSubsemigroup.closure (cotangentSupport b) :
      Set (characterLattice S)) := by
  classical
  let := CharacterLatticeProof.isDomain_coord G
  let := isNoetherianRing_coord (G := G)
  have h := hgen k (CharacterUnits.Coord G) (characterLattice S)
    (augmentationIdeal G) augmentationIdeal_ne_top (augmentationWeightSpace b) hW
    (fun _ _ _ _ hx hy => (augmentationGradedMul b).mul_mem hx hy)
  change support b = (AddSubsemigroup.closure
    (Langlands.Algebra.GradedIdealSupport.cotangentLiftSupport
      (augmentationIdeal G) (augmentationWeightSpace b)) : Set (characterLattice S)) at h
  rwa [cotangentLiftSupport_eq b hlift] at h

/-- Three separate prerequisites suffice for the unchanged exact group target. -/
theorem coordinateSemigroupComparison_of_prerequisites
    (hgen : Langlands.Algebra.GradedIdealSupport.PositiveGenerationStatement.{u, u, u})
    (hdecomp : CoordinateWeightDecompositionStatement.{u})
    (hlie : CotangentLieSupportStatement.{u}) :
    CoordinateSemigroupComparisonStatement.{u} := by
  apply coordinateSemigroupComparison_of_semigroup
  intro k _ G hsm hAff hconn S hsplit b
  classical
  let := hAff
  let := hsm
  let := hconn
  obtain ⟨_, hW, _, hlift⟩ := hdecomp k G hAff S hsplit b
  rw [support_eq_closure_cotangent_of_gradedIdeal hgen b hW hlift,
    hlie k G hAff inferInstance S hsplit b]

end Langlands.GroupScheme.CoordinateWeights
