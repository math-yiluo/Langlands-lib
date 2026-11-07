import Langlands.GroupScheme.HomImageEmbedding
import Langlands.GroupScheme.MatrixRepresentation.TorusEquivariantAdditive
import Langlands.GroupScheme.Rational.SteinbergRootMapUniqueness
import Langlands.GroupScheme.Rational.VectorGroupUnipotent
import Langlands.GroupScheme.Rational.TangentWeightTransport
import Langlands.GroupScheme.Rational.RootPointLieEquiv
import Langlands.GroupScheme.Rational.RootSubgroupUniquenessProof
import Langlands.GroupScheme.Reductive.SplitRootLieLineProof
import Langlands.GroupScheme.Torus.MaximalSplitComparison

/-! # Monic equivariant additive maps represent entire root subgroups -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.VectorGroup

variable {k : Type u} [Field k]
    {G : GroupScheme (Spec (CommRingCat.of k))}
    {T : CommGroupScheme (Spec (CommRingCat.of k))}
    {i : T.toGrp ⟶ G}
    {x : groupScheme (CommRingCat.of k) 1 ⟶ G} {α : characterLattice T}

local notation "V" => groupScheme (CommRingCat.of k) 1
local notation "coords" => coordinates (CommRingCat.of k) 1

local instance : IsAffineHom (V).X.hom :=
  isAffineHom_groupScheme (CommRingCat.of k) 1

namespace IsTorusEquivariant

variable (hx : IsTorusEquivariant i x α)

include hx

/-- Scalar equivariance is equivariance of the actual additive group action. -/
theorem weightAction_comp (Z : Over (Spec (CommRingCat.of k)))
    (t : Z ⟶ T.X) (v : Z ⟶ (V).X) :
    (weightAction α).act t v ≫ x.hom.hom =
      (AutomorphicAction.conjugation i).act t (v ≫ x.hom.hom) := by
  have hw : (weightAction α).act t v =
      scalarPoint (CommRingCat.of k) Z
        (charValue α Z t * (coords Z v).toAdd 0) := by
    apply points_ext
    intro j
    rw [coordinates_weightAction_act, coordinates_scalarPoint]
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [Subsingleton.elim j 0]
  rw [hw, ← hx Z t ((coords Z v).toAdd 0), scalarPoint_coordinate]
  rw [AutomorphicAction.conjugation_act]

/-- The image of an equivariant additive map is stable on every test scheme. -/
theorem range_isStable :
    (AutomorphicAction.conjugation i).IsStable (SubgroupFunctor.range x) := by
  intro Z t v hv
  obtain ⟨a, rfl⟩ := hv
  exact ⟨(weightAction α).act t a, hx.weightAction_comp Z t a⟩

variable [IsAffineHom G.X.hom]

/-- The whole differential image of an equivariant additive line has weight alpha. -/
theorem lie_range_le_weightSpace :
    LinearMap.range (Lie.targetMapLinear x k) ≤ weightSpace i α := by
  rintro _ ⟨v, rfl⟩
  have hv : v ∈ RelativeRoot.actionWeightSpace (weightAction (n := 1) α) α := by
    rw [(isWeightVectorCoordinates_weightAction (n := 1) α).actionWeightSpace_eq_top]
    trivial
  simpa only [RelativeRoot.actionWeightSpace_conjugation] using
    (RelativeRoot.lieKernelTargetLinear_mem_actionWeightSpace
      (AutomorphicAction.conjugation i) (weightAction α) x
      (fun Z t v => hx.weightAction_comp Z t v) α hv)

variable [Mono x.hom.hom]

/-- For a one-dimensional target root space, monicity makes the entire
differential image equal to that space. -/
theorem lie_range_eq_weightSpace
    (hline : Nonempty (k ≃ₗ[k] weightSpace i α)) :
    LinearMap.range (Lie.targetMapLinear x k) = weightSpace i α := by
  obtain ⟨e⟩ := hline
  let : Module.Finite k (weightSpace i α) := Module.Finite.equiv e
  let E := RelativeRoot.vectorLieCoordinates coords isNaturalVectorCoordinates
    (CommAlgCat.of k k)
  apply Submodule.eq_of_le_of_finrank_eq hx.lie_range_le_weightSpace
  rw [LinearMap.finrank_range_of_inj (Lie.targetMapLinear_injective x k),
    E.finrank_eq, ← e.finrank_eq]
  simp

/-- The actual differential identifies the source Lie algebra with the
entire target root weight line. -/
def rootLieEquiv (hline : Nonempty (k ≃ₗ[k] weightSpace i α)) :
    Additive (lieKernel V k) ≃ₗ[k] weightSpace i α :=
  (LinearEquiv.ofInjective (Lie.targetMapLinear x k)
    (Lie.targetMapLinear_injective x k)).trans
      (LinearEquiv.ofEq _ _ (hx.lie_range_eq_weightSpace hline))

@[simp]
theorem rootLieEquiv_coe (hline : Nonempty (k ≃ₗ[k] weightSpace i α))
    (v : Additive (lieKernel V k)) :
    (hx.rootLieEquiv hline v : Additive (lieKernel G k)) =
      Lie.targetMapLinear x k v := rfl

/-- A monic equivariant additive line represents the whole root subgroup
when the positive integral root span is a line. -/
theorem represents_root_of_lie_line
    (hG : IsConnectedReductive G) (hT : IsSplitTorus T.toGrp)
    (hi : IsMaximalTorus i) (hα : α ∈ roots i)
    (hhigh : RelativeRoot.HasNoHigherRoots i α)
    (hline : Nonempty (k ≃ₗ[k] weightSpace i α)) :
    (RelativeRoot.subgroup i α).IsRepresentedBy x := by
  let hV : RelativeRoot.IsVectorGroupOfDimension V 1 :=
    ⟨coords, isNaturalVectorCoordinates⟩
  let := hV.smooth
  let := hV.connectedSpace
  let := hG.smooth
  have hspan : RelativeRoot.positiveWeightSpan i α = weightSpace i α := by
    rw [← RelativeRoot.semigroupWeightSpan_cyclicTail_one_conjugation]
    exact RelativeRoot.semigroupWeightSpan_eq_weightSpace_of_noHigherRoots
      hT i hα.1 hhigh
  refine ⟨inferInstance, ?_⟩
  apply RelativeRoot.rootSubgroupUniqueness k G hG T i
    (hi.isMaximalSplitTorus hT) α hα V x
    (HomImage.isClosedSubgroup_of_mono x) hV.smooth hV.connectedSpace hx.range_isStable
  rw [hspan, ← hx.lie_range_eq_weightSpace hline]
  exact RelativeRoot.hasLieImage_range x

/-- Every monic additive map with a genuine root character of a split maximal
torus represents the entire intrinsic root subgroup, in the absence of higher roots. -/
theorem represents_root
    (hG : IsConnectedReductive G) (hT : IsSplitTorus T.toGrp)
    (hi : IsMaximalTorus i) (hα : α ∈ roots i)
    (hhigh : RelativeRoot.HasNoHigherRoots i α) :
    (RelativeRoot.subgroup i α).IsRepresentedBy x :=
  hx.represents_root_of_lie_line hG hT hi hα hhigh
    (splitRootLieLine k G hG T hT i hi α hα)

end IsTorusEquivariant
end Langlands.GroupScheme.VectorGroup
