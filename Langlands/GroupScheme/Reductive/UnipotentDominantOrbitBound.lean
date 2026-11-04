import Langlands.GroupScheme.SmoothConnectedNormalClosure
import Langlands.GroupScheme.Unipotent.CodimensionOneNormality
import Langlands.GroupScheme.Torus.UnipotentHomNonsplit
import Langlands.GroupScheme.Rational.AlgClosedNormalSolvableTorusStatement
import Langlands.GroupScheme.Rational.TorusGeneratedEnvelope
import Langlands.GroupScheme.Lie.SubgroupCellDimension
import Langlands.GroupScheme.SubgroupRangeTransport

/-! # Unipotent dimension bounds from dominant orbits and solvable stabilizers -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace Lie

variable {k : Type u} [Field k]
    {H G : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom H.X.hom] [IsAffineHom G.X.hom]

/-- A monomorphic subgroup with trivial all-test range has zero actual Lie dimension. -/
theorem dimension_eq_zero_of_range_eq_bot (j : H ⟶ G) [Mono j.hom.hom]
    (hj : SubgroupFunctor.range j = ⊥) : dimension H = 0 := by
  have hrep : (SubgroupFunctor.range j).IsRepresentedBy j := ⟨inferInstance, rfl⟩
  have h := RelativeRoot.finrank_tangentSubmodule_eq_of_isRepresentedBy _ j hrep
  rw [hj, RelativeRoot.tangentSubmodule_bot, finrank_bot] at h
  exact h.symm

end Lie

namespace SchemeAction

variable {k : Type u} [Field k]
    {G H B : GroupScheme (Spec (CommRingCat.of k))}
    {X : Over (Spec (CommRingCat.of k))}
    (a : SchemeAction G X)

/-- The actual factor of a smooth normal closure through a supplied closed
representative of a point stabilizer. -/
def normalClosureStabilizerHom {j : H ⟶ G} (D : SmoothConnectedNormalClosure j)
    (hj : SubgroupFunctor.range j ≤ a.kernel)
    (x : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ X) (b : B ⟶ G)
    (hb : IsClosedSubgroup b) (hrep : (a.stabilizer x).IsRepresentedBy b) :
    D.group ⟶ B :=
  hrep.factorHom D.inclusion (by
    rw [← hrep.2]
    exact a.normalClosure_range_le_stabilizer D hj x b hb hrep)

/-- The stabilizer factor followed by its actual inclusion is the normal-closure inclusion. -/
theorem normalClosureStabilizerHom_comp {j : H ⟶ G}
    (D : SmoothConnectedNormalClosure j) (hj : SubgroupFunctor.range j ≤ a.kernel)
    (x : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ X) (b : B ⟶ G)
    (hb : IsClosedSubgroup b) (hrep : (a.stabilizer x).IsRepresentedBy b) :
    a.normalClosureStabilizerHom D hj x b hb hrep ≫ b = D.inclusion :=
  hrep.factorHom_comp _ _

/-- The factor into a closed stabilizer is itself a closed subgroup inclusion. -/
theorem isClosedSubgroup_normalClosureStabilizerHom {j : H ⟶ G}
    (D : SmoothConnectedNormalClosure j) (hj : SubgroupFunctor.range j ≤ a.kernel)
    (x : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ X) (b : B ⟶ G)
    (hb : IsClosedSubgroup b) (hrep : (a.stabilizer x).IsRepresentedBy b) :
    IsClosedSubgroup (a.normalClosureStabilizerHom D hj x b hb hrep) := by
  apply IsClosedSubgroup.of_comp hb
  rw [normalClosureStabilizerHom_comp]
  exact D.closed

/-- A normal closure inside a solvable closed stabilizer is solvable. -/
theorem normalClosure_isSolvable_of_stabilizer {j : H ⟶ G}
    (D : SmoothConnectedNormalClosure j) (hj : SubgroupFunctor.range j ≤ a.kernel)
    (x : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ X) (b : B ⟶ G)
    (hb : IsClosedSubgroup b) (hrep : (a.stabilizer x).IsRepresentedBy b)
    (hB : IsSolvableGroupScheme B) : IsSolvableGroupScheme D.group := by
  have : IsClosedImmersion (a.normalClosureStabilizerHom D hj x b hb hrep).hom.hom.left :=
    a.isClosedSubgroup_normalClosureStabilizerHom D hj x b hb hrep
  have : Mono (a.normalClosureStabilizerHom D hj x b hb hrep).hom.hom :=
    Over.mono_of_mono_left _
  exact hB.of_mono (a.normalClosureStabilizerHom D hj x b hb hrep)

section AlgebraicallyClosed

attribute [local instance] P2MW.S_GoodReductionJacobian_AbelianSchemePropertyBundle_geometricallyIntegral.S17A0.subsingleton_spec_field

variable [IsAlgClosed k]

/-- Under the explicit normal-solvable-torus input, an affine unipotent
subgroup of the full action kernel is trivial if a point has a solvable closed stabilizer. -/
theorem range_eq_bot_of_unipotent_kernel_of_structural
    (htorus : AlgClosedReductiveNormalSolvableTorusStatement.{u})
    (hG : IsPseudoReductive G)
    [Smooth H.X.hom] [IsAffineHom H.X.hom] [ConnectedSpace H.X.left]
    (j : H ⟶ G) [Mono j.hom.hom] (hH : IsUnipotent H)
    (hj : SubgroupFunctor.range j ≤ a.kernel)
    (x : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ X) (b : B ⟶ G)
    (hb : IsClosedSubgroup b) (hrep : (a.stabilizer x).IsRepresentedBy b)
    (hB : IsSolvableGroupScheme B) : SubgroupFunctor.range j = ⊥ := by
  have : Smooth G.X.hom := hG.smooth
  have : IsAffineHom G.X.hom := hG.isAffineHom
  have : ConnectedSpace G.X.left := hG.connectedSpace
  let D := smoothConnectedNormalClosure j
  have : Smooth D.group.X.hom := D.hasSmoothConnectedGeneration.1
  have : GeometricallyConnected D.group.X.hom := D.hasSmoothConnectedGeneration.2.2.1
  have : ConnectedSpace D.group.X.left :=
    GeometricallyConnected.connectedSpace_of_subsingleton D.group.X.hom
  have hDt : IsTorus D.group := (htorus k G hG D.group D.inclusion D.closed
    D.hasSmoothConnectedGeneration.1 inferInstance
    (a.normalClosure_isSolvable_of_stabilizer D hj x b hb hrep hB) D.isNormal).1
  have : Mono D.inclusion.hom.hom := D.represents.1
  exact hH.range_eq_bot_of_range_le_isTorus hDt j D.inclusion D.contains

/-- A codimension-at-most-one unipotent subgroup fixing a point with dominant
unipotent orbit is trivial in the reductive ambient group under the explicit
normal-solvable-torus input and supplied solvable stabilizer. -/
theorem unipotent_dimension_le_one_of_dominant_orbit_of_structural
    (htorus : AlgClosedReductiveNormalSolvableTorusStatement.{u})
    (hG : IsPseudoReductive G)
    {U : GroupScheme (Spec (CommRingCat.of k))}
    [Smooth U.X.hom] [IsAffineHom U.X.hom] [ConnectedSpace U.X.left]
    [Smooth H.X.hom] [IsAffineHom H.X.hom] [ConnectedSpace H.X.left]
    [IsReduced X.left] [LocallyOfFiniteType X.hom] [IsSeparated X.hom]
    (i : U ⟶ G) [Mono i.hom.hom] (j : H ⟶ U) (hj : IsClosedSubgroup j)
    (hU : IsUnipotent U) (hH : IsUnipotent H)
    (hdim : Lie.dimension U ≤ Lie.dimension H + 1)
    (x : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ X)
    (hx : ((a.restrict i).restrict j).IsFixed x)
    [IsDominant ((a.restrict i).orbitMap x).left]
    [QuasiCompact ((a.restrict i).orbitMap x).left]
    (b : B ⟶ G) (hb : IsClosedSubgroup b)
    (hrep : (a.stabilizer x).IsRepresentedBy b) (hB : IsSolvableGroupScheme B) :
    SubgroupFunctor.range j = ⊥ ∧ Lie.dimension H = 0 ∧ Lie.dimension U ≤ 1 := by
  have : IsClosedImmersion j.hom.hom.left := hj
  have : Mono j.hom.hom := Over.mono_of_mono_left _
  have : Mono (j ≫ i).hom.hom := by
    rw [Grp.comp_hom_hom]
    infer_instance
  have hn := isNormal_of_lieDimension_le_succ_of_isUnipotent j hj hdim hU
  have hk := a.range_comp_le_kernel_of_dominant_orbit i j hn x hx
  have hz := a.range_eq_bot_of_unipotent_kernel_of_structural htorus hG
    (j ≫ i) hH hk x b hb hrep hB
  have hjz := (SubgroupFunctor.range_comp_eq_bot_iff j i).mp hz
  have hHz := Lie.dimension_eq_zero_of_range_eq_bot j hjz
  exact ⟨hjz, hHz, by omega⟩

end AlgebraicallyClosed

end SchemeAction

end Langlands.GroupScheme
