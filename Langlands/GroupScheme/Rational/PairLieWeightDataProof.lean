import Langlands.GroupScheme.Rational.FreudenthalLieInterface
import Langlands.GroupScheme.Rational.CocharacterWeightAction
import Langlands.GroupScheme.Rational.WeightShiftReflection
import Langlands.GroupScheme.Absolute.MaximalTorusCentralizerProof
import Langlands.GroupScheme.Reductive.SplitRootLieLineProof
import Langlands.GroupScheme.Lie.SelfCentralizing

/-! # The actual torus-weight data of a faithful pair Lie algebra -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped Matrix CategoryTheory.MonObj

attribute [local instance 100] LieRing.ofAssociativeRing

namespace Langlands.GroupScheme
namespace SplitPinning

set_option backward.isDefEq.respectTransparency false

variable {k : Type u} [Field k]
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom] (p : SplitPinning G) {N n : ℕ}

local instance : IsAffineHom p.torus.toGrp.X.hom := p.isSplitTorus.isAffineHom

omit [LocallyOfFiniteType G.X.hom] in
/-- Actual adjoint weights act as weight shifts on the pair representation. -/
theorem pairTangent_mem_weightShift
    (sigma : MatrixRepresentation G (Fin N)) (r : MatrixRepresentation G (Fin n))
    {chi : characterLattice p.torus} {X : Additive (lieKernel G k)}
    (hX : X ∈ weightSpace p.inclusion chi) :
    MatrixRepresentation.pairTangent sigma r X ∈ p.weightShift sigma r chi := by
  intro mu u hu
  exact ⟨p.tangentMatrix_mulVec_mem_representationWeightSpace sigma hX mu hu.1,
    p.tangentMatrix_mulVec_mem_representationWeightSpace r hX mu hu.2⟩

omit [LocallyOfFiniteType G.X.hom] in
/-- Faithfulness of the first block reflects pair weight shifts to actual adjoint weights. -/
theorem mem_weightSpace_of_pairTangent_mem_weightShift
    (sigma : MatrixRepresentation G (Fin N)) (r : MatrixRepresentation G (Fin n))
    (hsigma : Mono sigma.hom.hom) (chi : characterLattice p.torus)
    (X : Additive (lieKernel G k))
    (hX : MatrixRepresentation.pairTangent sigma r X ∈ p.weightShift sigma r chi) :
    X ∈ weightSpace p.inclusion chi := by
  apply p.mem_weightSpace_of_kernelDifferential_mem_representationWeightShift sigma hsigma chi X
  intro mu v hv
  exact (hX mu (v, 0) ⟨hv, Submodule.zero_mem _⟩).1

omit [LocallyOfFiniteType G.X.hom] in
/-- A faithful first block makes the pair tangent map injective. -/
theorem pairTangent_injective
    (sigma : MatrixRepresentation G (Fin N)) (r : MatrixRepresentation G (Fin n))
    (hsigma : Mono sigma.hom.hom) :
    Function.Injective (MatrixRepresentation.pairTangent sigma r) := by
  intro X Y h
  apply Additive.toMul.injective
  apply sigma.tangentMatrix_injective hsigma k
  apply Matrix.toLin'.injective
  apply LinearMap.ext
  intro v
  exact congrArg Prod.fst (LinearMap.congr_fun h (v, 0))

/-- The degree-`chi` piece of the pair Lie algebra is the image of the actual adjoint weight. -/
theorem pairLieGraded_eq_map_weightSpace
    (sigma : MatrixRepresentation G (Fin N)) (r : MatrixRepresentation G (Fin n))
    (hsigma : Mono sigma.hom.hom) (chi : characterLattice p.torus) :
    p.pairLieGraded sigma r chi =
      (weightSpace p.inclusion chi).map (MatrixRepresentation.pairTangent sigma r) := by
  ext f
  constructor
  · rintro ⟨⟨X, rfl⟩, hX⟩
    exact ⟨X, p.mem_weightSpace_of_pairTangent_mem_weightShift sigma r hsigma chi X hX, rfl⟩
  · rintro ⟨X, hX, rfl⟩
    exact ⟨⟨X, rfl⟩, p.pairTangent_mem_weightShift sigma r hX⟩

/-- A faithful pair tangent map identifies each actual adjoint weight with its graded piece. -/
def pairLieWeightEquiv
    (sigma : MatrixRepresentation G (Fin N)) (r : MatrixRepresentation G (Fin n))
    (hsigma : Mono sigma.hom.hom) (chi : characterLattice p.torus) :
    weightSpace p.inclusion chi ≃ₗ[k] p.pairLieGraded sigma r chi :=
  (Submodule.equivMapOfInjective (MatrixRepresentation.pairTangent sigma r)
    (pairTangent_injective sigma r hsigma) (weightSpace p.inclusion chi)).trans
      (LinearEquiv.ofEq _ _ (p.pairLieGraded_eq_map_weightSpace sigma r hsigma chi).symm)

/-- The pair action obtained by differentiating an actual cocharacter. -/
def pairCocharacterAction
    (sigma : MatrixRepresentation G (Fin N)) (r : MatrixRepresentation G (Fin n))
    (y : cocharacterLattice p.torus) : Module.End k ((Fin N → k) × (Fin n → k)) :=
  MatrixRepresentation.pairTangent sigma r
    (Lie.targetMapLinear p.inclusion k (Additive.ofMul (Lie.cocharacterTangent y)))

omit [LocallyOfFiniteType G.X.hom] in
/-- Actual cocharacter tangent actions satisfy the scalar-action interface. -/
theorem pairCocharacterAction_isCocharacterAction
    (sigma : MatrixRepresentation G (Fin N)) (r : MatrixRepresentation G (Fin n))
    (y : cocharacterLattice p.torus) :
    p.IsCocharacterAction sigma r y (p.pairCocharacterAction sigma r y) := by
  intro mu u hu
  apply Prod.ext
  · exact p.representationCocharacterAction_apply sigma y mu hu.1
  · exact p.representationCocharacterAction_apply r y mu hu.2

/-- The pair Lie algebra is the sum of its graded pieces. -/
theorem pairLieAlgebra_eq_iSup_pairLieGraded
    (sigma : MatrixRepresentation G (Fin N)) (r : MatrixRepresentation G (Fin n))
    (hsigma : Mono sigma.hom.hom) :
    (MatrixRepresentation.pairLieAlgebra sigma r).toSubmodule =
      ⨆ chi : characterLattice p.torus, p.pairLieGraded sigma r chi := by
  classical
  simp_rw [p.pairLieGraded_eq_map_weightSpace sigma r hsigma]
  rw [← Submodule.map_iSup,
    (isInternal_weightSpace_of_isSplitTorus k G p.torus p.isSplitTorus
      p.inclusion).submodule_iSup_eq_top, Submodule.map_top]
  rfl

/-- Degree zero consists of linear combinations of actual cocharacter actions. -/
theorem pairLieGraded_zero_le_span_cocharacterAction
    (sigma : MatrixRepresentation G (Fin N)) (r : MatrixRepresentation G (Fin n))
    (hsigma : Mono sigma.hom.hom) :
    p.pairLieGraded sigma r 0 ≤
      Submodule.span k {x | ∃ y : cocharacterLattice p.torus, p.IsCocharacterAction sigma r y x} := by
  let : Mono p.inclusion.hom.hom := p.isMaximalTorus.2.1.mono_overHom
  have hself := maximalTorusCentralizer k G p.isConnectedReductive p.torus p.inclusion
    p.isMaximalTorus
  let e := Lie.zeroWeightEquivOfSelfCentralizing p.inclusion hself
  let S := Submodule.span k {x | ∃ y : cocharacterLattice p.torus,
    p.IsCocharacterAction sigma r y x}
  let L := (MatrixRepresentation.pairTangent sigma r).comp
    (Lie.targetMapLinear p.inclusion k)
  have hspan : ∀ Y, L Y ∈ S := by
    have hle : Submodule.span k (Set.range fun y : cocharacterLattice p.torus =>
        Additive.ofMul (Lie.cocharacterTangent y)) ≤ S.comap L := by
      apply Submodule.span_le.mpr
      rintro _ ⟨y, rfl⟩
      exact Submodule.subset_span ⟨y, p.pairCocharacterAction_isCocharacterAction sigma r y⟩
    rw [Lie.span_cocharacterTangent p.isSplitTorus] at hle
    intro Y
    exact hle Submodule.mem_top
  rw [p.pairLieGraded_eq_map_weightSpace sigma r hsigma]
  rintro _ ⟨X, hX, rfl⟩
  let Y := e.symm ⟨X, hX⟩
  have hY : Lie.targetMapLinear p.inclusion k Y = X :=
    congrArg Subtype.val (e.apply_symm_apply ⟨X, hX⟩)
  rw [← hY]
  exact hspan Y

/-- Nonzero degrees not among the actual roots have zero pair Lie piece. -/
theorem pairLieGraded_eq_bot_of_not_root
    (sigma : MatrixRepresentation G (Fin N)) (r : MatrixRepresentation G (Fin n))
    (hsigma : Mono sigma.hom.hom) (chi : characterLattice p.torus)
    (hchi : chi ≠ 0) (hroot : chi ∉ Set.range p.rootDatum.root) :
    p.pairLieGraded sigma r chi = ⊥ := by
  have hbot : weightSpace p.inclusion chi = ⊥ := by
    by_contra h
    exact hroot (p.isRootDatum.2.1.symm ▸ (show chi ∈ roots p.inclusion from ⟨hchi, h⟩))
  rw [p.pairLieGraded_eq_map_weightSpace sigma r hsigma, hbot, Submodule.map_bot]

/-- Every actual root degree in the faithful pair Lie algebra is one-dimensional. -/
theorem finrank_pairLieGraded_root
    (sigma : MatrixRepresentation G (Fin N)) (r : MatrixRepresentation G (Fin n))
    (hsigma : Mono sigma.hom.hom) (i : p.rootIndex) :
    Module.finrank k (p.pairLieGraded sigma r (p.rootDatum.root i)) = 1 := by
  have hi : p.rootDatum.root i ∈ roots p.inclusion :=
    p.isRootDatum.2.1 ▸ Set.mem_range_self i
  obtain ⟨e⟩ := splitRootLieLine k G p.isConnectedReductive p.torus p.isSplitTorus
    p.inclusion p.isMaximalTorus (p.rootDatum.root i) hi
  calc
    Module.finrank k (p.pairLieGraded sigma r (p.rootDatum.root i)) =
        Module.finrank k (weightSpace p.inclusion (p.rootDatum.root i)) :=
      (p.pairLieWeightEquiv sigma r hsigma _).finrank_eq.symm
    _ = Module.finrank k k := e.finrank_eq.symm
    _ = 1 := Module.finrank_self k

/-- All group-side pair Lie weight facts hold for a closed first representation. -/
theorem pairLieWeightData [CharZero k]
    (sigma : MatrixRepresentation G (Fin N)) (r : MatrixRepresentation G (Fin n))
    (hsigma : IsClosedSubgroup sigma) : p.PairLieWeightData sigma r := by
  have hm := hsigma.mono_overHom
  refine ⟨(p.pairLieAlgebra_eq_iSup_pairLieGraded sigma r hm).le, ?_,
    p.pairLieGraded_zero_le_span_cocharacterAction sigma r hm,
    p.pairLieGraded_eq_bot_of_not_root sigma r hm,
    p.finrank_pairLieGraded_root sigma r hm,
    p.exists_weight_pairing_ne_zero_of_isClosedSubgroup sigma hsigma⟩
  intro y
  exact ⟨p.pairCocharacterAction sigma r y, ⟨_, rfl⟩,
    p.pairCocharacterAction_isCocharacterAction sigma r y⟩

end SplitPinning

/-- The group-side torus grading and cocharacter data needed by the Casimir argument. -/
theorem pairLieWeightDataStatement : PairLieWeightDataStatement.{u} := by
  intro k _ _ G _ _ p N n sigma r hsigma
  exact p.pairLieWeightData sigma r hsigma

end Langlands.GroupScheme
