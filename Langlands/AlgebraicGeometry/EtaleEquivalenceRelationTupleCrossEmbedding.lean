import Langlands.AlgebraicGeometry.EtaleEquivalenceRelationTupleCrossQuotient
import Langlands.AlgebraicGeometry.FiniteFreeSchemeActionProduct

/-! # Closed cross-correspondences between symmetric tuple schemes -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.AlgebraicGeometry

/-- Closed immersions between affine schemes descend along a flat surjective
change of the affine target. -/
theorem isClosedImmersion_of_isPullback_of_affine_fpqc
    {T X Y Z : Scheme.{u}} [IsAffine T] [IsAffine X] [IsAffine Y] [IsAffine Z]
    {i : T ⟶ X} {p : T ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z}
    (h : IsPullback i p f g) [Flat f] [Surjective f] [IsClosedImmersion i] :
    IsClosedImmersion g := by
  apply IsClosedImmersion.of_surjective_of_isAffine
  have hp := isPushout_appTop_of_isPullback h
  have hf := (Flat.flat_and_surjective_iff_faithfullyFlat_of_isAffine f).mp
    ⟨inferInstance, inferInstance⟩
  have hi := (IsClosedImmersion.isAffine_surjective_of_isAffine i).2
  let : Algebra Γ(Z, ⊤) Γ(X, ⊤) := f.appTop.hom.toAlgebra
  let : Algebra Γ(Z, ⊤) Γ(Y, ⊤) := g.appTop.hom.toAlgebra
  let : Algebra Γ(X, ⊤) Γ(T, ⊤) := i.appTop.hom.toAlgebra
  let : Algebra Γ(Y, ⊤) Γ(T, ⊤) := p.appTop.hom.toAlgebra
  let : Algebra Γ(Z, ⊤) Γ(T, ⊤) := (f.appTop ≫ i.appTop).hom.toAlgebra
  let : IsScalarTower Γ(Z, ⊤) Γ(X, ⊤) Γ(T, ⊤) :=
    IsScalarTower.of_algebraMap_eq' rfl
  let : IsScalarTower Γ(Z, ⊤) Γ(Y, ⊤) Γ(T, ⊤) :=
    IsScalarTower.of_algebraMap_eq' (congrArg CommRingCat.Hom.hom hp.w)
  let : Algebra.IsPushout Γ(Z, ⊤) Γ(Y, ⊤) Γ(X, ⊤) Γ(T, ⊤) :=
    (CommRingCat.isPushout_iff_isPushout.mp hp).symm
  exact RingHom.FaithfullyFlat.codescendsAlong_surjective hf hi

namespace EtaleEquivalenceRelation

variable (E : EtaleEquivalenceRelation.{u}) [IsSeparated E.s] (m n : ℕ)

/-- The ordered cross-correspondence is the inverse image of the original
relation under the zeroth-coordinate product map. -/
theorem tupleCross_isPullback_relation :
    IsPullback (E.tupleCrossMap m n)
      (prod.lift (E.tupleCrossLeft m n) (E.tupleCrossRight m n))
      (prod.lift E.t E.s)
      (prod.map (E.tupleDistinctProjection m 0) (E.tupleDistinctProjection n 0)) := by
  refine IsPullback.mk' ?_ ?_ ?_
  · apply prod.hom_ext
    · simp [E.tupleCrossMap_t]
    · simp [E.tupleCrossMap_s]
  · intro T a b _ hab
    apply E.tupleCross_hom_ext m n
    · simpa using congrArg (· ≫ prod.fst) hab
    · simpa using congrArg (· ≫ prod.snd) hab
  · intro T a b hab
    have ht : a ≫ E.t = (b ≫ prod.fst) ≫ E.tupleDistinctProjection m 0 := by
      simpa using congrArg (· ≫ prod.fst) hab
    have hs : a ≫ E.s = (b ≫ prod.snd) ≫ E.tupleDistinctProjection n 0 := by
      simpa using congrArg (· ≫ prod.snd) hab
    refine ⟨E.tupleCrossLift m n (b ≫ prod.fst) (b ≫ prod.snd) a ht hs, ?_, ?_⟩
    · simp
    · apply prod.hom_ext <;> simp

instance tupleCross_joint_isClosedImmersion
    [IsClosedImmersion (prod.lift E.t E.s)] :
    IsClosedImmersion (prod.lift (E.tupleCrossLeft m n) (E.tupleCrossRight m n)) :=
  MorphismProperty.of_isPullback (E.tupleCross_isPullback_relation m n) inferInstance

section Affine

variable [IsAffine E.U] [IsAffine E.R]

/-- The joint endpoint morphism of the symmetric cross-correspondence. -/
def tupleSymmetricCrossJoint :
    E.tupleSymmetricCrossScheme m n ⟶
      E.tupleSymmetricScheme m ⨯ E.tupleSymmetricScheme n :=
  prod.lift (E.tupleSymmetricCrossLeft m n) (E.tupleSymmetricCrossRight m n)

@[reassoc (attr := simp)]
theorem tupleSymmetricCrossJoint_fst :
    E.tupleSymmetricCrossJoint m n ≫ prod.fst = E.tupleSymmetricCrossLeft m n := by
  simp [tupleSymmetricCrossJoint]

@[reassoc (attr := simp)]
theorem tupleSymmetricCrossJoint_snd :
    E.tupleSymmetricCrossJoint m n ≫ prod.snd = E.tupleSymmetricCrossRight m n := by
  simp [tupleSymmetricCrossJoint]

/-- Quotienting both ordered tuples gives the cartesian square for the joint
endpoint morphism on symmetric cross-correspondences. -/
theorem tupleSymmetricCross_isPullback :
    IsPullback (prod.lift (E.tupleCrossLeft m n) (E.tupleCrossRight m n))
      (E.tupleSymmetricCrossMap m n)
      (prod.map (E.tupleSymmetricMap m) (E.tupleSymmetricMap n))
      (prod.lift (E.tupleSymmetricCrossLeft m n) (E.tupleSymmetricCrossRight m n)) := by
  let A := E.tupleCrossPermutationAction m n
  let B := (E.tuplePermutationAction m).product (E.tuplePermutationAction n)
  let f := prod.lift (E.tupleCrossLeft m n) (E.tupleCrossRight m n)
  have hf : ∀ g, (A.act g).hom ≫ f = f ≫ (B.act g).hom := by
    intro g
    apply prod.hom_ext <;>
      simp [A, B, f, tupleCrossPermutationAction, tupleCrossReindexIso,
        FiniteFreeSchemeAction.product, tuplePermutationAction]
  let Q := (E.tuplePermutationAction m).productQuotient (E.tuplePermutationAction n)
    (E.tupleSymmetricQuotient m) (E.tupleSymmetricQuotient n)
  have he : A.quotientMap B f hf (E.tupleCrossQuotient m n) Q =
      prod.lift (E.tupleSymmetricCrossLeft m n) (E.tupleSymmetricCrossRight m n) := by
    apply (E.tupleCrossQuotient m n).hom_ext
    rw [A.map_quotientMap B f hf]
    apply prod.hom_ext <;> simp [Q, f, FiniteFreeSchemeAction.productQuotient]
  have h := A.quotientMap_isPullback B f hf (E.tupleCrossQuotient m n) Q
  rw [he] at h
  exact h

instance tupleSymmetricCross_joint_isClosedImmersion
    [IsClosedImmersion (prod.lift E.t E.s)] :
    IsClosedImmersion
      (prod.lift (E.tupleSymmetricCrossLeft m n) (E.tupleSymmetricCrossRight m n)) := by
  let : IsAffine (E.tupleDistinctScheme m ⨯ E.tupleDistinctScheme n) :=
    IsAffine.of_isIso (prodIsoPullback _ _).hom
  let : IsAffine (E.tupleSymmetricScheme m ⨯ E.tupleSymmetricScheme n) :=
    IsAffine.of_isIso (prodIsoPullback _ _).hom
  let p := prod.map (E.tupleSymmetricMap m) (E.tupleSymmetricMap n)
  have : Flat p := schemeMorphismProperty_prod_map (@Flat) _ _ inferInstance inferInstance
  have : Surjective p :=
    schemeMorphismProperty_prod_map (@Surjective) _ _ inferInstance inferInstance
  exact isClosedImmersion_of_isPullback_of_affine_fpqc
    (E.tupleSymmetricCross_isPullback m n)

instance tupleSymmetricCrossJoint_isClosedImmersion
    [IsClosedImmersion (prod.lift E.t E.s)] :
    IsClosedImmersion (E.tupleSymmetricCrossJoint m n) := by
  dsimp [tupleSymmetricCrossJoint]
  infer_instance

end Affine

end EtaleEquivalenceRelation
end Langlands.AlgebraicGeometry
