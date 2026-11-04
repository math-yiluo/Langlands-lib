import Langlands.Representation.Plancherel.CompactSelfTwist
import Langlands.Representation.Plancherel.SmoothTensorFamilies
import Mathlib.LinearAlgebra.Pi

/-!
# Smooth families in the actual normalized product induction

Pointwise normalized restriction identifies dependent inducing fibers with the
fixed compact picture. The coefficient action is the actual self-twist action.
-/

noncomputable section

open Langlands.Aubert.General Langlands.Induction
open scoped TensorProduct NNReal

namespace Langlands.Plancherel

universe uG uI uV uJ

variable {G : Type uG} [Group G] [TopologicalSpace G] [NonarchimedeanGroup G]
  {M : Subgroup G} {I : Type uI} (ν : I → (M →* ℝ≥0ˣ))

/-- The literal inclusion of unitary unramified characters into all unramified
characters. It does not assert that every unramified character is unitary. -/
def unitaryUnramifiedInclusion :
    unitaryUnramifiedCharacters ν →* unramifiedCharacters ν :=
  Subgroup.inclusion inf_le_left

/-- The unitary part of the actual stabilizer of a canonical smooth class. -/
def unitaryClassTwistStabilizer
    (ω : SmoothDualClass.{0, uG, uV} (k := ℂ) (G := M)) :
    Subgroup (unitaryUnramifiedCharacters ν) :=
  (unramifiedTwistStabilizer ν ω).comap (unitaryUnramifiedInclusion ν)

/-- Inclusion into the full class stabilizer, retaining its actual membership
proof rather than assuming unitarity of the full stabilizer. -/
def unitaryClassStabilizerInclusion
    (ω : SmoothDualClass.{0, uG, uV} (k := ℂ) (G := M)) :
    unitaryClassTwistStabilizer ν ω →* unramifiedTwistStabilizer ν ω where
  toFun s := ⟨unitaryUnramifiedInclusion ν s.val, s.property⟩
  map_one' := rfl
  map_mul' _ _ := rfl

variable {J : Type uJ}
  (e : unitaryUnramifiedCharacters ν ≃* (J → Circle))

/-- The actual unramified character at a unitary torus coordinate. -/
def unitaryTorusParameter (z : J → Circle) : unramifiedCharacters ν :=
  unitaryUnramifiedInclusion ν (e.symm z)

/-- The stabilizer parameter homomorphism in the supplied torus coordinates. -/
def unitaryStabilizerTorusHom
    (ω : SmoothDualClass.{0, uG, uV} (k := ℂ) (G := M)) :
    unitaryClassTwistStabilizer ν ω →* (J → Circle) :=
  e.toMonoidHom.comp (unitaryClassTwistStabilizer ν ω).subtype

theorem unitaryTorusParameter_mul_stabilizer
    (ω : SmoothDualClass.{0, uG, uV} (k := ℂ) (G := M))
    (z : J → Circle) (s : unitaryClassTwistStabilizer ν ω) :
    unitaryTorusParameter ν e (z * unitaryStabilizerTorusHom ν e ω s) =
      unitaryTorusParameter ν e z * unitaryUnramifiedInclusion ν s.val := by
  change unitaryUnramifiedInclusion ν (e.symm (z * e s.val)) = _
  rw [map_mul, e.symm_apply_apply, map_mul]
  rfl

section ParameterTransport

variable (A : SmoothRep.{0, uG, uV} ℂ M)

/-- Twist an actual vector self-equivalence by another parameter. The final
action equality has identity vector map; the vector transport remains `a`. -/
def parameterSelfTwistEquiv (χ η : unramifiedCharacters ν)
    (a : A.representation.Equiv
      (A.twist η.val.toMonoidHom (unramifiedCharacter_isOpen_ker ν η)).representation) :
    (A.twist χ.val.toMonoidHom (unramifiedCharacter_isOpen_ker ν χ)).representation.Equiv
      (A.twist (χ * η).val.toMonoidHom
        (unramifiedCharacter_isOpen_ker ν (χ * η))).representation :=
  (twistEquiv χ.val.toMonoidHom a).trans
    (equivOfRepresentationEq (twist_twist χ.val.toMonoidHom η.val.toMonoidHom
      A.representation))

/-- Parameter transport on tensors is exactly the fixed self-twist operator
after removing the source and target smooth-dual twists. -/
theorem parameterSelfTwistEquiv_tensor (χ η : unramifiedCharacters ν)
    (a : A.representation.Equiv
      (A.twist η.val.toMonoidHom (unramifiedCharacter_isOpen_ker ν η)).representation)
    (t : CoefficientTensor
      (A.twist χ.val.toMonoidHom (unramifiedCharacter_isOpen_ker ν χ))) :
    productCompactTwistTensorEquiv ν (χ * η) A
        (coefficientTensorCongr (parameterSelfTwistEquiv ν A χ η a) t) =
      selfTwistTensorEquiv ν A η a (productCompactTwistTensorEquiv ν χ A t) := by
  induction t using TensorProduct.inductionOn with
  | tmul v ℓ => rfl
  | add t u ht hu => simp only [map_add, ht, hu]

end ParameterTransport

variable [LocallyCompactSpace G]
  {P U : Subgroup G} (h : IsSemidirectDecomposition P M U) (K : OpenSubgroup G)
  (hP : IsClosed (P : Set G)) (hK : IsCompact (K : Set G))
  (hν : ∀ i, Continuous (ν i)) (hr : Continuous h.projection)
  (hU : IsClosed (U : Set G))
  (hPK : ∀ g : G, ∃ p : P, ∃ k : K, g = (p : G) * (k : G))
  (A : SmoothRep.{0, uG, uV} ℂ M)

/-- Actual sections of the dependent normalized product-induction fibers. -/
abbrev ProductInducedTorusFamilies :=
  ∀ z : J → Circle, productInducedCoefficientObject h hU
    (A.twist (unitaryTorusParameter ν e z).val.toMonoidHom
      (unramifiedCharacter_isOpen_ker ν (unitaryTorusParameter ν e z)))

/-- Restrict each actual induced section to the compact product subgroup and
remove its smooth-dual twist, retaining the underlying functionals. -/
def productInducedFamilyRestriction :
    ProductInducedTorusFamilies ν e h hU A ≃ₗ[ℂ]
      ((J → Circle) → ProductInducedCompactPicture h K A) :=
  LinearEquiv.piCongrRight fun z =>
    (productInducedCompactEquiv ν h K hP hK hν hr hU hPK
      (unitaryTorusParameter ν e z) A).toLinearEquiv

@[simp]
theorem productInducedFamilyRestriction_eval
    (F : ProductInducedTorusFamilies ν e h hU A)
    (z : J → Circle) (k : K.prod K) :
    eval _ _ (productInducedFamilyRestriction ν e h K hP hK hν hr hU hPK A F z) k =
      productCompactTwistTensorEquiv ν (unitaryTorusParameter ν e z) A
        (eval _ _ (F z) k) := rfl

/-- The inverse uses the actual normalized extension on every fiber. -/
theorem productInducedFamilyRestriction_symm_mul
    (F : (J → Circle) → ProductInducedCompactPicture h K A)
    (z : J → Circle) (p : P.prod P) (k : K.prod K) :
    eval _ _
      ((productInducedFamilyRestriction ν e h K hP hK hν hr hU hPK A).symm F z)
      ((p : G × G) * (k : G × G)) =
      (inducingRepresentation (h.prod h) (hU.prod hU)
        (productLeviObject
          (A.twist (unitaryTorusParameter ν e z).val.toMonoidHom
            (unramifiedCharacter_isOpen_ker ν (unitaryTorusParameter ν e z)))
          (A.twist (unitaryTorusParameter ν e z).val.toMonoidHom
            (unramifiedCharacter_isOpen_ker ν (unitaryTorusParameter ν e z))).contragredient) p)
        ((productCompactTwistTensorEquiv ν (unitaryTorusParameter ν e z) A).symm
          (eval _ _ (F z) k)) :=
  productInducedCompactEquiv_symm_mul ν h K hP hK hν hr hU hPK
    (unitaryTorusParameter ν e z) A (F z) p k

/-- The actual transport of a parameter-twisted inducing representative
commutes with restriction to the fixed compact picture. -/
theorem productInducedParameterSelfTwist_restriction (χ η : unramifiedCharacters ν)
    (a : A.representation.Equiv
      (A.twist η.val.toMonoidHom (unramifiedCharacter_isOpen_ker ν η)).representation)
    (F : productInducedCoefficientObject h hU
      (A.twist χ.val.toMonoidHom (unramifiedCharacter_isOpen_ker ν χ))) :
    productInducedCompactEquiv ν h K hP hK hν hr hU hPK (χ * η) A
        (productInducedCoefficientTransport h hU
          (parameterSelfTwistEquiv ν A χ η a) F) =
      productCompactSelfTwistEquiv ν A h K hP hK hν hr η a
        (productInducedCompactEquiv ν h K hP hK hν hr hU hPK χ A F) := by
  apply Subtype.ext
  apply Subtype.ext
  funext k
  exact parameterSelfTwistEquiv_tensor ν A χ η a _

variable (π : IrreducibleAdmissibleRep.{0, uG, uV} (k := ℂ) (G := M))

/-- All actual inducing equivalences between two twists give the same
product-induced coefficient transport. Schur applies to the twisted inducing
object, whose admissibility and irreducibility are proved by twist invariance. -/
theorem productInducedTwistedTransport_independent (χ η : unramifiedCharacters ν)
    (a b :
      (π.obj.twist χ.val.toMonoidHom (unramifiedCharacter_isOpen_ker ν χ)).representation.Equiv
      (π.obj.twist η.val.toMonoidHom (unramifiedCharacter_isOpen_ker ν η)).representation) :
    productInducedCoefficientTransport h hU a = productInducedCoefficientTransport h hU b :=
  productInducedCoefficientTransport_independent h hU
    ((SmoothRep.isAdmissible_twist_iff χ.val.toMonoidHom
      (unramifiedCharacter_isOpen_ker ν χ) π.obj).mpr π.property.2)
    ((SmoothRep.isIrreducible_twist_iff χ.val.toMonoidHom
      (unramifiedCharacter_isOpen_ker ν χ) π.obj).mpr π.property.1) a b

/-- The genuine coefficient action of the unitary class stabilizer. -/
def unitaryStabilizerCompactRepresentation :
    Representation ℂ (unitaryClassTwistStabilizer ν (Quotient.mk _ π))
      (ProductInducedCompactPicture h K π.obj) :=
  (unramifiedStabilizerCompactRepresentation ν π h K hP hK hν hr).comp
    (unitaryClassStabilizerInclusion ν (Quotient.mk _ π))

/-- Canonical self-twist transport from a parameter fiber to the fiber at the
stabilizer translate. The lift is chosen from actual equality of smooth classes. -/
def unitaryTorusFiberEquiv
    (s : unitaryClassTwistStabilizer ν (Quotient.mk _ π)) (z : J → Circle) :
    (π.obj.twist (unitaryTorusParameter ν e z).val.toMonoidHom
      (unramifiedCharacter_isOpen_ker ν (unitaryTorusParameter ν e z))).representation.Equiv
    (π.obj.twist
      (unitaryTorusParameter ν e (z * unitaryStabilizerTorusHom ν e (Quotient.mk _ π) s)).val.toMonoidHom
      (unramifiedCharacter_isOpen_ker ν
        (unitaryTorusParameter ν e (z * unitaryStabilizerTorusHom ν e (Quotient.mk _ π) s)))).representation :=
  (parameterSelfTwistEquiv ν π.obj (unitaryTorusParameter ν e z)
    (unitaryUnramifiedInclusion ν s.val)
    (stabilizerRepresentationEquiv ν π
      (unitaryClassStabilizerInclusion ν (Quotient.mk _ π) s))).trans
    (equivOfRepresentationEq (by
      change twist
        ((unitaryTorusParameter ν e z * unitaryUnramifiedInclusion ν s.val).val.toMonoidHom)
        π.obj.representation = _
      rw [← unitaryTorusParameter_mul_stabilizer ν e (Quotient.mk _ π) z s]))

omit [LocallyCompactSpace G] in
/-- The torus-coordinate equality changes only the representation action, so
the underlying tensor transport remains vector and inverse-functional transport. -/
theorem unitaryTorusFiberEquiv_tensor
    (s : unitaryClassTwistStabilizer ν (Quotient.mk _ π)) (z : J → Circle)
    (t : CoefficientTensor
      (π.obj.twist (unitaryTorusParameter ν e z).val.toMonoidHom
        (unramifiedCharacter_isOpen_ker ν (unitaryTorusParameter ν e z)))) :
    productCompactTwistTensorEquiv ν
        (unitaryTorusParameter ν e (z * unitaryStabilizerTorusHom ν e (Quotient.mk _ π) s)) π.obj
        (coefficientTensorCongr (unitaryTorusFiberEquiv ν e π s z) t) =
      selfTwistTensorEquiv ν π.obj (unitaryUnramifiedInclusion ν s.val)
        (stabilizerRepresentationEquiv ν π
          (unitaryClassStabilizerInclusion ν (Quotient.mk _ π) s))
        (productCompactTwistTensorEquiv ν (unitaryTorusParameter ν e z) π.obj t) := by
  induction t using TensorProduct.inductionOn with
  | tmul v ℓ => rfl
  | add t u ht hu => simp only [map_add, ht, hu]

/-- Actual normalized product-induced transport between the two dependent
fibers, including inverse pullback of every smooth functional. -/
def unitaryTorusInducedFiberEquiv
    (s : unitaryClassTwistStabilizer ν (Quotient.mk _ π)) (z : J → Circle) :
    (productInducedCoefficientObject h hU
      (π.obj.twist (unitaryTorusParameter ν e z).val.toMonoidHom
        (unramifiedCharacter_isOpen_ker ν (unitaryTorusParameter ν e z)))).representation.Equiv
    (productInducedCoefficientObject h hU
      (π.obj.twist
        (unitaryTorusParameter ν e (z * unitaryStabilizerTorusHom ν e (Quotient.mk _ π) s)).val.toMonoidHom
        (unramifiedCharacter_isOpen_ker ν
          (unitaryTorusParameter ν e (z * unitaryStabilizerTorusHom ν e (Quotient.mk _ π) s))))).representation :=
  productInducedCoefficientTransport h hU (unitaryTorusFiberEquiv ν e π s z)

/-- The chosen class lift can be replaced by any actual equivalence between
the parameter fibers. No coherence assumption on those choices is needed. -/
theorem unitaryTorusInducedFiberEquiv_eq_transport
    (s : unitaryClassTwistStabilizer ν (Quotient.mk _ π)) (z : J → Circle)
    (a :
      (π.obj.twist (unitaryTorusParameter ν e z).val.toMonoidHom
        (unramifiedCharacter_isOpen_ker ν (unitaryTorusParameter ν e z))).representation.Equiv
      (π.obj.twist
        (unitaryTorusParameter ν e (z * unitaryStabilizerTorusHom ν e (Quotient.mk _ π) s)).val.toMonoidHom
        (unramifiedCharacter_isOpen_ker ν
          (unitaryTorusParameter ν e (z * unitaryStabilizerTorusHom ν e (Quotient.mk _ π) s)))).representation) :
    unitaryTorusInducedFiberEquiv ν e h hU π s z =
      productInducedCoefficientTransport h hU a :=
  productInducedTwistedTransport_independent ν h hU π
    (unitaryTorusParameter ν e z)
    (unitaryTorusParameter ν e (z * unitaryStabilizerTorusHom ν e (Quotient.mk _ π) s))
    (unitaryTorusFiberEquiv ν e π s z) a

/-- The canonical dependent-fiber transport is the genuine compact coefficient
action under the actual normalized restriction equivalences. -/
theorem unitaryTorusInducedFiberEquiv_restriction
    (s : unitaryClassTwistStabilizer ν (Quotient.mk _ π)) (z : J → Circle)
    (F : productInducedCoefficientObject h hU
      (π.obj.twist (unitaryTorusParameter ν e z).val.toMonoidHom
        (unramifiedCharacter_isOpen_ker ν (unitaryTorusParameter ν e z)))) :
    productInducedCompactEquiv ν h K hP hK hν hr hU hPK
        (unitaryTorusParameter ν e (z * unitaryStabilizerTorusHom ν e (Quotient.mk _ π) s)) π.obj
        (unitaryTorusInducedFiberEquiv ν e h hU π s z F) =
      unitaryStabilizerCompactRepresentation ν h K hP hK hν hr π s
        (productInducedCompactEquiv ν h K hP hK hν hr hU hPK
          (unitaryTorusParameter ν e z) π.obj F) := by
  apply Subtype.ext
  apply Subtype.ext
  funext k
  exact unitaryTorusFiberEquiv_tensor ν e π s z _

variable [Fintype J]

local instance productSmoothTensorAddCommGroup :
    AddCommGroup
      (smoothFiniteTorusFunctions J ⊗[ℂ] ProductInducedCompactPicture h K π.obj) :=
  TensorProduct.addCommGroup

/-- Smooth actual induced families: finite scalar-smooth compact families
satisfying the canonical coefficient covariance, pulled back by restriction. -/
def productInducedSmoothFamilies :
    Submodule ℂ (ProductInducedTorusFamilies ν e h hU π.obj) :=
  (finiteSmoothEquivariantFamilies J (ProductInducedCompactPicture h K π.obj)
    (unitaryStabilizerTorusHom ν e (Quotient.mk _ π))
    (unitaryStabilizerCompactRepresentation ν h K hP hK hν hr π)).comap
      (productInducedFamilyRestriction ν e h K hP hK hν hr hU hPK π.obj).toLinearMap

/-- Membership is finite scalar smoothness of actual compact restrictions
together with equality under the actual canonical induced-fiber transports. -/
theorem mem_productInducedSmoothFamilies_iff
    (F : ProductInducedTorusFamilies ν e h hU π.obj) :
    F ∈ productInducedSmoothFamilies ν e h K hP hK hν hr hU hPK π ↔
      productInducedFamilyRestriction ν e h K hP hK hν hr hU hPK π.obj F ∈
        finiteSmoothFamilies J (ProductInducedCompactPicture h K π.obj) ∧
      ∀ (s : unitaryClassTwistStabilizer ν (Quotient.mk _ π)) (z : J → Circle),
        F (z * unitaryStabilizerTorusHom ν e (Quotient.mk _ π) s) =
          unitaryTorusInducedFiberEquiv ν e h hU π s z (F z) := by
  constructor
  · intro hF
    refine ⟨hF.1, fun s z => ?_⟩
    apply (productInducedCompactEquiv ν h K hP hK hν hr hU hPK
      (unitaryTorusParameter ν e (z * unitaryStabilizerTorusHom ν e (Quotient.mk _ π) s)) π.obj).injective
    exact (hF.2 s z).trans
      (unitaryTorusInducedFiberEquiv_restriction ν e h K hP hK hν hr hU hPK π s z
        (F z)).symm
  · rintro ⟨hF, hcov⟩
    refine ⟨hF, fun s z => ?_⟩
    exact (congrArg
      (productInducedCompactEquiv ν h K hP hK hν hr hU hPK
        (unitaryTorusParameter ν e (z * unitaryStabilizerTorusHom ν e (Quotient.mk _ π) s)) π.obj)
      (hcov s z)).trans
        (unitaryTorusInducedFiberEquiv_restriction ν e h K hP hK hν hr hU hPK π s z
          (F z))

/-- The tensor action uses inverse torus translation together with actual
vector and inverse-functional self-twist transport on the compact sections. -/
abbrev productInducedSmoothTensorRepresentation :=
  smoothTensorRepresentation J (ProductInducedCompactPicture h K π.obj)
    (unitaryStabilizerTorusHom ν e (Quotient.mk _ π))
    (unitaryStabilizerCompactRepresentation ν h K hP hK hν hr π)

/-- Diagonal invariant tensors are exactly these actual normalized
product-induced families, via evaluation followed by normalized extension. -/
def productInducedSmoothTensorFamilyEquiv :
    (productInducedSmoothTensorRepresentation ν e h K hP hK hν hr π).invariants ≃ₗ[ℂ]
      productInducedSmoothFamilies ν e h K hP hK hν hr hU hPK π :=
  (smoothTensorInvariantFamilyEquiv J (ProductInducedCompactPicture h K π.obj)
    (unitaryStabilizerTorusHom ν e (Quotient.mk _ π))
    (unitaryStabilizerCompactRepresentation ν h K hP hK hν hr π)).trans
      ((productInducedFamilyRestriction ν e h K hP hK hν hr hU hPK π.obj).ofSubmodule'
        (finiteSmoothEquivariantFamilies J (ProductInducedCompactPicture h K π.obj)
          (unitaryStabilizerTorusHom ν e (Quotient.mk _ π))
          (unitaryStabilizerCompactRepresentation ν h K hP hK hν hr π))).symm

@[simp]
theorem productInducedSmoothTensorFamilyEquiv_restriction
    (t : (productInducedSmoothTensorRepresentation ν e h K hP hK hν hr π).invariants)
    (z : J → Circle) :
    productInducedFamilyRestriction ν e h K hP hK hν hr hU hPK π.obj
      (productInducedSmoothTensorFamilyEquiv ν e h K hP hK hν hr hU hPK π t).val z =
      smoothTensorEvaluation J (ProductInducedCompactPicture h K π.obj) t.val z := by
  change productInducedFamilyRestriction ν e h K hP hK hν hr hU hPK π.obj
    ((productInducedFamilyRestriction ν e h K hP hK hν hr hU hPK π.obj).symm
      ((smoothTensorInvariantFamilyEquiv J (ProductInducedCompactPicture h K π.obj)
        (unitaryStabilizerTorusHom ν e (Quotient.mk _ π))
        (unitaryStabilizerCompactRepresentation ν h K hP hK hν hr π) t).val)) z = _
  rw [LinearEquiv.apply_symm_apply]
  rfl

/-- The family produced by an invariant tensor is the actual normalized
extension of its compact tensor evaluation on every parameter fiber. -/
theorem productInducedSmoothTensorFamilyEquiv_eval_mul
    (t : (productInducedSmoothTensorRepresentation ν e h K hP hK hν hr π).invariants)
    (z : J → Circle) (p : P.prod P) (k : K.prod K) :
    eval _ _
      ((productInducedSmoothTensorFamilyEquiv ν e h K hP hK hν hr hU hPK π t).val z)
      ((p : G × G) * (k : G × G)) =
      (inducingRepresentation (h.prod h) (hU.prod hU)
        (productLeviObject
          (π.obj.twist (unitaryTorusParameter ν e z).val.toMonoidHom
            (unramifiedCharacter_isOpen_ker ν (unitaryTorusParameter ν e z)))
          (π.obj.twist (unitaryTorusParameter ν e z).val.toMonoidHom
            (unramifiedCharacter_isOpen_ker ν (unitaryTorusParameter ν e z))).contragredient) p)
        ((productCompactTwistTensorEquiv ν (unitaryTorusParameter ν e z) π.obj).symm
          (eval _ _ (smoothTensorEvaluation J (ProductInducedCompactPicture h K π.obj)
            t.val z) k)) :=
  productInducedFamilyRestriction_symm_mul ν e h K hP hK hν hr hU hPK π.obj
    (smoothTensorEvaluation J (ProductInducedCompactPicture h K π.obj) t.val) z p k

@[simp]
theorem productInducedSmoothTensorFamilyEquiv_symm_evaluation
    (F : productInducedSmoothFamilies ν e h K hP hK hν hr hU hPK π)
    (z : J → Circle) :
    smoothTensorEvaluation J (ProductInducedCompactPicture h K π.obj)
      ((productInducedSmoothTensorFamilyEquiv ν e h K hP hK hν hr hU hPK π).symm F).val z =
      productInducedFamilyRestriction ν e h K hP hK hν hr hU hPK π.obj F.val z := by
  simpa only [LinearEquiv.apply_symm_apply] using
    (productInducedSmoothTensorFamilyEquiv_restriction ν e h K hP hK hν hr hU hPK π
      ((productInducedSmoothTensorFamilyEquiv ν e h K hP hK hν hr hU hPK π).symm F) z).symm

end Langlands.Plancherel
