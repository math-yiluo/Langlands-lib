import Langlands.Representation.Plancherel.ProductCompactPicture

/-! # Change of base object in the actual compact coefficient picture -/

noncomputable section

open Langlands.Aubert.General Langlands.Induction
open scoped TensorProduct NNReal

namespace Langlands.Plancherel

universe uG uI uV uW

variable {G : Type uG} [Group G] [TopologicalSpace G] [NonarchimedeanGroup G]
  {M : Subgroup G} {I : Type uI} (ν : I → (M →* ℝ≥0ˣ))
  {A : SmoothRep.{0, uG, uV} ℂ M} {B : SmoothRep.{0, uG, uW} ℂ M}

/-- An equivalence from the fixed twist to a new base object, twisted by a
variable parameter. Its vector map is still the original equivalence. -/
def productBaseTwistEquiv (χ η : unramifiedCharacters ν)
    (a : (A.twist χ.val.toMonoidHom
      (unramifiedCharacter_isOpen_ker ν χ)).representation.Equiv B.representation) :
    (A.twist (η * χ).val.toMonoidHom
      (unramifiedCharacter_isOpen_ker ν (η * χ))).representation.Equiv
      (B.twist η.val.toMonoidHom
        (unramifiedCharacter_isOpen_ker ν η)).representation :=
  (equivOfRepresentationEq
    (twist_twist η.val.toMonoidHom χ.val.toMonoidHom A.representation)).symm.trans
      (twistEquiv η.val.toMonoidHom a)

/-- Removing the variable smooth-dual twist gives one fixed coefficient
map: restore the fixed twist, then transport vectors and inverse functionals. -/
theorem productBaseTwistEquiv_tensor (χ η : unramifiedCharacters ν)
    (a : (A.twist χ.val.toMonoidHom
      (unramifiedCharacter_isOpen_ker ν χ)).representation.Equiv B.representation)
    (t : CoefficientTensor (A.twist (η * χ).val.toMonoidHom
      (unramifiedCharacter_isOpen_ker ν (η * χ)))) :
    productCompactTwistTensorEquiv ν η B
        (coefficientTensorCongr (productBaseTwistEquiv ν χ η a) t) =
      coefficientTensorCongr a
        ((productCompactTwistTensorEquiv ν χ A).symm
          (productCompactTwistTensorEquiv ν (η * χ) A t)) := by
  induction t using TensorProduct.inductionOn with
  | tmul v ℓ => rfl
  | add t s ht hs => simp only [map_add, ht, hs]

variable [LocallyCompactSpace G]
  {P U : Subgroup G} (h : IsSemidirectDecomposition P M U) (K : OpenSubgroup G)
  (hP : IsClosed (P : Set G)) (hK : IsCompact (K : Set G))
  (hν : ∀ i, Continuous (ν i)) (hr : Continuous h.projection)

/-- A fixed compact coefficient equivalence for a new base object. The
inverse twist-removal map is followed by actual representative transport. -/
def productCompactBaseChangeEquiv (χ : unramifiedCharacters ν)
    (a : (A.twist χ.val.toMonoidHom
      (unramifiedCharacter_isOpen_ker ν χ)).representation.Equiv B.representation) :
    (productInducedCompactRepresentation h K A).Equiv
      (productInducedCompactRepresentation h K B) :=
  (smoothInducedEquiv _
    (productCompactTwistInducingEquiv ν h K hP hK hν hr χ A)).symm.trans
      (productCompactRepresentativeEquiv h K a)

omit [LocallyCompactSpace G] in
/-- The fixed compact comparison retains inverse pullback on every smooth
functional; it is pointwise on actual compact induced functions. -/
@[simp]
theorem productCompactBaseChangeEquiv_eval (χ : unramifiedCharacters ν)
    (a : (A.twist χ.val.toMonoidHom
      (unramifiedCharacter_isOpen_ker ν χ)).representation.Equiv B.representation)
    (F : ProductInducedCompactPicture h K A) (k : K.prod K) :
    eval _ _ (productCompactBaseChangeEquiv ν h K hP hK hν hr χ a F) k =
      coefficientTensorCongr a
        ((productCompactTwistTensorEquiv ν χ A).symm (eval _ _ F k)) := rfl

omit [LocallyCompactSpace G] in
/-- For a fixed character, admissible Schur on the inducing object removes
the choice of actual equivalence to the new base. -/
theorem productCompactBaseChangeEquiv_independent
    (hA : A.IsAdmissible) (hi : A.representation.IsIrreducible)
    (χ : unramifiedCharacters ν)
    (a b : (A.twist χ.val.toMonoidHom
      (unramifiedCharacter_isOpen_ker ν χ)).representation.Equiv B.representation) :
    productCompactBaseChangeEquiv ν h K hP hK hν hr χ a =
      productCompactBaseChangeEquiv ν h K hP hK hν hr χ b := by
  have hab := coefficientTensorCongr_eq_of_admissible
    ((SmoothRep.isAdmissible_twist_iff χ.val.toMonoidHom
      (unramifiedCharacter_isOpen_ker ν χ) A).mpr hA)
    ((SmoothRep.isIrreducible_twist_iff χ.val.toMonoidHom
      (unramifiedCharacter_isOpen_ker ν χ) A).mpr hi) a b
  apply Representation.Equiv.ext
  funext F
  apply Subtype.ext
  apply Subtype.ext
  funext k
  exact congrArg (fun T : CoefficientTensor
      (A.twist χ.val.toMonoidHom (unramifiedCharacter_isOpen_ker ν χ)) ≃ₗ[ℂ]
        CoefficientTensor B => T _) hab

variable (hU : IsClosed (U : Set G))
  (hPK : ∀ g : G, ∃ p : P, ∃ k : K, g = (p : G) * (k : G))

/-- The actual normalized restriction square for a change of base. Variable
parameters are translated by the fixed character; the compact map is fixed. -/
theorem productInducedCompactBaseChange (χ η : unramifiedCharacters ν)
    (a : (A.twist χ.val.toMonoidHom
      (unramifiedCharacter_isOpen_ker ν χ)).representation.Equiv B.representation)
    (F : productInducedCoefficientObject h hU
      (A.twist (η * χ).val.toMonoidHom
        (unramifiedCharacter_isOpen_ker ν (η * χ)))) :
    productInducedCompactEquiv ν h K hP hK hν hr hU hPK η B
        (productInducedCoefficientTransport h hU (productBaseTwistEquiv ν χ η a) F) =
      productCompactBaseChangeEquiv ν h K hP hK hν hr χ a
        (productInducedCompactEquiv ν h K hP hK hν hr hU hPK (η * χ) A F) := by
  apply Subtype.ext
  apply Subtype.ext
  funext k
  exact productBaseTwistEquiv_tensor ν χ η a _

end Langlands.Plancherel
