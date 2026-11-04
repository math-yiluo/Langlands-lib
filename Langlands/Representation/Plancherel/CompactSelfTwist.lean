import Langlands.Representation.Plancherel.ProductCompactPicture
import Langlands.Representation.Plancherel.DiscreteSeriesOrbits

/-!
# The actual self-twist action on the compact coefficient picture

Vector transport tensored with inverse functional pullback gives the
stabilizer action. Schur is used on the inducing representation only.
-/

noncomputable section

open CategoryTheory Langlands.Aubert.General Langlands.Induction
open scoped TensorProduct NNReal

namespace Langlands.Plancherel

universe uG uI uV

variable {G : Type uG} [Group G] [TopologicalSpace G] [NonarchimedeanGroup G]
  {M : Subgroup G} {I : Type uI} (ν : I → (M →* ℝ≥0ˣ))
  (A : SmoothRep.{0, uG, uV} ℂ M)

/-- The underlying coefficient-tensor automorphism of an actual self-twist.
The functional is pulled back by the inverse vector equivalence. -/
def selfTwistTensorEquiv (χ : unramifiedCharacters ν)
    (e : A.representation.Equiv
      (A.twist χ.val.toMonoidHom (unramifiedCharacter_isOpen_ker ν χ)).representation) :
    CoefficientTensor A ≃ₗ[ℂ] CoefficientTensor A :=
  (coefficientTensorCongr e).trans (productCompactTwistTensorEquiv ν χ A)

@[simp]
theorem selfTwistTensorEquiv_tmul (χ : unramifiedCharacters ν)
    (e : A.representation.Equiv
      (A.twist χ.val.toMonoidHom (unramifiedCharacter_isOpen_ker ν χ)).representation)
    (v : A) (ℓ : SmoothDual A.representation) :
    selfTwistTensorEquiv ν A χ e (v ⊗ₜ[ℂ] ℓ) =
      e v ⊗ₜ[ℂ] smoothContragredientTwistEquiv χ.val.toMonoidHom A.representation
        (unramifiedCharacter_isOpen_ker ν χ)
        (contragredientMap e.symm.toIntertwiningMap ℓ) := rfl

/-- This is the inverse-transpose formula on actual underlying functionals. -/
theorem selfTwistTensorEquiv_dual_apply (χ : unramifiedCharacters ν)
    (e : A.representation.Equiv
      (A.twist χ.val.toMonoidHom (unramifiedCharacter_isOpen_ker ν χ)).representation)
    (ℓ : SmoothDual A.representation) (v : A) :
    (smoothContragredientTwistEquiv χ.val.toMonoidHom A.representation
      (unramifiedCharacter_isOpen_ker ν χ)
      (contragredientMap e.symm.toIntertwiningMap ℓ)).val v = ℓ.val (e.symm v) := rfl

theorem selfTwistTensorEquiv_pairing (χ : unramifiedCharacters ν)
    (e : A.representation.Equiv
      (A.twist χ.val.toMonoidHom (unramifiedCharacter_isOpen_ker ν χ)).representation)
    (t : CoefficientTensor A) :
    TensorProduct.lift (smoothDualPairing A.representation).flip
        (selfTwistTensorEquiv ν A χ e t) =
      TensorProduct.lift (smoothDualPairing A.representation).flip t := by
  exact (productCompactTwistTensorEquiv_pairing ν χ A _).trans
    (productCoefficientLeviEquiv_pairing e t)

/-- Independence is proved using admissible Schur on the inducing source. -/
theorem selfTwistTensorEquiv_independent (hA : A.IsAdmissible)
    (hi : A.representation.IsIrreducible) (χ : unramifiedCharacters ν)
    (e f : A.representation.Equiv
      (A.twist χ.val.toMonoidHom (unramifiedCharacter_isOpen_ker ν χ)).representation) :
    selfTwistTensorEquiv ν A χ e = selfTwistTensorEquiv ν A χ f := by
  unfold selfTwistTensorEquiv
  rw [coefficientTensorCongr_eq_of_admissible hA hi e f]

/-- An explicit lift of the product character, ordered so the tensor maps
compose as a left group action. Its underlying map is `eχ ∘ eη`. -/
def selfTwistComposite (χ η : unramifiedCharacters ν)
    (eχ : A.representation.Equiv
      (A.twist χ.val.toMonoidHom (unramifiedCharacter_isOpen_ker ν χ)).representation)
    (eη : A.representation.Equiv
      (A.twist η.val.toMonoidHom (unramifiedCharacter_isOpen_ker ν η)).representation) :
    A.representation.Equiv
      (A.twist (χ * η).val.toMonoidHom
        (unramifiedCharacter_isOpen_ker ν (χ * η))).representation :=
  (eη.trans (twistEquiv η.val.toMonoidHom eχ)).trans
    (equivOfRepresentationEq (by
      change twist η.val.toMonoidHom (twist χ.val.toMonoidHom A.representation) =
        twist (χ.val.toMonoidHom * η.val.toMonoidHom) A.representation
      rw [twist_twist]
      congr 1
      exact MonoidHom.ext (fun m => mul_comm _ _)))

theorem selfTwistTensorEquiv_composite (χ η : unramifiedCharacters ν)
    (eχ : A.representation.Equiv
      (A.twist χ.val.toMonoidHom (unramifiedCharacter_isOpen_ker ν χ)).representation)
    (eη : A.representation.Equiv
      (A.twist η.val.toMonoidHom (unramifiedCharacter_isOpen_ker ν η)).representation)
    (t : CoefficientTensor A) :
    selfTwistTensorEquiv ν A (χ * η) (selfTwistComposite ν A χ η eχ eη) t =
      selfTwistTensorEquiv ν A χ eχ (selfTwistTensorEquiv ν A η eη t) := by
  induction t using TensorProduct.inductionOn with
  | tmul v ℓ => rfl
  | add t s ht hs => simp only [map_add, ht, hs]

/-- The identity lift of the trivial character uses the proved equality of
actions, with the identity underlying linear map. -/
def selfTwistOneEquiv :
    A.representation.Equiv
      (A.twist (1 : unramifiedCharacters ν).val.toMonoidHom
        (unramifiedCharacter_isOpen_ker ν 1)).representation :=
  equivOfRepresentationEq (twist_one A.representation).symm

@[simp]
theorem selfTwistTensorEquiv_one (t : CoefficientTensor A) :
    selfTwistTensorEquiv ν A 1 (selfTwistOneEquiv ν A) t = t := by
  induction t using TensorProduct.inductionOn with
  | tmul v ℓ => rfl
  | add t s ht hs => simp only [map_add, ht, hs]

variable (π : IrreducibleAdmissibleRep.{0, uG, uV} (k := ℂ) (G := M))

/-- A lift is chosen from actual equality of canonical smooth-dual classes.
It is subsequently removed from the tensor and compact actions by Schur. -/
def stabilizerRepresentationEquiv
    (χ : unramifiedTwistStabilizer ν (Quotient.mk _ π)) :
    π.obj.representation.Equiv
      (π.obj.twist χ.val.val.toMonoidHom
        (unramifiedCharacter_isOpen_ker ν χ.val)).representation := by
  have hχ : Quotient.mk _
      (IrreducibleAdmissibleRep.twist χ.val.val.toMonoidHom
        (unramifiedCharacter_isOpen_ker ν χ.val) π) = Quotient.mk _ π :=
    χ.property
  let e := Classical.choice (Quotient.exact hχ)
  exact SmoothRep.equivOfIso
    ((irreducibleAdmissibleProperty (k := ℂ) (G := M)).ι.mapIso e.symm)

/-- The actual full unramified stabilizer acts linearly on the coefficient
tensor. The chosen vector lifts are not assumed to satisfy a cocycle law. -/
def unramifiedStabilizerTensorRepresentation :
    Representation ℂ (unramifiedTwistStabilizer ν (Quotient.mk _ π))
      (CoefficientTensor π.obj) where
  toFun χ := (selfTwistTensorEquiv ν π.obj χ.val
    (stabilizerRepresentationEquiv ν π χ)).toLinearMap
  map_one' := by
    apply LinearMap.ext
    intro t
    change selfTwistTensorEquiv ν π.obj 1
      (stabilizerRepresentationEquiv ν π 1) t = t
    rw [selfTwistTensorEquiv_independent ν π.obj π.property.2 π.property.1 1
      (stabilizerRepresentationEquiv ν π 1) (selfTwistOneEquiv ν π.obj)]
    exact selfTwistTensorEquiv_one ν π.obj t
  map_mul' χ η := by
    apply LinearMap.ext
    intro t
    change selfTwistTensorEquiv ν π.obj (χ.val * η.val)
      (stabilizerRepresentationEquiv ν π (χ * η)) t =
        selfTwistTensorEquiv ν π.obj χ.val (stabilizerRepresentationEquiv ν π χ)
          (selfTwistTensorEquiv ν π.obj η.val (stabilizerRepresentationEquiv ν π η) t)
    exact (DFunLike.congr_fun
      (selfTwistTensorEquiv_independent ν π.obj π.property.2 π.property.1 (χ.val * η.val)
        (stabilizerRepresentationEquiv ν π (χ * η))
        (selfTwistComposite ν π.obj χ.val η.val
          (stabilizerRepresentationEquiv ν π χ) (stabilizerRepresentationEquiv ν π η)))
      t).trans (selfTwistTensorEquiv_composite ν π.obj χ.val η.val _ _ t)

section Compact

variable {P U : Subgroup G}
  (h : IsSemidirectDecomposition P M U) (K : OpenSubgroup G)
  (hP : IsClosed (P : Set G)) (hK : IsCompact (K : Set G))
  (hν : ∀ i, Continuous (ν i)) (hr : Continuous h.projection)

/-- The actual compact-section automorphism from a self-twist equivalence.
It is obtained by coefficient transport and functional-preserving twist removal. -/
def productCompactSelfTwistEquiv (χ : unramifiedCharacters ν)
    (e : A.representation.Equiv
      (A.twist χ.val.toMonoidHom (unramifiedCharacter_isOpen_ker ν χ)).representation) :
    (productInducedCompactRepresentation h K A).Equiv
      (productInducedCompactRepresentation h K A) :=
  (productCompactRepresentativeEquiv h K e).trans
    (smoothInducedEquiv _ (productCompactTwistInducingEquiv ν h K hP hK hν hr χ A))

@[simp]
theorem productCompactSelfTwistEquiv_eval (χ : unramifiedCharacters ν)
    (e : A.representation.Equiv
      (A.twist χ.val.toMonoidHom (unramifiedCharacter_isOpen_ker ν χ)).representation)
    (F : ProductInducedCompactPicture h K A) (k : K.prod K) :
    eval _ _ (productCompactSelfTwistEquiv ν A h K hP hK hν hr χ e F) k =
      selfTwistTensorEquiv ν A χ e (eval _ _ F k) := rfl

theorem productCompactSelfTwistEquiv_independent (hA : A.IsAdmissible)
    (hi : A.representation.IsIrreducible) (χ : unramifiedCharacters ν)
    (e f : A.representation.Equiv
      (A.twist χ.val.toMonoidHom (unramifiedCharacter_isOpen_ker ν χ)).representation) :
    productCompactSelfTwistEquiv ν A h K hP hK hν hr χ e =
      productCompactSelfTwistEquiv ν A h K hP hK hν hr χ f := by
  apply Representation.Equiv.ext
  funext F
  apply Subtype.ext
  apply Subtype.ext
  funext k
  change selfTwistTensorEquiv ν A χ e _ = selfTwistTensorEquiv ν A χ f _
  rw [selfTwistTensorEquiv_independent ν A hA hi χ e f]

/-- A genuine representation of the actual stabilizer on the fixed compact
picture. No irreducibility of parabolic induction is used. -/
def unramifiedStabilizerCompactRepresentation :
    Representation ℂ (unramifiedTwistStabilizer ν (Quotient.mk _ π))
      (ProductInducedCompactPicture h K π.obj) where
  toFun χ := (productCompactSelfTwistEquiv ν π.obj h K hP hK hν hr χ.val
    (stabilizerRepresentationEquiv ν π χ)).toLinearMap
  map_one' := by
    apply LinearMap.ext
    intro F
    apply Subtype.ext
    apply Subtype.ext
    funext k
    change selfTwistTensorEquiv ν π.obj 1 (stabilizerRepresentationEquiv ν π 1)
      (F.val.val k) = F.val.val k
    exact (DFunLike.congr_fun
      (selfTwistTensorEquiv_independent ν π.obj π.property.2 π.property.1 1
        (stabilizerRepresentationEquiv ν π 1) (selfTwistOneEquiv ν π.obj))
      (F.val.val k)).trans (selfTwistTensorEquiv_one ν π.obj _)
  map_mul' χ η := by
    apply LinearMap.ext
    intro F
    apply Subtype.ext
    apply Subtype.ext
    funext k
    change selfTwistTensorEquiv ν π.obj (χ.val * η.val)
      (stabilizerRepresentationEquiv ν π (χ * η)) (F.val.val k) =
        selfTwistTensorEquiv ν π.obj χ.val (stabilizerRepresentationEquiv ν π χ)
          (selfTwistTensorEquiv ν π.obj η.val (stabilizerRepresentationEquiv ν π η)
            (F.val.val k))
    exact (DFunLike.congr_fun
      (selfTwistTensorEquiv_independent ν π.obj π.property.2 π.property.1 (χ.val * η.val)
        (stabilizerRepresentationEquiv ν π (χ * η))
        (selfTwistComposite ν π.obj χ.val η.val
          (stabilizerRepresentationEquiv ν π χ) (stabilizerRepresentationEquiv ν π η)))
      (F.val.val k)).trans (selfTwistTensorEquiv_composite ν π.obj χ.val η.val _ _ _)

/-- The canonical stabilizer operator commutes with the actual right compact
product-group action. -/
theorem unramifiedStabilizerCompactRepresentation_action
    (χ : unramifiedTwistStabilizer ν (Quotient.mk _ π))
    (k : K.prod K) (F : ProductInducedCompactPicture h K π.obj) :
    unramifiedStabilizerCompactRepresentation ν π h K hP hK hν hr χ
        (productInducedCompactRepresentation h K π.obj k F) =
      productInducedCompactRepresentation h K π.obj k
        (unramifiedStabilizerCompactRepresentation ν π h K hP hK hν hr χ F) :=
  congrArg (fun T => T F)
    ((productCompactSelfTwistEquiv ν π.obj h K hP hK hν hr χ.val
      (stabilizerRepresentationEquiv ν π χ)).isIntertwining' k)

variable [LocallyCompactSpace G] (hU : IsClosed (U : Set G))
  (hPK : ∀ g : G, ∃ p : P, ∃ k : K, g = (p : G) * (k : G))

/-- This is Waldspurger's self-twist square, on actual product-induced
functions with their actual normalized restriction maps. -/
theorem productCompactSelfTwistEquiv_restriction (χ : unramifiedCharacters ν)
    (e : A.representation.Equiv
      (A.twist χ.val.toMonoidHom (unramifiedCharacter_isOpen_ker ν χ)).representation)
    (F : productInducedCoefficientObject h hU A) :
    productInducedCompactEquiv ν h K hP hK hν hr hU hPK χ A
        (productInducedCoefficientTransport h hU e F) =
      productCompactSelfTwistEquiv ν A h K hP hK hν hr χ e
        (normalizedInductionCompactEquiv (h.prod h) (K.prod K) (hU.prod hU)
          (hP.prod hP) (hK.prod hK) (product_compact_factorization K hPK)
          (productLeviObject A A.contragredient) F) := by
  apply Subtype.ext
  apply Subtype.ext
  funext k
  rfl

end Compact

end Langlands.Plancherel
