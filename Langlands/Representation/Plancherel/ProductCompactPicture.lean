import Langlands.Representation.Plancherel.NormalizedCompactPicture
import Langlands.Representation.Plancherel.ProductInducedTransport
import Langlands.Representation.Twist.SmoothPartDefinitions

/-!
# A fixed compact picture for actual product-induced coefficient spaces

Restriction and the actual smooth-dual twist equivalence identify the product
induction attached to every unramified twist with a fixed compact section space.
-/

noncomputable section

open Langlands.Aubert.General Langlands.Induction
open scoped TensorProduct NNReal

namespace Langlands.Plancherel

universe uG uI uV uW

variable {G : Type uG} [Group G] [TopologicalSpace G] [NonarchimedeanGroup G]
  {M : Subgroup G} {I : Type uI} (ν : I → (M →* ℝ≥0ˣ))

/-- Remove the actual smooth-dual twist while retaining the vector and every
underlying linear functional. This is not an equivalence for the full product
Levi action; the compact-intersection compatibility is proved below. -/
def productCompactTwistTensorEquiv (χ : unramifiedCharacters ν)
    (A : SmoothRep.{0, uG, uV} ℂ M) :
    CoefficientTensor
        (A.twist χ.val.toMonoidHom (unramifiedCharacter_isOpen_ker ν χ)) ≃ₗ[ℂ]
      CoefficientTensor A :=
  TensorProduct.congr (LinearEquiv.refl ℂ A)
    (smoothContragredientTwistEquiv χ.val.toMonoidHom A.representation
      (unramifiedCharacter_isOpen_ker ν χ)).toLinearEquiv

@[simp]
theorem productCompactTwistTensorEquiv_tmul (χ : unramifiedCharacters ν)
    (A : SmoothRep.{0, uG, uV} ℂ M) (v : A)
    (ℓ : SmoothDual
      (A.twist χ.val.toMonoidHom (unramifiedCharacter_isOpen_ker ν χ)).representation) :
    productCompactTwistTensorEquiv ν χ A (v ⊗ₜ[ℂ] ℓ) =
      v ⊗ₜ[ℂ] smoothContragredientTwistEquiv χ.val.toMonoidHom A.representation
        (unramifiedCharacter_isOpen_ker ν χ) ℓ := rfl

/-- The bilinear contraction is preserved on all coefficient tensors. -/
theorem productCompactTwistTensorEquiv_pairing (χ : unramifiedCharacters ν)
    (A : SmoothRep.{0, uG, uV} ℂ M)
    (t : CoefficientTensor
      (A.twist χ.val.toMonoidHom (unramifiedCharacter_isOpen_ker ν χ))) :
    TensorProduct.lift (smoothDualPairing A.representation).flip
        (productCompactTwistTensorEquiv ν χ A t) =
      TensorProduct.lift (smoothDualPairing
        (A.twist χ.val.toMonoidHom (unramifiedCharacter_isOpen_ker ν χ)).representation).flip
        t := by
  induction t using TensorProduct.inductionOn with
  | tmul v ℓ => rfl
  | add t s ht hs => simp only [map_add, ht, hs]

variable {A : SmoothRep.{0, uG, uV} ℂ M} {B : SmoothRep.{0, uG, uW} ℂ M}

/-- Removing the smooth-dual twist commutes with actual representative
transport, including the inverse pullback on functionals. -/
theorem productCompactTwistTensorEquiv_natural (χ : unramifiedCharacters ν)
    (e : A.representation.Equiv B.representation)
    (t : CoefficientTensor
      (A.twist χ.val.toMonoidHom (unramifiedCharacter_isOpen_ker ν χ))) :
    productCompactTwistTensorEquiv ν χ B
        (coefficientTensorCongr (twistEquiv χ.val.toMonoidHom e) t) =
      coefficientTensorCongr e (productCompactTwistTensorEquiv ν χ A t) := by
  induction t using TensorProduct.inductionOn with
  | tmul v ℓ => rfl
  | add t s ht hs => simp only [map_add, ht, hs]

variable [LocallyCompactSpace G]
  {P U : Subgroup G} (h : IsSemidirectDecomposition P M U) (K : OpenSubgroup G)

/-- The fixed actual compact space of product-induced coefficient sections. -/
abbrev ProductInducedCompactPicture (A : SmoothRep.{0, uG, uV} ℂ M) :=
  CompactInductionPicture (h.prod h) (K.prod K)
    (productLeviObject A A.contragredient)

/-- The actual right action of the compact product subgroup on that space. -/
abbrev productInducedCompactRepresentation (A : SmoothRep.{0, uG, uV} ℂ M) :=
  smoothInduced ((P.prod P).comap (K.prod K).toSubgroup.subtype)
    (compactPictureInducingRepresentation (h.prod h) (K.prod K)
      (productLeviObject A A.contragredient))

variable (hP : IsClosed (P : Set G)) (hK : IsCompact (K : Set G))
  (hν : ∀ i, Continuous (ν i)) (hr : Continuous h.projection)

include hP hK hν hr in
omit [LocallyCompactSpace G] in
private theorem compact_projection_character_eq_one (χ : unramifiedCharacters ν)
    (p : P) (hp : (p : G) ∈ K) : χ.val (h.projection p) = 1 :=
  unramifiedPullback_eq_one_of_mem_conjOpenSubgroup P hP ν hν
    h.projection hr χ K hK 1 (by
      apply mem_conjOpenSubgroup.mpr
      simpa only [inv_one, one_mul, mul_one] using hp)

/-- The actual coefficient-tensor comparison intertwines the two compact
intersection actions. Compactness removes each character factor separately. -/
def productCompactTwistInducingEquiv (χ : unramifiedCharacters ν)
    (A : SmoothRep.{0, uG, uV} ℂ M) :
    Representation.Equiv
      (compactPictureInducingRepresentation (h.prod h) (K.prod K)
        (productLeviObject
          (A.twist χ.val.toMonoidHom (unramifiedCharacter_isOpen_ker ν χ))
          (A.twist χ.val.toMonoidHom (unramifiedCharacter_isOpen_ker ν χ)).contragredient))
      (compactPictureInducingRepresentation (h.prod h) (K.prod K)
        (productLeviObject A A.contragredient)) :=
  Representation.Equiv.mk (productCompactTwistTensorEquiv ν χ A) (by
    intro p
    apply TensorProduct.ext
    ext v ℓ
    let q := (K.prod K).toSubgroup.subtype.subgroupComap (P.prod P) p
    let q₁ : P := ⟨q.1.1, q.2.1⟩
    let q₂ : P := ⟨q.1.2, q.2.2⟩
    have hχ₁ : χ.val (h.projection q₁) = 1 :=
      compact_projection_character_eq_one ν h K hP hK hν hr χ q₁ p.1.property.1
    have hχ₂ : χ.val (h.projection q₂) = 1 :=
      compact_projection_character_eq_one ν h K hP hK hν hr χ q₂ p.1.property.2
    change productCompactTwistTensorEquiv ν χ A
      ((productLeviObject
        (A.twist χ.val.toMonoidHom (unramifiedCharacter_isOpen_ker ν χ))
        (A.twist χ.val.toMonoidHom (unramifiedCharacter_isOpen_ker ν χ)).contragredient).representation
          ((h.prod h).projection q) (v ⊗ₜ[ℂ] ℓ)) =
      (productLeviObject A A.contragredient).representation ((h.prod h).projection q)
        (productCompactTwistTensorEquiv ν χ A (v ⊗ₜ[ℂ] ℓ))
    rw [h.prod_projection h q]
    let D := smoothContragredientTwistEquiv χ.val.toMonoidHom A.representation
      (unramifiedCharacter_isOpen_ker ν χ)
    have hD := congrArg (fun T => T ℓ) (D.isIntertwining' (h.projection q₂))
    change D (smoothContragredient
        (A.twist χ.val.toMonoidHom (unramifiedCharacter_isOpen_ker ν χ)).representation
          (h.projection q₂) ℓ) =
      ((χ.val (h.projection q₂))⁻¹ : ℂˣ) •
        smoothContragredient A.representation (h.projection q₂) (D ℓ) at hD
    change ((χ.val (h.projection q₁) : ℂ) • A.representation (h.projection q₁) v) ⊗ₜ[ℂ]
        D (smoothContragredient
          (A.twist χ.val.toMonoidHom (unramifiedCharacter_isOpen_ker ν χ)).representation
            (h.projection q₂) ℓ) =
      A.representation (h.projection q₁) v ⊗ₜ[ℂ]
        smoothContragredient A.representation (h.projection q₂) (D ℓ)
    rw [hD, hχ₁, hχ₂]
    simp)

variable (hU : IsClosed (U : Set G))
  (hPK : ∀ g : G, ∃ p : P, ∃ k : K, g = (p : G) * (k : G))

include hPK in
omit [LocallyCompactSpace G] [NonarchimedeanGroup G] in
/-- Coordinatewise factorization gives the actual product factorization. -/
theorem product_compact_factorization (x : G × G) :
    ∃ p : P.prod P, ∃ k : K.prod K, x = (p : G × G) * (k : G × G) := by
  obtain ⟨p, k, hp⟩ := hPK x.1
  obtain ⟨q, l, hq⟩ := hPK x.2
  exact ⟨⟨(p, q), p.2, q.2⟩, ⟨(k, l), k.2, l.2⟩, Prod.ext hp hq⟩

/-- Every actual unramified-twisted product induction has one fixed compact
picture, using the actual smooth dual of the twisted inducing representation. -/
def productInducedCompactEquiv (χ : unramifiedCharacters ν)
    (A : SmoothRep.{0, uG, uV} ℂ M) :
    Representation.Equiv
      ((productInducedCoefficientObject h hU
        (A.twist χ.val.toMonoidHom (unramifiedCharacter_isOpen_ker ν χ))).representation.comp
          (K.prod K).toSubgroup.subtype)
      (productInducedCompactRepresentation h K A) :=
  (normalizedInductionCompactEquiv (h.prod h) (K.prod K) (hU.prod hU)
    (hP.prod hP) (hK.prod hK) (product_compact_factorization K hPK)
    (productLeviObject
      (A.twist χ.val.toMonoidHom (unramifiedCharacter_isOpen_ker ν χ))
      (A.twist χ.val.toMonoidHom (unramifiedCharacter_isOpen_ker ν χ)).contragredient)).trans
    (smoothInducedEquiv _ (productCompactTwistInducingEquiv ν h K hP hK hν hr χ A))

@[simp]
theorem productInducedCompactEquiv_eval (χ : unramifiedCharacters ν)
    (A : SmoothRep.{0, uG, uV} ℂ M)
    (F : productInducedCoefficientObject h hU
      (A.twist χ.val.toMonoidHom (unramifiedCharacter_isOpen_ker ν χ))) (k : K.prod K) :
    eval _ _ (productInducedCompactEquiv ν h K hP hK hν hr hU hPK χ A F) k =
      productCompactTwistTensorEquiv ν χ A (eval _ _ F k) := rfl

/-- The inverse extends by actual normalized product covariance after undoing
the functional-preserving tensor equivalence. -/
@[simp]
theorem productInducedCompactEquiv_symm_mul (χ : unramifiedCharacters ν)
    (A : SmoothRep.{0, uG, uV} ℂ M) (F : ProductInducedCompactPicture h K A)
    (p : P.prod P) (k : K.prod K) :
    eval _ _
      ((productInducedCompactEquiv ν h K hP hK hν hr hU hPK χ A).symm F)
      ((p : G × G) * (k : G × G)) =
      (inducingRepresentation (h.prod h) (hU.prod hU)
        (productLeviObject
          (A.twist χ.val.toMonoidHom (unramifiedCharacter_isOpen_ker ν χ))
          (A.twist χ.val.toMonoidHom (unramifiedCharacter_isOpen_ker ν χ)).contragredient) p)
        ((productCompactTwistTensorEquiv ν χ A).symm (eval _ _ F k)) :=
  normalizedInductionCompactEquiv_symm_mul (h.prod h) (K.prod K) (hU.prod hU)
    (hP.prod hP) (hK.prod hK) (product_compact_factorization K hPK) _ _ p k

/-- Representative transport on the fixed compact picture is pointwise vector
transport tensored with inverse smooth-dual pullback. -/
def productCompactRepresentativeEquiv (e : A.representation.Equiv B.representation) :
    (productInducedCompactRepresentation h K A).Equiv
      (productInducedCompactRepresentation h K B) :=
  compactInductionPictureEquiv (h.prod h) (K.prod K) (productCoefficientLeviEquiv e)

omit [LocallyCompactSpace G] in
@[simp]
theorem productCompactRepresentativeEquiv_eval
    (e : A.representation.Equiv B.representation)
    (F : ProductInducedCompactPicture h K A) (k : K.prod K) :
    eval _ _ (productCompactRepresentativeEquiv h K e F) k =
      coefficientTensorCongr e (eval _ _ F k) := rfl

/-- The actual product-induced representative map commutes with the fixed
compact-picture comparison for every unramified parameter. -/
theorem productInducedCompactEquiv_natural (χ : unramifiedCharacters ν)
    (e : A.representation.Equiv B.representation)
    (F : productInducedCoefficientObject h hU
      (A.twist χ.val.toMonoidHom (unramifiedCharacter_isOpen_ker ν χ))) :
    productInducedCompactEquiv ν h K hP hK hν hr hU hPK χ B
      (productInducedCoefficientTransport h hU (twistEquiv χ.val.toMonoidHom e) F) =
      productCompactRepresentativeEquiv h K e
        (productInducedCompactEquiv ν h K hP hK hν hr hU hPK χ A F) := by
  apply Subtype.ext
  apply Subtype.ext
  funext k
  exact productCompactTwistTensorEquiv_natural ν χ e _

end Langlands.Plancherel
