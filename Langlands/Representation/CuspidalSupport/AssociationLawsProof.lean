import Langlands.Representation.CuspidalSupport.MinimalConjugatingCosetsProof
import Langlands.Representation.CuspidalSupport.AssociationLawsStatement

/-! Proof of the algebraic relation laws for actual Levi and representation
association: identity, inverse, and composite permutations. -/

namespace Langlands.CuspidalSupport

open GeneralLinear

universe uF uV uW uX

section Laws

variable {F : Type uF} [Field F] {n : ℕ}

/-- Conjugation by a product is the composite of the two conjugations. -/
theorem conj_mul_toMonoidHom (p q : Langlands.GeneralLinear n F) :
    (MulAut.conj (p * q)).toMonoidHom =
      (MulAut.conj p).toMonoidHom.comp (MulAut.conj q).toMonoidHom :=
  MonoidHom.ext fun x => by simp [MulAut.conj_apply, mul_assoc]

/-- Conjugation by the identity matrix fixes every subgroup. -/
theorem map_conj_one (H : Subgroup (Langlands.GeneralLinear n F)) :
    H.map (MulAut.conj (1 : Langlands.GeneralLinear n F)).toMonoidHom = H := by
  have h : (MulAut.conj (1 : Langlands.GeneralLinear n F)).toMonoidHom =
      MonoidHom.id _ :=
    MonoidHom.ext fun x => by simp
  rw [h, Subgroup.map_id]

/-- The identity permutation conjugates every Levi onto itself. -/
theorem conjugatesLevi_one (B : BlockShape n) :
    ConjugatesLevi (F := F) B B 1 := by
  unfold ConjugatesLevi
  rw [map_one]
  exact map_conj_one _

/-- The identity permutation induces the identity Levi equivalence. -/
theorem leviConjugation_one (B : BlockShape n) (h : ConjugatesLevi (F := F) B B 1) :
    leviConjugation B B 1 h = MulEquiv.refl (B.Levi F) :=
  MulEquiv.ext fun m => B.leviEmbedding_injective F (by
    rw [leviConjugation_embedding]
    simp)

/-- The inverse permutation induces the inverse Levi equivalence. -/
theorem leviConjugation_inv_symm {B C : BlockShape n} {w : Equiv.Perm (Fin n)}
    (hw : ConjugatesLevi (F := F) B C w) (h : ConjugatesLevi (F := F) C B w⁻¹) :
    (leviConjugation C B w⁻¹ h).symm = leviConjugation B C w hw :=
  MulEquiv.ext fun m => C.leviEmbedding_injective F (by
    rw [leviConjugation_symm_embedding, leviConjugation_embedding, map_inv, inv_inv])

/-- The composite permutation induces the composite Levi equivalence. -/
theorem leviConjugation_mul {B C D : BlockShape n} {w v : Equiv.Perm (Fin n)}
    (hw : ConjugatesLevi (F := F) B C w) (hv : ConjugatesLevi (F := F) C D v)
    (h : ConjugatesLevi (F := F) B D (v * w)) :
    leviConjugation B D (v * w) h =
      (leviConjugation B C w hw).trans (leviConjugation C D v hv) :=
  MulEquiv.ext fun m => D.leviEmbedding_injective F (by
    rw [MulEquiv.trans_apply, leviConjugation_embedding, leviConjugation_embedding,
      leviConjugation_embedding, map_mul]
    simp only [mul_inv_rev, mul_assoc])

theorem leviAssociationEquivalence : LeviAssociationEquivalenceTheorem.{uF} := by
  intro F _ n
  refine ⟨fun B => ⟨⟨1, conjugatesLevi_one B⟩⟩, ?_, ?_⟩
  · rintro B C ⟨⟨w, hw⟩⟩
    exact ⟨⟨w⁻¹, conjugatesLevi_inv hw⟩⟩
  · rintro B C D ⟨⟨w, hw⟩⟩ ⟨⟨v, hv⟩⟩
    exact ⟨⟨v * w, conjugatesLevi_mul hw hv⟩⟩

theorem representationAssociationReflexivity :
    RepresentationAssociationReflexivityTheorem.{uF, uV} := by
  intro F _ n B V _ _ ρ
  let h := conjugatesLevi_one (F := F) B
  refine ⟨1, h, ⟨Representation.Equiv.mk (LinearEquiv.refl ℂ V) fun m => ?_⟩⟩
  refine LinearMap.ext fun x => ?_
  change ρ ((leviConjugation B B 1 h).symm m) x = ρ m x
  rw [leviConjugation_one]
  rfl

theorem representationAssociationSymmetry :
    RepresentationAssociationSymmetryTheorem.{uF, uV, uW} := by
  intro F _ n B C V W _ _ _ _ ρ σ
  rintro ⟨w, hw, ⟨e⟩⟩
  let h := conjugatesLevi_inv hw
  refine ⟨w⁻¹, h, ⟨Representation.Equiv.mk e.symm.toLinearEquiv fun m => ?_⟩⟩
  refine LinearMap.ext fun x => ?_
  change e.symm (σ ((leviConjugation C B w⁻¹ h).symm m) x) = ρ m (e.symm x)
  rw [leviConjugation_inv_symm hw h]
  have hi : e.symm (σ (leviConjugation B C w hw m) x) =
      transport B C w hw ρ (leviConjugation B C w hw m) (e.symm x) :=
    LinearMap.congr_fun (e.symm.isIntertwining' (leviConjugation B C w hw m)) x
  rw [hi]
  change ρ ((leviConjugation B C w hw).symm (leviConjugation B C w hw m)) _ = _
  rw [MulEquiv.symm_apply_apply]

theorem representationAssociationTransitivity :
    RepresentationAssociationTransitivityTheorem.{uF, uV, uW, uX} := by
  intro F _ n B C D V W X _ _ _ _ _ _ ρ σ τ
  rintro ⟨w, hw, ⟨e₁⟩⟩ ⟨v, hv, ⟨e₂⟩⟩
  let h := conjugatesLevi_mul hw hv
  refine ⟨v * w, h, ⟨Representation.Equiv.mk
    (e₁.toLinearEquiv.trans e₂.toLinearEquiv) fun m => ?_⟩⟩
  refine LinearMap.ext fun x => ?_
  change e₂ (e₁ (ρ ((leviConjugation B D (v * w) h).symm m) x)) =
    τ m (e₂ (e₁ x))
  rw [leviConjugation_mul hw hv h, MulEquiv.symm_trans_apply]
  have h₁ : e₁ (ρ ((leviConjugation B C w hw).symm
      ((leviConjugation C D v hv).symm m)) x) =
      σ ((leviConjugation C D v hv).symm m) (e₁ x) :=
    LinearMap.congr_fun (e₁.isIntertwining' ((leviConjugation C D v hv).symm m)) x
  have h₂ : e₂ (σ ((leviConjugation C D v hv).symm m) (e₁ x)) = τ m (e₂ (e₁ x)) :=
    LinearMap.congr_fun (e₂.isIntertwining' m) (e₁ x)
  rw [h₁, h₂]

/-- The algebraic association laws: Levi association is an equivalence
relation, and representation association is reflexive, symmetric, and
transitive across independent carrier universes. -/
theorem associationRelationLaws :
    AssociationRelationLawsTheorem.{uF, uV, uW, uX} :=
  ⟨leviAssociationEquivalence, representationAssociationReflexivity,
    representationAssociationSymmetry, representationAssociationTransitivity⟩

end Laws

end Langlands.CuspidalSupport
