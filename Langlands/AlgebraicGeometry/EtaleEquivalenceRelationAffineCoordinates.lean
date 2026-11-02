import Langlands.AlgebraicGeometry.GroupoidCoactionPushforward
import Langlands.AlgebraicGeometry.EtaleEquivalenceRelationRingFormProof
import Mathlib.AlgebraicGeometry.Morphisms.Affine

/-! # Tensor coordinates for affine cartesian relation morphisms -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct

namespace Langlands.AlgebraicGeometry

namespace GroupoidCoaction

variable {B C D P : Type u} [CommRing B] [CommRing C] [CommRing D] [CommRing P]
  [Algebra B C] [Algebra B D] [Algebra D P]

/-- Tensor coordinates for a pushout square of commutative rings. -/
noncomputable def tensorEquivOfIsPushout (ρ : C →+* P)
    (h : IsPushout (CommRingCat.ofHom (algebraMap B D))
      (CommRingCat.ofHom (algebraMap B C)) (CommRingCat.ofHom (algebraMap D P))
      (CommRingCat.ofHom ρ)) : P ≃ₐ[D] D ⊗[B] C := by
  let h₀ := CommRingCat.isPushout_tensorProduct B D C
  let i := h₀.isoIsPushout _ _ h
  let e := i.commRingCatIsoToRingEquiv
  have he (d : D) : e (d ⊗ₜ[B] (1 : C)) = algebraMap D P d :=
    RingHom.congr_fun (congrArg CommRingCat.Hom.hom (h₀.inl_isoIsPushout_hom _ _ h)) d
  exact
    { __ := e.symm
      commutes' := fun d => by
        apply e.injective
        change e (e.symm (algebraMap D P d)) = e (d ⊗ₜ[B] (1 : C))
        rw [e.apply_symm_apply, he] }

@[simp]
theorem tensorEquivOfIsPushout_symm_right (ρ : C →+* P)
    (h : IsPushout (CommRingCat.ofHom (algebraMap B D))
      (CommRingCat.ofHom (algebraMap B C)) (CommRingCat.ofHom (algebraMap D P))
      (CommRingCat.ofHom ρ)) (c : C) :
    (tensorEquivOfIsPushout ρ h).symm ((1 : D) ⊗ₜ[B] c) = ρ c := by
  exact RingHom.congr_fun (congrArg CommRingCat.Hom.hom
    ((CommRingCat.isPushout_tensorProduct B D C).inr_isoIsPushout_hom _ _ h)) c

@[simp]
theorem cartesianBaseMap_tensorEquivOfIsPushout (ρ : C →+* P)
    (h : IsPushout (CommRingCat.ofHom (algebraMap B D))
      (CommRingCat.ofHom (algebraMap B C)) (CommRingCat.ofHom (algebraMap D P))
      (CommRingCat.ofHom ρ)) :
    cartesianBaseMap (tensorEquivOfIsPushout ρ h) = ρ := by
  ext c
  exact tensorEquivOfIsPushout_symm_right ρ h c

end GroupoidCoaction

namespace EtaleEquivalenceRelation

section Cartesian

variable (E' E : EtaleEquivalenceRelation.{u}) [IsAffine E'.U] [IsAffine E.U]
  [IsAffine E.R] (f : E'.U ⟶ E.U) (g : E'.R ⟶ E.R)
  (h : E'.IsCartesianHom E f g)

/-- The source-cartesian square of affine schemes gives precisely the tensor
presentation used by coaction pushforward. -/
noncomputable def sourceTensorEquiv :
    letI : Algebra Γ(E.U, ⊤) Γ(E.R, ⊤) := E.s.appTop.hom.toAlgebra
    letI : Algebra Γ(E.U, ⊤) Γ(E'.U, ⊤) := f.appTop.hom.toAlgebra
    letI : Algebra Γ(E'.U, ⊤) Γ(E'.R, ⊤) := E'.s.appTop.hom.toAlgebra
    Γ(E'.R, ⊤) ≃ₐ[Γ(E'.U, ⊤)] Γ(E'.U, ⊤) ⊗[Γ(E.U, ⊤)] Γ(E.R, ⊤) := by
  letI : Algebra Γ(E.U, ⊤) Γ(E.R, ⊤) := E.s.appTop.hom.toAlgebra
  letI : Algebra Γ(E.U, ⊤) Γ(E'.U, ⊤) := f.appTop.hom.toAlgebra
  letI : Algebra Γ(E'.U, ⊤) Γ(E'.R, ⊤) := E'.s.appTop.hom.toAlgebra
  exact GroupoidCoaction.tensorEquivOfIsPushout g.appTop.hom
    (isPushout_appTop_of_isPullback h.2).flip

/-- The relation-ring map encoded by the tensor presentation is the actual
map on global sections of the relation morphism. -/
theorem sourceTensorEquiv_baseMap :
    letI : Algebra Γ(E.U, ⊤) Γ(E.R, ⊤) := E.s.appTop.hom.toAlgebra
    letI : Algebra Γ(E.U, ⊤) Γ(E'.U, ⊤) := f.appTop.hom.toAlgebra
    letI : Algebra Γ(E'.U, ⊤) Γ(E'.R, ⊤) := E'.s.appTop.hom.toAlgebra
    GroupoidCoaction.cartesianBaseMap (sourceTensorEquiv E' E f g h) = g.appTop.hom := by
  let : Algebra Γ(E.U, ⊤) Γ(E.R, ⊤) := E.s.appTop.hom.toAlgebra
  let : Algebra Γ(E.U, ⊤) Γ(E'.U, ⊤) := f.appTop.hom.toAlgebra
  let : Algebra Γ(E'.U, ⊤) Γ(E'.R, ⊤) := E'.s.appTop.hom.toAlgebra
  apply GroupoidCoaction.cartesianBaseMap_tensorEquivOfIsPushout

/-- Compatibility of the actual scheme morphism with targets supplies the
target equation required by coaction pushforward. -/
theorem sourceTensorEquiv_target :
    letI : Algebra Γ(E.U, ⊤) Γ(E.R, ⊤) := E.s.appTop.hom.toAlgebra
    letI : Algebra Γ(E.U, ⊤) Γ(E'.U, ⊤) := f.appTop.hom.toAlgebra
    letI : Algebra Γ(E'.U, ⊤) Γ(E'.R, ⊤) := E'.s.appTop.hom.toAlgebra
    (GroupoidCoaction.cartesianBaseMap (sourceTensorEquiv E' E f g h)).comp
      E.t.appTop.hom = E'.t.appTop.hom.comp f.appTop.hom := by
  rw [sourceTensorEquiv_baseMap]
  exact congrArg (fun k : E'.R ⟶ E.U => k.appTop.hom) h.1

end Cartesian

/-- An affine quotient makes the relation map a closed immersion, since it
is the pullback of the diagonal of the quotient. -/
theorem isClosedImmersion_of_hasAffineQuotient (E : EtaleEquivalenceRelation.{u})
    (hQ : E.HasAffineQuotient) : IsClosedImmersion (prod.lift E.t E.s) := by
  obtain ⟨M, q, hM, hpb, _⟩ := hQ
  let : IsAffine M := hM
  let hprod := IsPullback.of_hasBinaryProduct' E.U E.U
  let i := hpb.isoPullback.hom ≫ pullback.mapDesc q q (terminal.from M) ≫
    (pullback.congrHom (terminal.comp_from q) (terminal.comp_from q)).hom ≫
    hprod.isoPullback.inv
  have hi : i = prod.lift E.t E.s := by
    apply prod.hom_ext <;>
      simp [i, pullback.congrHom, pullback.mapDesc, pullback.map, Category.assoc,
        pullback.lift_fst, pullback.lift_snd]
  have : IsClosedImmersion i := inferInstance
  rwa [hi] at this

/-- The actual affine relation with an affine quotient has the published
ring-level relation laws, without an additional closed-immersion premise. -/
theorem ringRelation_of_hasAffineQuotient (E : EtaleEquivalenceRelation.{u})
    [IsAffine E.U] (hQ : E.HasAffineQuotient) :
    letI : Algebra Γ(E.U, ⊤) Γ(E.R, ⊤) := E.s.appTop.hom.toAlgebra
    RingEtaleEquivalenceRelation E.t.appTop.hom := by
  have hclosed := E.isClosedImmersion_of_hasAffineQuotient hQ
  obtain ⟨M, q, hM, hpb, _⟩ := hQ
  let : IsAffine M := hM
  let : IsAffine E.R := IsAffine.of_isPullback hpb
  exact etaleEquivalenceRelationRingForm E inferInstance inferInstance hclosed

end EtaleEquivalenceRelation

end Langlands.AlgebraicGeometry
