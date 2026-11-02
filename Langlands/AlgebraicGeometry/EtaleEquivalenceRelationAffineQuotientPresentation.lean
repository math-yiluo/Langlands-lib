import Langlands.AlgebraicGeometry.EtaleEquivalenceRelationAffineCoordinates
import Langlands.AlgebraicGeometry.GroupoidCoactionInvariants
import Mathlib.RingTheory.TensorProduct.IncludeLeftSubRight

/-! # Invariant-ring presentations from affine quotients -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct

namespace Langlands.AlgebraicGeometry

namespace GroupoidCoaction

variable {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
  [Algebra A B] [Algebra B C] (t : B →+* C)
  (hP : IsPushout (CommRingCat.ofHom (algebraMap A B))
    (CommRingCat.ofHom (algebraMap A B)) (CommRingCat.ofHom (algebraMap B C))
    (CommRingCat.ofHom t))

include hP

/-- The quotient-ring map with its codomain restricted to invariant elements. -/
def quotientToInvariant : A →+* invariantRing t :=
  (algebraMap A B).codRestrict _ fun a =>
    (RingHom.congr_fun (congrArg CommRingCat.Hom.hom hP.w) a).symm

@[simp]
theorem quotientToInvariant_coe (a : A) :
    (quotientToInvariant t hP a : B) = algebraMap A B a := rfl

/-- Faithfully flat effectivity identifies invariant elements with the image
of the quotient-ring map. -/
theorem mem_invariantRing_iff_mem_range [Module.FaithfullyFlat A B] (b : B) :
    b ∈ invariantRing t ↔ b ∈ Set.range (algebraMap A B) := by
  let e := tensorEquivOfIsPushout t hP
  have ht (b : B) : e (t b) = (1 : B) ⊗ₜ[A] b := by
    rw [← tensorEquivOfIsPushout_symm_right t hP b]
    exact e.apply_symm_apply _
  rw [← (Algebra.IsEffective.of_faithfullyFlat A B).eqLocus_includeLeft_includeRight]
  change t b = algebraMap B C b ↔
    b ⊗ₜ[A] (1 : B) = (1 : B) ⊗ₜ[A] b
  rw [← e.injective.eq_iff, ht, e.commutes]
  exact eq_comm

theorem quotientToInvariant_bijective [Module.FaithfullyFlat A B] :
    Function.Bijective (quotientToInvariant t hP) := by
  constructor
  · intro a b hab
    exact FaithfulSMul.algebraMap_injective A B (congrArg Subtype.val hab)
  · intro b
    obtain ⟨a, ha⟩ := (mem_invariantRing_iff_mem_range t hP b).mp b.property
    exact ⟨a, Subtype.ext ha⟩

/-- The actual faithfully flat quotient ring is the invariant ring. -/
noncomputable def quotientInvariantEquiv [Module.FaithfullyFlat A B] :
    A ≃+* invariantRing t :=
  RingEquiv.ofBijective (quotientToInvariant t hP) (quotientToInvariant_bijective t hP)

@[simp]
theorem quotientInvariantEquiv_coe [Module.FaithfullyFlat A B] (a : A) :
    (quotientInvariantEquiv t hP a : B) = algebraMap A B a := rfl

/-- Faithful flatness over the quotient transports to the actual invariant ring. -/
theorem faithfullyFlat_invariantRing_of_isPushout [Module.FaithfullyFlat A B] :
    Module.FaithfullyFlat (invariantRing t) B := by
  let e := quotientInvariantEquiv t hP
  have hf : (algebraMap A B).FaithfullyFlat := RingHom.faithfullyFlat_algebraMap_iff.mpr
    inferInstance
  have hg := RingHom.FaithfullyFlat.respectsIso.2 (algebraMap A B) e.symm hf
  have he : (algebraMap A B).comp e.symm.toRingHom =
      algebraMap (invariantRing t) B := by
    ext b
    have hb := quotientInvariantEquiv_coe t hP (e.symm b)
    change algebraMap A B (e.symm b) = (b : B)
    change (e (e.symm b) : B) = algebraMap A B (e.symm b) at hb
    simpa only [e.apply_symm_apply] using hb.symm
  rw [he, RingHom.faithfullyFlat_algebraMap_iff] at hg
  exact hg

/-- The quotient pushout can be expressed over the invariant ring. -/
theorem invariantRing_isPushout_of_isPushout [Module.FaithfullyFlat A B] :
    IsPushout (CommRingCat.ofHom (algebraMap (invariantRing t) B))
      (CommRingCat.ofHom (algebraMap (invariantRing t) B))
      (CommRingCat.ofHom (algebraMap B C)) (CommRingCat.ofHom t) := by
  let e := quotientInvariantEquiv t hP
  exact hP.of_iso e.toCommRingCatIso (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (by ext a; exact (quotientInvariantEquiv_coe t hP a).symm)
    (by ext a; exact (quotientInvariantEquiv_coe t hP a).symm)
    (by simp) (by simp)

/-- Tensor coordinates of the actual relation over its invariant ring. -/
noncomputable def invariantTensorEquivOfIsPushout [Module.FaithfullyFlat A B] :
    B ⊗[invariantRing t] B ≃ₐ[B] C :=
  (tensorEquivOfIsPushout t (invariantRing_isPushout_of_isPushout t hP)).symm

@[simp]
theorem invariantTensorEquivOfIsPushout_target [Module.FaithfullyFlat A B] (b : B) :
    invariantTensorEquivOfIsPushout t hP ((1 : B) ⊗ₜ[invariantRing t] b) = t b :=
  tensorEquivOfIsPushout_symm_right t (invariantRing_isPushout_of_isPushout t hP) b

end GroupoidCoaction

namespace EtaleEquivalenceRelation

/-- An actual affine quotient supplies faithful flatness and effective tensor
coordinates over the invariant ring of the unchanged relation. -/
theorem invariantPresentation_of_hasAffineQuotient (E : EtaleEquivalenceRelation.{u})
    [IsAffine E.U] (hQ : E.HasAffineQuotient) :
    letI : Algebra Γ(E.U, ⊤) Γ(E.R, ⊤) := E.s.appTop.hom.toAlgebra
    Module.FaithfullyFlat (GroupoidCoaction.invariantRing E.t.appTop.hom) Γ(E.U, ⊤) ∧
      ∃ e : Γ(E.U, ⊤) ⊗[GroupoidCoaction.invariantRing E.t.appTop.hom] Γ(E.U, ⊤)
          ≃ₐ[Γ(E.U, ⊤)] Γ(E.R, ⊤),
        ∀ b : Γ(E.U, ⊤), e ((1 : Γ(E.U, ⊤)) ⊗ₜ[_] b) = E.t.appTop.hom b := by
  let : Algebra Γ(E.U, ⊤) Γ(E.R, ⊤) := E.s.appTop.hom.toAlgebra
  obtain ⟨M, q, hM, hpb, hflat, _, hsurj⟩ := hQ
  let : IsAffine M := hM
  let : IsAffine E.R := IsAffine.of_isPullback hpb
  let : Algebra Γ(M, ⊤) Γ(E.U, ⊤) := q.appTop.hom.toAlgebra
  have hP := (isPushout_appTop_of_isPullback hpb).flip
  have hf : q.appTop.hom.FaithfullyFlat :=
    (Flat.flat_and_surjective_iff_faithfullyFlat_of_isAffine q).mp ⟨hflat, hsurj⟩
  let : Module.FaithfullyFlat Γ(M, ⊤) Γ(E.U, ⊤) :=
    RingHom.faithfullyFlat_algebraMap_iff.mp hf
  refine ⟨GroupoidCoaction.faithfullyFlat_invariantRing_of_isPushout E.t.appTop.hom hP,
    GroupoidCoaction.invariantTensorEquivOfIsPushout E.t.appTop.hom hP, ?_⟩
  exact GroupoidCoaction.invariantTensorEquivOfIsPushout_target E.t.appTop.hom hP

end EtaleEquivalenceRelation

end Langlands.AlgebraicGeometry
