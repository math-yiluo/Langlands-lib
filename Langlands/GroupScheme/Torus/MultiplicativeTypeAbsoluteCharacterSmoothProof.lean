import Langlands.GroupScheme.Torus.MultiplicativeTypeAbsoluteCharacterStatement
import Langlands.GroupScheme.Torus.MultiplicativeTypeGeometry
import Langlands.GroupScheme.Torus.LatticeGaloisContinuityProof

/-! # Continuity of actual multiplicative-type characters -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme

theorem multiplicativeTypeAbsoluteCharacterSmooth :
    MultiplicativeTypeAbsoluteCharacterSmoothStatement.{u} := by
  intro k _ T hT χ
  let Ω := SeparableClosure k
  let b := algebraBaseMap k Ω
  let S₀ := Gm (Spec (CommRingCat.of k))
  let f : (CommGroupScheme.baseChange b).obj T ⟶
      (CommGroupScheme.baseChange b).obj S₀ :=
    χ ≫ (Gm.commBaseChangeIso b).inv
  let : IsAffineHom T.X.hom := hT.isAffineHom
  let : Smooth S₀.X.hom := smooth_gm _
  let D := Descent.FiniteStage.homModel k Ω (CommGroupScheme.groupHom f)
  let : FiniteDimensional k D.fieldOfDefinition.1 := D.fieldOfDefinition.2
  refine ⟨⟨D.fieldOfDefinition.1.fixingSubgroup,
    D.fieldOfDefinition.1.fixingSubgroup_isOpen⟩, ?_⟩
  rw [fixedVectors, Representation.mem_invariants]
  intro σ
  have hσ : ∀ x ∈ D.fieldOfDefinition.1, σ.val x = x :=
    (IntermediateField.mem_fixingSubgroup_iff _ _).mp σ.property
  have hdesc := LatticeGaloisContinuity.descent_comm_of_model
    D.fieldOfDefinition D.hom (CommGroupScheme.groupHom f) D.recovery σ.val hσ
  have htrans : galoisHomTransport σ.val f = f := by
    change Additive.ofMul
      ((descentBaseChangeIso b (galoisBaseMap k Ω σ.val)
        (galoisBaseMap_over k Ω σ.val) T.toGrp).inv ≫
        (baseChange (galoisBaseMap k Ω σ.val)).map (CommGroupScheme.groupHom f) ≫
        (descentBaseChangeIso b (galoisBaseMap k Ω σ.val)
          (galoisBaseMap_over k Ω σ.val) S₀.toGrp).hom) = f
    rw [hdesc, Iso.inv_hom_id_assoc]
    rfl
  have h := galoisHomTransport_comp σ.val f
    (characterLattice.baseChange b S₀ (𝟙 S₀))
  rw [htrans, characterLattice.galoisRepresentation_baseChange] at h
  have hf : f ≫ characterLattice.baseChange b S₀ (𝟙 S₀) = χ := by
    simp [f, characterLattice.baseChange_apply]
  rw [hf] at h
  exact h.symm

end Langlands.GroupScheme
