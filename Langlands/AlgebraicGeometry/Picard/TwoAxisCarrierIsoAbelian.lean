import Langlands.AlgebraicGeometry.Picard.TwoAxisCarrierIso

/-! # Two-axis rigidified bundles with isomorphic carriers: abelian schemes -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace Langlands.AlgebraicGeometry.Picard

open Langlands.SchemeModule Langlands.Scheme.Modules

namespace TwoAxisRigidifiedLineBundle

open Langlands.AbelianScheme

variable {S : Scheme.{u}} (A : Langlands.AbelianScheme S)

lemma mumfordSection_fst :
    mumfordSection A ≫ pullback.fst A.X.hom A.X.hom = 𝟙 A.X.left :=
  relativeSection_projection A.X.hom (unitSection A) (unitSection_comp A) A.X

/-- Two compatible two-axis rigidifications on isomorphic actual line bundles over the
self-product of an abelian scheme give isomorphic rigidified bundles. -/
theorem nonempty_iso_of_carrierIso
    {L M : TwoAxisRigidifiedLineBundle (unitSection A) (unitSection A)
      (mumfordSection A) (twoAxisSecond A) (twoAxis_unit_comp A)}
    (f : L.obj.carrier ≅ M.obj.carrier) : Nonempty (L ≅ M) := by
  obtain ⟨g₁, hfirst⟩ : ∃ g₁ : L.obj.carrier ≅ M.obj.carrier,
      L.obj.rigidification.first.hom ≫
        (Scheme.Modules.pullback (mumfordSection A)).map g₁.hom =
          M.obj.rigidification.first.hom := by
    let L₁ : RigidifiedLineBundle (mumfordSection A) :=
      ⟨⟨L.obj.carrier, L.obj.rigidification.first⟩, L.property⟩
    let M₁ : RigidifiedLineBundle (mumfordSection A) :=
      ⟨⟨M.obj.carrier, M.obj.rigidification.first⟩, M.property⟩
    obtain ⟨g⟩ : Nonempty (L₁ ≅ M₁) :=
      ⟨RigidifiedLineBundle.isoOfCarrierIso pullbackTensorComparisonIsIso
        (pullback.fst A.X.hom A.X.hom) (mumfordSection_fst A) f⟩
    exact ⟨(RigidifiedModule.forget _).mapIso ((ObjectProperty.ι _).mapIso g),
      g.hom.hom.property⟩
  have hδ : L.obj.rigidification.second ≪≫
      (Scheme.Modules.pullback (twoAxisSecond A)).mapIso g₁ ≪≫
        M.obj.rigidification.second.symm = Iso.refl _ :=
    structureAut_eq_refl_of_section A.X.hom (unitSection A) (unitSection_comp A)
      (smoothProperConnectedGlobalFunctions _ _ A.X.hom inferInstance inferInstance
        inferInstance ⊤) _
      (secondDiscrepancy_restrict_refl L.obj.rigidification M.obj.rigidification g₁ hfirst)
  refine ⟨isoMk g₁ hfirst ?_⟩
  have h := congrArg Iso.hom hδ
  change (L.obj.rigidification.second.hom ≫
      (Scheme.Modules.pullback (twoAxisSecond A)).map g₁.hom) ≫
        M.obj.rigidification.second.inv = 𝟙 _ at h
  exact (Iso.comp_inv_eq_id _).mp h

end TwoAxisRigidifiedLineBundle

end Langlands.AlgebraicGeometry.Picard
