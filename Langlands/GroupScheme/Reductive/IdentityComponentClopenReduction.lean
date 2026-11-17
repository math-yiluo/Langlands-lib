import Langlands.GroupScheme.Reductive.IdentityComponentClopenStatement
import Langlands.GroupScheme.Reductive.MonomorphismClosedImmersionStatement
import Langlands.GroupScheme.Reductive.FiberwiseAffinenessStatement
import Langlands.GroupScheme.Reductive.ResidueFiberGeometry
import Langlands.GroupScheme.RelativeIdentityComponent.ClopenQuotientStatement
import Langlands.GroupScheme.RelativeIdentityComponent.QuotientAssembly

/-! # Reduction of the identity-component clopen theorem -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme

/-- The three structural inputs suffice for the exact identity-component
clopen statement over every base scheme. -/
def IdentityComponentClopenReductionStatement : Prop :=
  ReductiveFiberAffinenessStatement.{u} →
    ReductiveMonomorphismClosedImmersionStatement.{u} →
      RelativeIdentityComponent.ClopenQuotientStatement.{u} →
        IdentityComponentClopenStatement.{u}

/-- Conditional assembly using affineness of groups with reductive
residue fibres, closedness of reductive monomorphisms, and representability
of the quotient by a clopen relative identity component. -/
theorem identityComponentClopenReduction : IdentityComponentClopenReductionStatement.{u} := by
  intro hAffine hClosed hQuot S G _ _ _ H i hi hres
  let : IsOpenImmersion i.hom.hom.left := hi.isOpenImmersion
  have hw : H.X.hom = i.hom.hom.left ≫ G.X.hom := (Over.w i.hom.hom).symm
  let : Smooth H.X.hom := by rw [hw]; infer_instance
  let : IsSeparated H.X.hom := by rw [hw]; infer_instance
  let : QuasiCompact H.X.hom := quasiCompact_of_connectedReductive_residueFibers H hres
  let : IsAffineHom H.X.hom := hAffine S H hres
  have hH : IsReductive H :=
    isReductive_of_isAffineHom_of_connectedReductive_residueFibers H hres
  have hiClosed : IsClosedImmersion i.hom.hom.left :=
    hClosed S H G hH inferInstance inferInstance inferInstance i inferInstance
  obtain ⟨D⟩ := hQuot S G H i hi hiClosed
  exact ⟨hH, hiClosed,
    RelativeIdentityComponent.exists_etale_fppfQuotient_of_homogeneousQuotient hi D⟩

end Langlands.GroupScheme
