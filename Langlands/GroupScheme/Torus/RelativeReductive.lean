import Langlands.GroupScheme.Torus.RelativeGeometry
import Langlands.GroupScheme.Torus.RelativeFieldComparison
import Langlands.GroupScheme.Torus.ConnectedReductive
import Langlands.GroupScheme.Reductive.ToPseudoReductive
import Langlands.AlgebraicGeometry.SchemeFlatPropertyDescent

/-! # Reductivity of relative tori over an arbitrary base -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme

namespace RelativeTorus

variable {S : Scheme.{u}} {T : GroupScheme S}

/-- A relative torus is affine over its base, by descent from its splitting cover. -/
theorem IsTorus.isAffineHom (hT : IsTorus T) : IsAffineHom T.X.hom := by
  obtain ⟨𝒰, h𝒰⟩ := hT
  have (i : 𝒰.I₀) : Etale (𝒰.f i) := 𝒰.map_prop i
  let 𝒱 : Scheme.Cover Scheme.fppfPrecoverage S :=
    𝒰.changeProp (Q := @Flat ⊓ @LocallyOfFinitePresentation)
      (fun _ => ⟨inferInstance, inferInstance⟩)
  have : MorphismProperty.IsLocalAtTarget (@IsAffineHom : MorphismProperty Scheme.{u})
      Scheme.fppfPrecoverage :=
    Langlands.AlgebraicGeometry.FppfLocal.isLocalAtTarget_fppfPrecoverage _
  exact MorphismProperty.IsLocalAtTarget.of_zeroHypercover 𝒱 fun i => (h𝒰 i).isAffineHom

/-- A relative torus over a field is connected reductive. -/
theorem IsTorus.isConnectedReductive {k : Type u} [Field k]
    {T : GroupScheme (Spec (CommRingCat.of k))} (hT : IsTorus T) :
    IsConnectedReductive T :=
  hT.isTorus.isConnectedReductive_of_fieldSplitting

/-- Every relative torus is reductive, over an arbitrary base scheme. -/
theorem IsTorus.isReductive (hT : IsTorus T) : IsReductive T :=
  ⟨hT.smooth, hT.isAffineHom, fun s =>
    (hT.baseChange (geometricPoint S s)).isConnectedReductive.isPseudoReductive⟩

end RelativeTorus

/-- Relative tori are reductive over every base scheme, in every universe. -/
def RelativeTorusReductiveStatement : Prop :=
  ∀ (S : Scheme.{u}) (T : GroupScheme S), RelativeTorus.IsTorus T → IsReductive T

theorem relativeTorusReductive : RelativeTorusReductiveStatement.{u} :=
  fun _ _ hT => hT.isReductive

end Langlands.GroupScheme
