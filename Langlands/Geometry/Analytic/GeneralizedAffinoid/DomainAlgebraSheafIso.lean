import Langlands.Geometry.Analytic.GeneralizedAffinoid.DomainAlgebraSheaf
import Langlands.Geometry.Analytic.GeneralizedAffinoid.DomainAlgebraComparison

/-! # Stored domain algebras are the finite rational descent extension -/

noncomputable section

universe u

namespace Langlands.Analytic.PresentedAffinoidAlgebra.Domain

open CategoryTheory CategoryTheory.Limits Opposite

variable (K : Type u) [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  (A : PresentedAffinoidAlgebra K)

/-- The canonical comparison, regarded as a morphism of the proved sheaves. -/
def algebraToExtensionSheaf :
    algebraSheaf K A ⟶ algebraSheafExtension K A :=
  ObjectProperty.homMk (algebraToExtensionNat K A)

/-- The actual comparison is an isomorphism: its restriction to every rational
image is an isomorphism, and fully faithful sheaf restriction reflects this. -/
instance algebraToExtensionSheaf_isIso : IsIso (algebraToExtensionSheaf K A) := by
  let F := RationalChart.domainSheafRestriction K A (CommAlgCat K)
  have : ∀ d : (RationalChart K A)ᵒᵖ,
      IsIso ((F.map (algebraToExtensionSheaf K A)).hom.app d) := by
    intro d
    change IsIso (algebraToExtension K A d.unop.toDomain)
    infer_instance
  have : IsIso ((sheafToPresheaf (RationalChart.finiteRationalTopology K A)
      (CommAlgCat K)).map (F.map (algebraToExtensionSheaf K A))) := by
    change IsIso (F.map (algebraToExtensionSheaf K A)).hom
    exact NatIso.isIso_of_isIso_app _
  have : IsIso (F.map (algebraToExtensionSheaf K A)) :=
    isIso_of_reflects_iso _ (sheafToPresheaf
      (RationalChart.finiteRationalTopology K A) (CommAlgCat K))
  exact isIso_of_reflects_iso (algebraToExtensionSheaf K A) F

/-- The actual stored algebra sheaf is canonically isomorphic to the explicit
finite-rational-descent sheaf. -/
def algebraSheafExtensionIso :
    algebraSheaf K A ≅ algebraSheafExtension K A :=
  asIso (algebraToExtensionSheaf K A)

@[simp]
theorem algebraSheafExtensionIso_hom :
    (algebraSheafExtensionIso K A).hom.hom = algebraToExtensionNat K A := rfl

/-- The stored presented algebra of any full domain is its finite rational
descent algebra, by the canonical map using the original bounded restrictions. -/
def algebraSectionIso (U : Domain K A) :
    CommAlgCat.of K U.algebra ≅ (algebraSheafExtension K A).obj.obj (op U) :=
  ((sheafToPresheaf (finiteDomainTopology K A) (CommAlgCat K)).mapIso
    (algebraSheafExtensionIso K A)).app (op U)

@[simp]
theorem algebraSectionIso_hom (U : Domain K A) :
    (algebraSectionIso K A U).hom = algebraToExtension K A U := rfl

instance algebraToExtension_isIso (U : Domain K A) :
    IsIso (algebraToExtension K A U) := by
  rw [← algebraSectionIso_hom]
  infer_instance

@[reassoc (attr := simp)]
theorem algebraSectionIso_hom_projection (U : Domain K A)
    (i : Fin (finiteRationalCoverData U).size) :
    (algebraSectionIso K A U).hom ≫ sectionProjection K A U i =
      CommAlgCat.ofHom ((finiteRationalCoverData U).map i).restriction.toAlgHom :=
  algebraToExtension_projection K A U i

/-- The canonical section identifications commute with every original bounded
restriction, so they identify the entire presheaves as well as their values. -/
@[reassoc]
theorem algebraSectionIso_naturality {U V : Domain K A} (f : U ⟶ V) :
    CommAlgCat.ofHom f.restriction.toAlgHom ≫ (algebraSectionIso K A U).hom =
      (algebraSectionIso K A V).hom ≫
        (algebraSheafExtension K A).obj.map f.op :=
  algebraToExtension_naturality f

/-- The inverse canonical identification recovers stored elements from their
finite rational descent data. -/
def algebraSectionEquiv (U : Domain K A) :
    U.algebra ≃ₐ[K] (algebraSheafExtension K A).obj.obj (op U) :=
  CommAlgCat.algEquivOfIso (algebraSectionIso K A U)

@[simp]
theorem algebraSectionEquiv_apply (U : Domain K A) (a : U.algebra) :
    algebraSectionEquiv K A U a = algebraToExtension K A U a := rfl

end Langlands.Analytic.PresentedAffinoidAlgebra.Domain
