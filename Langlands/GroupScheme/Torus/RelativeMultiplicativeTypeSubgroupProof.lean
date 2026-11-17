import Langlands.GroupScheme.Torus.RelativeMultiplicativeTypeSubgroupReduction
import Langlands.GroupScheme.Torus.GroupLikeHopfBaseChange
import Langlands.GroupScheme.Torus.HopfDiagonalizableLocality
import Langlands.Algebra.BialgebraLocalization
import Langlands.Algebra.GroupLikeSpanLocal

/-! # Flat finitely presented closed subgroups of multiplicative-type groups -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped TensorProduct

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme.HopfCoordinates

/-- The standard group algebra commutes with scalar extension as a Hopf
algebra, using the actual spectrum and diagonalizable-group comparisons. -/
def groupAlgebraBaseChangeEquiv (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
    (M : Type u) [AddCommGroup M] :
    S ⊗[R] AddMonoidAlgebra R M ≃ₐc[S] AddMonoidAlgebra S M := by
  let b := Spec.map (CommRingCat.ofHom (algebraMap R S))
  let e : (hopfSpec (CommRingCat.of S)).obj
        (op (scalarExtension R S (AddMonoidAlgebra R M))) ≅
      (hopfSpec (CommRingCat.of S)).obj
        (op (Diagonalizable.hopfAlgebra (CommRingCat.of S) M)) :=
    (baseChangeSpecIso R S (AddMonoidAlgebra R M)).symm ≪≫
      (GroupScheme.baseChange b).mapIso (Diagonalizable.hopfSpecIso (CommRingCat.of R) M) ≪≫
      Diagonalizable.baseChangeIso b M ≪≫
      (Diagonalizable.hopfSpecIso (CommRingCat.of S) M).symm
  exact CommHopfAlgCat.ofIso (hopfSpec.fullyFaithful.preimageIso e).unop.symm

/-- The local reconstruction theorem supplies a finitely generated
abelian character group and an actual group-algebra equivalence. -/
theorem exists_groupAlgebra_model_of_isLocalRing
    (R : CommRingCat.{u}) [IsLocalRing R] (A : CommHopfAlgCat.{u} R)
    [Module.Flat R A] [Algebra.FinitePresentation R A]
    (hspan : Submodule.span R {a : A | IsGroupLikeElem R a} = ⊤) :
    ∃ (M : Type u) (_ : AddCommGroup M) (_ : AddGroup.FG M),
      Nonempty (A ≃ₐc[R] AddMonoidAlgebra R M) := by
  let : Group.FG (GroupLike R A) := Langlands.GroupLikeSpan.groupFG hspan
  refine ⟨Additive (GroupLike R A), inferInstance, inferInstance, ?_⟩
  exact ⟨(Langlands.GroupLikeSpan.bialgEquiv hspan).symm.trans
    (_root_.MonoidAlgebra.toAdditiveBialgEquiv R R (GroupLike R A))⟩

/-- A diagonalizable model at a prime extends to an actual principal
neighborhood when the original Hopf algebra is finitely presented. -/
theorem exists_away_isDiagonalizable_of_local_model
    (R : CommRingCat.{u}) (A : CommHopfAlgCat.{u} R)
    [Algebra.FinitePresentation R A] (p : PrimeSpectrum R)
    (M : Type u) [AddCommGroup M] [AddGroup.FG M]
    (eₚ : Localization.AtPrime p.asIdeal ⊗[R] A ≃ₐc[Localization.AtPrime p.asIdeal]
      AddMonoidAlgebra (Localization.AtPrime p.asIdeal) M) :
    ∃ f : R, f ∉ p.asIdeal ∧ RelativeMultiplicativeType.IsDiagonalizable
      ((hopfSpec (CommRingCat.of (Localization.Away f))).obj
        (op (scalarExtension R (Localization.Away f) A))) := by
  let B := AddMonoidAlgebra R M
  let : Algebra.FinitePresentation R B :=
    Diagonalizable.finitePresentation_addGroupAlgebra R M
  let e := eₚ.trans (groupAlgebraBaseChangeEquiv R (Localization.AtPrime p.asIdeal) M).symm
  obtain ⟨f, hf, ⟨ef⟩⟩ := Langlands.BialgebraSpreading.exists_away_bialgEquiv
    p.asIdeal.primeCompl (Localization.AtPrime p.asIdeal) A B e
  refine ⟨f, hf, ?_⟩
  exact isDiagonalizable_of_bialgEquiv (CommRingCat.of (Localization.Away f))
    (scalarExtension R (Localization.Away f) A)
    (ef.trans (groupAlgebraBaseChangeEquiv R (Localization.Away f) M))

end Langlands.GroupScheme.HopfCoordinates

namespace Langlands.GroupScheme

/-- A flat finitely presented Hopf algebra spanned by group-like elements
has a spectrum of multiplicative type. -/
theorem flatGroupLikeHopfMultiplicativeType :
    FlatGroupLikeHopfMultiplicativeTypeStatement.{u} := by
  intro R A hflat hfp hspan
  let : Module.Flat R A := hflat
  let : Algebra.FinitePresentation R A := hfp
  apply HopfCoordinates.isMultiplicativeType_of_forall_exists_away R A
  intro p
  let Rₚ := Localization.AtPrime p.asIdeal
  let Aₚ : CommHopfAlgCat.{u} Rₚ := HopfCoordinates.scalarExtension R Rₚ A
  have hspanₚ : Submodule.span Rₚ {a : Aₚ | IsGroupLikeElem Rₚ a} = ⊤ :=
    HopfCoordinates.span_groupLike_baseChange hspan
  obtain ⟨M, _, _, ⟨eₚ⟩⟩ := HopfCoordinates.exists_groupAlgebra_model_of_isLocalRing
    (CommRingCat.of Rₚ) Aₚ hspanₚ
  exact HopfCoordinates.exists_away_isDiagonalizable_of_local_model R A p M eₚ

/-- Flat locally finitely presented closed subgroups of groups of
multiplicative type are of multiplicative type, over every base scheme. -/
theorem relativeMultiplicativeTypeClosedSubgroup :
    RelativeMultiplicativeTypeClosedSubgroupStatement.{u} :=
  relativeMultiplicativeTypeClosedSubgroup_of_flatGroupLikeHopf
    flatGroupLikeHopfMultiplicativeType

end Langlands.GroupScheme
