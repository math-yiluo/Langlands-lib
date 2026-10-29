import Langlands.Representation.Classification.RelativePositiveTotalHeadStatement
import Langlands.Representation.Classification.PositiveTotalHeadCriterionProof
import Langlands.Representation.Classification.RegularLanglandsHeadReduction
import Langlands.Representation.CuspidalSupport.RefinedCuspidalInductionReduction
import Langlands.Representation.Parabolic.SecondAdjointnessProof
import Langlands.Representation.Parabolic.StandardOppositeJacquetAdmissibilityProof
import Langlands.Representation.Parabolic.OppositeRefinementExactnessProof
import Langlands.Representation.Parabolic.OppositeRefinementTransitivityProof
import Langlands.Representation.Unramified.SphericalConstituentExistenceProof

/-! Strong heads of actual GL inductions from equal positive Jacquet counts. -/

noncomputable section

namespace Langlands

open GeneralLinear Geometric RelativeJacquetMultiplicity CategoryTheory Representation

universe uF uV uW

namespace RelativePositiveTotalHead

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}
  (T : F.TopologicalData) {n : ℕ} (B : BlockShape n) (S : BlockRefinement B)

/-- The actual composed opposite Jacquet quotient, with algebraic target. -/
private def jacquetFunctor :
    letI := T.topology
    SmoothRep.{0, uF, uW} ℂ (GeneralLinear n F.Carrier) ⥤
      Rep.{uW} ℂ (refinedLevi F.Carrier B S) := by
  let := T.topology
  exact {
    obj := fun A => Rep.of (T.normalizedComposedOppositeJacquet B S A.representation)
    map := fun f => Rep.ofHom
      (T.normalizedComposedOppositeJacquetMap B S (SmoothRep.hom f))
    map_id := by intros; ext x; rfl
    map_comp := by intros; ext x; rfl }

private instance jacquetFunctor_additive :
    letI := T.topology
    (jacquetFunctor.{uF, uW} T B S).Additive := by
  let := T.topology
  refine ⟨?_⟩
  intro A C f g
  ext x
  obtain ⟨v, rfl⟩ := Parabolic.composedOppositeJacquetMk_surjective B S
    A.representation x
  change Parabolic.composedOppositeJacquetMk B S C.representation
    ((SmoothRep.hom f) v + (SmoothRep.hom g) v) = _
  exact map_add (Parabolic.composedOppositeJacquetMk B S C.representation) _ _

private instance jacquetFunctor_preservesEpimorphisms :
    letI := T.topology
    (jacquetFunctor.{uF, uW} T B S).PreservesEpimorphisms := by
  let := T.topology
  refine ⟨?_⟩
  intro A C f hf
  apply (Rep.epi_iff_surjective _).mpr
  change Function.Surjective (Coinvariants.map _ _
    (Jacquet.restrictMap (SmoothRep.hom f)
      (Parabolic.composedOppositeUnipotent F.Carrier B S)))
  exact coinvariants_map_surjective _ ((SmoothRep.epi_iff_surjective f).mp hf)

end RelativePositiveTotalHead

/-- Second adjointness supplies every quotient-image count bound; nonvanishing
and finite length supply quotient existence for the positive-total criterion. -/
theorem glRelativePositiveTotalHead :
    GLRelativePositiveTotalHeadStatement.{uF, uV, uW} := by
  intro p _ F T
  let := T.topology
  intro n hn B S τ μ hμi hμa hfinite m hm hinner hambient
  let := T.generalLinearTopologicalGroup n
  let := T.leviTopologicalGroup B
  let I := CuspidalJacquetMultiplicity.induced T B μ
  have hIa : IsAdmissible I.ρ :=
    Parabolic.normalizedInductionAdmissibility F T B μ μ.ρ hμa
  let A : SmoothRep.{0, uF, max uF uW} ℂ (GeneralLinear n F.Carrier) :=
    SmoothRep.of I.ρ hIa.1
  let J := RelativePositiveTotalHead.jacquetFunctor.{uF, max uF uW} T B S
  let := hμi
  let : Nontrivial μ := IsSimpleModule.nontrivial
    (MonoidAlgebra ℂ (B.Levi F.Carrier)) μ.ρ.asModule
  let : Nontrivial A :=
    (CuspidalSupport.normalizedParabolicInduced_eval_surjective T B μ.ρ hμa.1).nontrivial
  have hex : ∃ P : SmoothRep.{0, uF, max uF uW} ℂ (GeneralLinear n F.Carrier),
      P.IsIrreducible ∧ ∃ q : A ⟶ P, Function.Surjective (SmoothRep.hom q) := by
    obtain ⟨P, hP, q, hq⟩ :=
      RegularHeadExistence.exists_irreducibleQuotient_of_finiteLength A hfinite
    exact ⟨P, hP, SmoothRep.ofHom q, hq⟩
  apply Classification.positiveTotalHeadCore J A τ m hm hambient hex
  intro P hP q hq
  have hPa : IsAdmissible P.representation := by
    apply Unramified.SphericalExistence.isAdmissible_of_surjective ?_
      (SmoothRep.hom q) hq hIa
    intro H
    obtain ⟨K, hK, hKH, -⟩ :=
      B.exists_compactOpenSubgroup_hasBlockIwahoriFactorization T
        (H.isOpen.mem_nhds H.one_mem)
    exact ⟨K, hK, hKH⟩
  let := hP
  let : Nontrivial P := IsSimpleModule.nontrivial
    (MonoidAlgebra ℂ (GeneralLinear n F.Carrier)) P.representation.asModule
  have hq0 : SmoothRep.hom q ≠ 0 := by
    intro hz
    obtain ⟨v, hv⟩ := exists_ne (0 : P)
    obtain ⟨w, hw⟩ := hq v
    apply hv
    simpa [hz] using hw.symm
  obtain ⟨E, -, -⟩ :=
    Parabolic.normalizedSecondAdjointness.{uF, uW, max uF uW}.1 p F T n hn B
  let i := E μ P.obj hμa hPa (SmoothRep.hom q)
  have hi0 : i ≠ 0 := by
    intro hz
    exact hq0 ((E μ P.obj hμa hPa).injective (hz.trans (map_zero _).symm))
  have hi : Function.Injective i :=
    (Representation.IsIrreducible.injective_or_eq_zero i).resolve_right hi0
  let O := CuspidalJacquetMultiplicity.oppositeJacquet T B P.obj
  have hOa : IsAdmissible O.ρ :=
    Parabolic.isAdmissible_standardOppositeJacquet F T B P P.representation hPa
  have hiq : Function.Injective (T.normalizedRefinedOppositeJacquetMap B S i) :=
    T.normalizedRefinedOppositeJacquetMap_injective B S i hOa.1 hi
  obtain ⟨Etrans, -⟩ :=
    Parabolic.normalizedOppositeRefinementTransitivity p F T n B S P.obj
  let j : (innerJacquet T B S μ).ρ.IntertwiningMap (J.obj P).ρ :=
    Etrans.toIntertwiningMap.comp (T.normalizedRefinedOppositeJacquetMap B S i)
  have hj : Function.Injective j := Etrans.toLinearEquiv.injective.comp hiq
  let f := (J.map q).hom
  let : Epi q := (SmoothRep.epi_iff_surjective q).mpr hq
  have hf : Function.Surjective f :=
    (Rep.epi_iff_surjective (J.map q)).mp inferInstance
  let K := Rep.of f.ker.toRepresentation
  let iK : K.ρ.IntertwiningMap (J.obj A).ρ :=
    { toLinearMap := f.ker.toSubmodule.subtype
      isIntertwining' _ := rfl }
  have hexK : LinearMap.range iK.toLinearMap = LinearMap.ker f.toLinearMap :=
    Submodule.range_subtype _
  obtain ⟨a, c, -, hc, -⟩ :=
    jordanHolderShortExactDecomposition ℂ (refinedLevi F.Carrier B S)
      K (J.obj A) (J.obj P) τ iK f (Submodule.injective_subtype _) hf hexK m hambient
  exact ⟨c, hc, jordanHolderInjectiveMonotonicity ℂ (refinedLevi F.Carrier B S)
    (innerJacquet T B S μ) (J.obj P) τ j hj m c hinner hc⟩

end Langlands
