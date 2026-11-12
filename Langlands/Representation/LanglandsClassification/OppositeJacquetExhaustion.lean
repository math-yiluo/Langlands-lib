import Langlands.Representation.LanglandsClassification.OppositeJacquetUntwist
import Langlands.Representation.LanglandsClassification.OppositeJacquetInductionQuotient
import Langlands.Representation.LanglandsClassification.LanglandsClassificationStatement
import Langlands.Representation.Exponents.LeviSecondAdjointnessStatement

/-! # The final quotient step for opposite Jacquet untwists

Second adjointness turns the constructed untwist and its recovery map into
a quotient from the original standard induction. Temperedness and membership
of the actual exponent parameter in the open chamber remain explicit.
-/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RepresentedParabolic.OppositeStandardJacquetFamily

open GroupScheme

variable {k : Type u} [Field k] [ValuativeRel k] [TopologicalSpace k]
  [IsNonarchimedeanLocalField k] [T2Space k]
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  (i : T.toGrp ⟶ G) (ν : cocharacterLattice T)
  (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
  (hν : IsGenericCocharacter i ν)

local instance exhaustionAmbientPointTopology : TopologicalSpace (rationalPoints G) :=
  RationalPointFamily.pointTopology

variable [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
  (π : SmoothRep.{0, u, v} ℂ (rationalPoints G))

local instance exhaustionLeviPointTopology (J : StandardJacquetFamily.Index i ν) :
    TopologicalSpace (rationalPoints (StandardJacquetFamily.datum i ν hG hi hν J).M) :=
  leviPointTopology (StandardJacquetFamily.datum i ν hG hi hν J).l
    (StandardJacquetFamily.datum i ν hG hi hν J).hl

set_option maxHeartbeats 100000 in
private theorem exists_nonzero_jacquetMap_untwist
    (x : exponents i ν hG hi hν π) (W : UnitaryUntwist i ν hG hi hν π x) :
    let S := StandardJacquetFamily.datum i ν hG hi hν x.1
    letI := leviPointTopology S.l S.hl
    ∃ j : (W.untwist.twist
        (positiveUnramifiedCharacter i ν hG hi hν π x).val.toMonoidHom
        (positiveUnramifiedCharacter_isOpen_ker i ν hG hi hν π x)).representation.IntertwiningMap
        (leviJacquetObject i ν hG hi hν π x.1).representation,
      ∃ w, j w ≠ 0 := by
  let S := StandardJacquetFamily.datum i ν hG hi hν x.1
  let := leviPointTopology S.l S.hl
  let ψ := (positiveUnramifiedCharacter i ν hG hi hν π x).val.toMonoidHom
  have hψ := positiveUnramifiedCharacter_isOpen_ker i ν hG hi hν π x
  let τ := W.untwist.twist ψ hψ
  let e := SmoothRep.equivOfIso W.recovery
  let j := (SmoothRep.hom W.inclusion).comp e.toIntertwiningMap
  have hj : Function.Injective j := W.inclusion_injective.comp e.injective
  have hτirr : τ.IsIrreducible :=
    (SmoothRep.isIrreducible_twist_iff ψ hψ W.untwist).mpr W.untwist_irreducible
  let : Nontrivial τ :=
    CuspidalSupport.QuasicuspidalEmbedding.nontrivial_of_isIrreducible τ.representation hτirr
  obtain ⟨w, hw⟩ := exists_ne (0 : τ)
  refine ⟨j, w, ?_⟩
  intro hz
  apply hw
  apply hj
  exact hz.trans (map_zero j).symm

include hG in
set_option maxHeartbeats 20000 in
private theorem nonempty_adjunctionOfOpposite
    (hAdj : LeviSecondAdjointnessStatement.{u, v})
    (S : ParabolicDatum G) (O : OppositeLeviParabolicData S.p S.l) :
    letI := leviPointTopology S.l S.hl
    Nonempty (leviInductionFunctor.{u, max u v} S.p S.l S.r S.hp S.hr S.hl S.hmul ⊣
      leviJacquetFunctor.{u, max u v} O.inclusion O.levi O.unipotent O.isParabolic
        O.isRadical O.isLevi O.multiplication) := by
  exact hAdj k G hG S.P O.parabolic S.M S.U O.radical S.p S.l S.r
    S.hp S.hl S.hr S.hmul O.inclusion O.levi O.unipotent
    O.isParabolic O.isLevi O.isRadical O.multiplication O.levi_comp O.intersection

include hG in
set_option maxHeartbeats 20000 in
private theorem exists_surjective_inductionOfOpposite
    (hAdj : LeviSecondAdjointnessStatement.{u, v})
    (S : ParabolicDatum G) (O : OppositeLeviParabolicData S.p S.l)
    (σ : letI := leviPointTopology S.l S.hl; SmoothRep.{0, u, v} ℂ (rationalPoints S.M))
    (π : SmoothRep.{0, u, v} ℂ (rationalPoints G)) (hπ : π.IsIrreducible)
    (j : letI := leviPointTopology S.l S.hl
      σ.representation.IntertwiningMap
        ((leviJacquetFunctor O.inclusion O.levi O.unipotent O.isParabolic
          O.isRadical O.isLevi O.multiplication).obj π).representation)
    (hj : ∃ w, j w ≠ 0) :
    letI := leviPointTopology S.l S.hl
    ∃ q : ((leviInductionFunctor S.p S.l S.r S.hp S.hr S.hl S.hmul).obj σ).representation.IntertwiningMap
      π.representation, Function.Surjective q := by
  obtain ⟨adj⟩ := nonempty_adjunctionOfOpposite.{u, v} hG hAdj S O
  exact exists_surjective_leviInduction_of_nonzero_jacquetMap.{u, v}
    S.p S.l S.r S.hp S.hl S.hr S.hmul
    O.inclusion O.levi O.unipotent O.isParabolic O.isLevi O.isRadical O.multiplication
    adj σ π hπ j (by
      intro hz
      obtain ⟨w, hw⟩ := hj
      apply hw
      rw [hz]
      rfl)

set_option maxHeartbeats 50000 in
private theorem exists_surjective_standardInduction_of_nonzero_map
    (hAdj : LeviSecondAdjointnessStatement.{u, v}) (hπ : π.IsIrreducible)
    (J : StandardJacquetFamily.Index i ν)
    (σ :
      let S := StandardJacquetFamily.datum i ν hG hi hν J
      letI := leviPointTopology S.l S.hl
      SmoothRep.{0, u, v} ℂ (rationalPoints S.M))
    (j : σ.representation.IntertwiningMap
      (leviJacquetObject i ν hG hi hν π J).representation) (hj : ∃ w, j w ≠ 0) :
    let S := StandardJacquetFamily.datum i ν hG hi hν J
    letI := leviPointTopology S.l S.hl
    ∃ q : ((leviInductionFunctor S.p S.l S.r S.hp S.hr S.hl S.hmul).obj σ).representation.IntertwiningMap
      π.representation, Function.Surjective q := by
  have h := exists_surjective_inductionOfOpposite.{u, v} hG hAdj
    (StandardJacquetFamily.datum i ν hG hi hν J) (opposite i ν hG hi hν J) σ π hπ
  dsimp +instances only [leviJacquetObject, datum, leviPointTopology] at h j hj ⊢
  with_reducible refine h j ?_
  exact hj

set_option maxHeartbeats 200000 in
/-- The actual recovery isomorphism and Jacquet inclusion give a quotient
from the original standard induction, using the supplied closed second
adjointness proposition. The ambient target keeps its original carrier. -/
theorem exists_surjective_standardInduction_untwist
    (hAdj : LeviSecondAdjointnessStatement.{u, v}) (hπ : π.IsIrreducible)
    (x : exponents i ν hG hi hν π) (W : UnitaryUntwist i ν hG hi hν π x) :
    let S := StandardJacquetFamily.datum i ν hG hi hν x.1
    letI := leviPointTopology S.l S.hl
    ∃ q : ((leviInductionFunctor S.p S.l S.r S.hp S.hr S.hl S.hmul).obj
        (W.untwist.twist (positiveUnramifiedCharacter i ν hG hi hν π x).val.toMonoidHom
          (positiveUnramifiedCharacter_isOpen_ker i ν hG hi hν π x))).representation.IntertwiningMap
        π.representation,
      Function.Surjective q := by
  let S := StandardJacquetFamily.datum i ν hG hi hν x.1
  let := leviPointTopology S.l S.hl
  let τ := W.untwist.twist
    (positiveUnramifiedCharacter i ν hG hi hν π x).val.toMonoidHom
    (positiveUnramifiedCharacter_isOpen_ker i ν hG hi hν π x)
  obtain ⟨j, hj0⟩ := exists_nonzero_jacquetMap_untwist i ν hG hi hν π x W
  have h := exists_surjective_standardInduction_of_nonzero_map i ν hG hi hν π hAdj hπ x.1 τ
  with_reducible refine h j ?_
  exact hj0

/-- Select a quotient map of the original standard induction, retaining its
actual target and the surjectivity certificate. -/
def standardInductionQuotientOfUntwist
    (hAdj : LeviSecondAdjointnessStatement.{u, v}) (hπ : π.IsIrreducible)
    (x : exponents i ν hG hi hν π) (W : UnitaryUntwist i ν hG hi hν π x) :
    let S := StandardJacquetFamily.datum i ν hG hi hν x.1
    letI := leviPointTopology S.l S.hl
    {q : ((leviInductionFunctor S.p S.l S.r S.hp S.hr S.hl S.hmul).obj
        (W.untwist.twist (positiveUnramifiedCharacter i ν hG hi hν π x).val.toMonoidHom
          (positiveUnramifiedCharacter_isOpen_ker i ν hG hi hν π x))).representation.IntertwiningMap
        π.representation // Function.Surjective q} :=
  ⟨(exists_surjective_standardInduction_untwist i ν hG hi hν π hAdj hπ x W).choose,
    (exists_surjective_standardInduction_untwist i ν hG hi hν π hAdj hπ x W).choose_spec⟩

end Langlands.Aubert.General.RepresentedParabolic.OppositeStandardJacquetFamily
