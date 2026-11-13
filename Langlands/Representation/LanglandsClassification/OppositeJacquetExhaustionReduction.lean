import Langlands.Representation.LanglandsClassification.OppositeJacquetExhaustion
import Langlands.Representation.LanglandsClassification.OppositeJacquetUntwistSelectionStatement

/-! # Exact exhaustion from a tempered opposite-Jacquet untwist

The actual root presentation and realizing unramified character assemble a
Langlands triplet from an untwist whose temperedness and chamber membership
are supplied. This isolates the remaining exponent-selection argument.
-/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme


namespace OppositeStandardJacquetFamily

variable {k : Type u} [Field k] [ValuativeRel k] [TopologicalSpace k]
  [IsNonarchimedeanLocalField k] [T2Space k]
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  (i : T.toGrp ⟶ G) (ν : cocharacterLattice T)
  (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
  (hν : IsGenericCocharacter i ν)

local instance reductionAmbientPointTopology : TopologicalSpace (rationalPoints G) :=
  RationalPointFamily.pointTopology

variable [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
  (π : SmoothRep.{0, u, v} ℂ (rationalPoints G))
  [Mono i.hom.hom.left] (D : RelativeRootReflectionData i)

set_option maxHeartbeats 200000 in
/-- The original standard presentation, the supplied temperedness, and the
real-part identity for the realizing character give precisely a Langlands
triplet on the original standard Levi and split component. -/
theorem isLanglandsTriplet_untwist
    (x : exponents i ν hG hi hν π) (W : UnitaryUntwist i ν hG hi hν π x)
    (hTemp :
      let S := StandardJacquetFamily.datum i ν hG hi hν x.1
      haveI := S.hl.isConnectedReductive.isAffineHom
      letI := leviPointTopology S.l S.hl
      haveI := leviPoints_locallyCompactSpace S.p S.l S.hp S.hl
      haveI := leviPoints_nonarchimedeanGroup S.p S.l S.hp S.hl
      IsNormalizedExponentTempered S.hl.isConnectedReductive W.untwist)
    (hCh : realPart i ν hG hi hν π x ∈
      restrictedCorootChamber i ν x.1.val
        (Additive.ofMul (component i ν hG hi hν x.1).g) D) :
    let S := StandardJacquetFamily.datum i ν hG hi hν x.1
    let C := component i ν hG hi hν x.1
    IsLanglandsTriplet i ν D S.p S.l C.a S.hp S.hl C.ha x.1.val
      (Additive.ofMul C.g) W.untwist (positiveUnramifiedCharacter i ν hG hi hν π x) := by
  refine ⟨?_, W.untwist_irreducible, hTemp, ?_⟩
  · exact (rootPresentation i ν hG hi hν x.1).isCompatible
  · rw [realPart_positiveUnramifiedCharacter]
    exact hCh

end OppositeStandardJacquetFamily

set_option maxHeartbeats 200000 in
/-- The exact exhaustive component of the Langlands classification follows
from the actual tempered-untwist selection obligation and second adjointness.
The original ambient carrier and the original fixed standard data are retained. -/
theorem langlandsQuotientExhaustive_of_selectedUnitaryUntwist
    (hSelect : OppositeJacquetUntwistSelectionStatement.{u, v})
    (hAdj : LeviSecondAdjointnessStatement.{u, v}) :
    LanglandsQuotientExhaustiveStatement.{u, v} := by
  intro k _ _ _ _ _ G hG
  have := hG.isAffineHom
  let : TopologicalSpace (rationalPoints G) := RationalPointFamily.pointTopology
  intro _ _ T i _ ν D hi hν hmin π hπ
  obtain ⟨x, W, hTemp, hCh⟩ :=
    hSelect k G hG T i ν D hi hν hmin π hπ
  let S := StandardJacquetFamily.datum i ν hG hi hν x.1
  let C := OppositeStandardJacquetFamily.component i ν hG hi hν x.1
  have := S.hl.isConnectedReductive.isAffineHom
  let := leviPointTopology S.l S.hl
  have := leviPoints_locallyCompactSpace S.p S.l S.hp S.hl
  have := leviPoints_nonarchimedeanGroup S.p S.l S.hp S.hl
  refine ⟨S.P, S.M, S.U, C.A, S.p, S.l, S.r, C.a,
    S.hp, S.hl, S.hr, S.hmul, C.ha, x.1.val, Additive.ofMul C.g,
    W.untwist, OppositeStandardJacquetFamily.positiveUnramifiedCharacter
      i ν hG hi hν π x, ?_, ?_⟩
  · exact OppositeStandardJacquetFamily.isLanglandsTriplet_untwist
      i ν hG hi hν π D x W hTemp hCh
  · have h := OppositeStandardJacquetFamily.exists_surjective_standardInduction_untwist
      i ν hG hi hν π hAdj hπ x W
    with_reducible exact h

end Langlands.Aubert.General.RepresentedParabolic
