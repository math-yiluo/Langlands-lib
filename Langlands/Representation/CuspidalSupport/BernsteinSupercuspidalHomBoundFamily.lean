import Langlands.Representation.CuspidalSupport.BernsteinSupercuspidalHomBound
import Langlands.GroupScheme.Rational.StandardCocharacterProof
import Langlands.GroupScheme.Rational.StandardLeviIntersectionProof
import Langlands.GroupScheme.Rational.RelativeRootSystemProof
import Langlands.Representation.Aubert.General.CuspidalRemainderProjection

/-! # The Hom bound for standard cuspidal data of a standard family (Renard VI.5.4) -/

noncomputable section

set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency.types false

universe uF uV

open CategoryTheory

namespace Langlands.CuspidalSupport.HomBound

section Bernstein

open _root_.AlgebraicGeometry GroupScheme Group.RelativeWeylIndexing
open Langlands.Aubert.General Langlands.Aubert.General.RationalPointFamily
open Langlands.AlgebraicGeometry.PointTopology
open scoped CategoryTheory.MonObj

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  {T : CommGroupScheme (Spec (CommRingCat.of F))}
  (i : T.toGrp ⟶ G) (ν : cocharacterLattice T)

local instance homBoundAmbientAffine : IsAffine G.X.left :=
  isAffine_of_isAffineHom G.X.hom
local instance homBoundAmbientTopology : TopologicalSpace (rationalPoints G) :=
  pointTopology
local instance homBoundLeviClosedImmersion (I : Finset (SimpleRoot i ν)) :
    IsClosedImmersion (Standard.leviHom i ν (rootSet i ν I)).hom.hom.left :=
  Standard.isClosedSubgroup_leviHom i ν (rootSet i ν I)
local instance homBoundLeviAffine (I : Finset (SimpleRoot i ν)) :
    IsAffine (bernsteinLeviScheme i ν I).X.left :=
  isAffine_of_isAffineHom (Standard.leviHom i ν (rootSet i ν I)).hom.hom.left
local instance homBoundLeviTopology (I : Finset (SimpleRoot i ν)) :
    TopologicalSpace (rationalPoints (bernsteinLeviScheme i ν I)) :=
  rationalPointTopology F (bernsteinLeviScheme i ν I).X

variable [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
  (family : BernsteinStandardFamily i ν)

/-- The set `W(ρ, ρ')` of Renard VI.5.4 for cuspidal data `a = (M, ρ)` and
`a' = (M', ρ')`: Weyl elements with a representative `n` such that
`n M n⁻¹ = M'` and `ρ' ∘ Ad(n) ≃ ρ` as representations of `M(F)`. This is
literally the second set of `BernsteinSupercuspidalInductionBoundsStatement`. -/
def bernsteinMatchingWeyl (a a' : BernsteinCuspidalDatum.{uF, uV} i ν family) :
    Set (Weyl i) :=
  {w : Weyl i | ∃ (n : Group.RelativeWeyl.normalizer (torusPoints i))
      (h : (levi i ν a.roots).map
        (MulAut.conj (n : rationalPoints G) : rationalPoints G →* rationalPoints G) =
        levi i ν a'.roots),
    (QuotientGroup.mk n : Weyl i) = w ∧
      ∃ e : bernsteinLiteralLeviRep i ν a.roots a.representation ≃ₗ[ℂ]
          bernsteinLiteralLeviRep i ν a'.roots a'.representation,
        ∀ (m : levi i ν a.roots) (x : bernsteinLiteralLeviRep i ν a.roots a.representation),
          e ((bernsteinLiteralLeviRep i ν a.roots a.representation).representation m x) =
            (bernsteinLiteralLeviRep i ν a'.roots a'.representation).representation
              (Group.RelativeWeyl.conjugationEquiv (n : rationalPoints G)
                (levi i ν a.roots) (levi i ν a'.roots) h m) (e x)}

/-- Renard VI.5.4, Hom bound before passing to cosets: with the
proper-standard exclusion input, the intertwiners between the inductions of
two standard cuspidal data `a = (M_I, ρ)` and `a' = (M_J, ρ')` number at most
the minimal representatives `w` of `W_J \ W / W_I` lying in `W(ρ, ρ')`. -/
theorem bernsteinInduction_rank_intertwiningMap_le_card_minimal
    [Mono i.hom.hom.left] [Fintype (SimpleRoot i ν)]
    (hN : HasPointNormalizerComparison i) (hZ : HasPointCentralizerComparison i)
    {C : CoxeterMatrix (SimpleRoot i ν)} (cs : ActualCoxeterSystem (torusPoints i) C)
    (hIdent : actualLeviWeylIdentification (torusPoints i) (levi i ν) cs)
    (hLength : RootLengthComparison i ν hN hZ cs)
    (hExclude : PointLeviStandardInductionCuspidalExclusion.{uF, uV}
      i ν standardLeviIntersection family.connectedReductive family.maximalSplitTorus
      family.genericCocharacter family.closedLevi family.closedUnipotent)
    (a a' : BernsteinCuspidalDatum.{uF, uV} i ν family) :
    Module.rank ℂ ((bernsteinInduction i ν family a).representation.IntertwiningMap
        (bernsteinInduction i ν family a').representation) ≤
      Nat.card {w : Weyl i // IsMinimal cs a'.roots a.roots w ∧
        w ∈ bernsteinMatchingWeyl i ν family a a'} := by
  classical
  have hG := family.connectedReductive
  have hi := family.maximalSplitTorus
  have hν := family.genericCocharacter
  have : T2Space F := Langlands.HarmonicAnalysis.GeneralLocalField.t2Space F
  have : T2Space (rationalPoints G) := rationalPoint_t2Space F G
  have hRoots : HasRelativeRootSystem i := relativeRootSystem F G hG T i hi
  obtain ⟨hW, -⟩ := exists_rootSpanPointCoxeterSystem i ν hN hZ hG hi hRoots hν
  let : Fintype (Weyl i) := Fintype.ofFinite _
  let ρ := bernsteinLiteralLeviRep i ν a.roots a.representation
  let ρ' := bernsteinLiteralLeviRep i ν a'.roots a'.representation
  have hρ : ρ.IsIrreducible :=
    (isIrreducible_comp_continuousMulEquiv_iff a.representation.representation
      (leviRationalPointHomeomorph i ν a.roots).symm).mpr a.irreducible
  have hρ' : ρ'.IsIrreducible :=
    (isIrreducible_comp_continuousMulEquiv_iff a'.representation.representation
      (leviRationalPointHomeomorph i ν a'.roots).symm).mpr a'.irreducible
  have hcσ : Langlands.Aubert.General.IsLeviCuspidal (parabolic i ν) (levi i ν) (unipotent i ν)
      family.closedUnipotent a.roots (family.closedLevi a.roots)
      (isSemidirectDecomposition_in_levi i ν standardLeviIntersection hG hi hν a.roots)
      (SmoothRep.universeLift.{uF + 1} ρ) := by
    let := (family.closedLevi a.roots).locallyCompactSpace
    exact IsCuspidalFor.of_surjective_intertwiner a.cuspidal
      (SmoothRep.universeLiftEquiv.{uF + 1} ρ).toIntertwiningMap
      (SmoothRep.universeLiftEquiv.{uF + 1} ρ).surjective
  have hcτ : Langlands.Aubert.General.IsLeviCuspidal (parabolic i ν) (levi i ν) (unipotent i ν)
      family.closedUnipotent a'.roots (family.closedLevi a'.roots)
      (isSemidirectDecomposition_in_levi i ν standardLeviIntersection hG hi hν a'.roots)
      (SmoothRep.universeLift.{uF + 1} ρ') := by
    let := (family.closedLevi a'.roots).locallyCompactSpace
    exact IsCuspidalFor.of_surjective_intertwiner a'.cuspidal
      (SmoothRep.universeLiftEquiv.{uF + 1} ρ').toIntertwiningMap
      (SmoothRep.universeLiftEquiv.{uF + 1} ρ').surjective
  have h := rank_normalizedInduction_intertwiningMap_le i ν hN hZ cs
    standardCocharacter standardLeviIntersection hG hi hν family.closedLevi
    family.closedUnipotent hRoots hIdent hLength hExclude
    (SmoothRep.universeLift.{uF + 1} ρ) ((SmoothRep.isIrreducible_universeLift_iff ρ).mpr hρ)
    hcσ (SmoothRep.universeLift.{uF + 1} ρ') ((SmoothRep.isIrreducible_universeLift_iff ρ').mpr hρ')
    hcτ (fun w => w ∈ bernsteinMatchingWeyl i ν family a a') (fun n hn ⟨φ⟩ => by
      obtain ⟨hmap, e, he⟩ :=
        exists_conjugation_linearEquiv_of_iso_universeLift (n : rationalPoints G) hn φ
      exact ⟨n, hmap, rfl, e, he⟩)
  have key := (intertwiningMapLinearCongr
    (normalizedInductionUniverseLiftEquiv.{uF, uV, uF + 1}
      (family.decomposition a.roots) (family.closedUnipotent a.roots) ρ)
    (normalizedInductionUniverseLiftEquiv.{uF, uV, uF + 1}
      (family.decomposition a'.roots) (family.closedUnipotent a'.roots) ρ')).lift_rank_eq
  refine Cardinal.lift_le_nat_iff.mp (key.trans_le ?_)
  exact Cardinal.lift_le_nat_iff.mpr h

/-- The Hom bound of `bernsteinInduction_rank_intertwiningMap_le_card_minimal`
with the proper-standard exclusion input supplied by the rational extraction
inputs statement. -/
theorem bernsteinInduction_rank_intertwiningMap_le_card_minimal_of_inputs
    [Mono i.hom.hom.left]
    (hInputs : RationalCuspidalExtractionInputsStatement.{uF, uV})
    (hN : HasPointNormalizerComparison i) (hZ : HasPointCentralizerComparison i)
    {C : CoxeterMatrix (SimpleRoot i ν)} (cs : ActualCoxeterSystem (torusPoints i) C)
    (hIdent : actualLeviWeylIdentification (torusPoints i) (levi i ν) cs)
    (hLength : RootLengthComparison i ν hN hZ cs)
    (a a' : BernsteinCuspidalDatum.{uF, uV} i ν family) :
    Module.rank ℂ ((bernsteinInduction i ν family a).representation.IntertwiningMap
        (bernsteinInduction i ν family a').representation) ≤
      Nat.card {w : Weyl i // IsMinimal cs a'.roots a.roots w ∧
        w ∈ bernsteinMatchingWeyl i ν family a a'} := by
  have hG := family.connectedReductive
  have hi := family.maximalSplitTorus
  have : T2Space F := Langlands.HarmonicAnalysis.GeneralLocalField.t2Space F
  have : T2Space (rationalPoints G) := rationalPoint_t2Space F G
  have hRoots : HasRelativeRootSystem i := relativeRootSystem F G hG T i hi
  let := simpleRelativeRootFintype i hRoots hi.isSplitSubtorus.1 ν
  obtain ⟨-, hExclude⟩ := hInputs F G hG T i hi ν family.genericCocharacter
    standardCocharacter standardLeviIntersection hRoots hN hZ family.closedUnipotent
    family.closedLevi
  exact bernsteinInduction_rank_intertwiningMap_le_card_minimal i ν family hN hZ cs hIdent
    hLength hExclude a a'

end Bernstein

end Langlands.CuspidalSupport.HomBound
