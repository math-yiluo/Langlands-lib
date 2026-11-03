import Langlands.Representation.Aubert.General.CentralUnitarizedInduction
import Langlands.Representation.Aubert.General.RationalLeviWeylComparison
import Langlands.Representation.Aubert.General.RationalLeviDecomposition
import Langlands.Representation.Aubert.General.RationalUnipotentRegularity
import Langlands.Representation.Unitary.RationalCentralUnitarizer
import Langlands.Representation.Smooth.Schur.Proof

/-! # Central unitarization on the actual rational-point families -/

noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RationalPointFamily

universe u v

open GroupScheme SmoothRep
open Langlands.AlgebraicGeometry.PointTopology

variable {k : Type u} [Field k] [ValuativeRel k] [TopologicalSpace k]
  [IsNonarchimedeanLocalField k]
  {G : GroupScheme (Spec (CommRingCat.of k))}
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] (i : T.toGrp ⟶ G) (ν : cocharacterLattice T)

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
/-- The original point-centralizer comparison places the full abstract
ambient center in every actual standard Levi. -/
theorem center_le_standardLevi (hZ : HasPointCentralizerComparison i)
    (J : Finset (SimpleRoot i ν)) :
    Subgroup.center (RationalPoint k G.X) ≤ levi i ν J :=
  (Subgroup.center_le_centralizer (torusPoints i : Set (RationalPoint k G.X))).trans
    (pointCentralizer_le_levi i ν hZ J)

local instance instRationalCentralUnitarizedInduction1 : TopologicalSpace (RationalPoint k G.X) := pointTopology

variable (hG : IsConnectedReductive G)

local instance instRationalCentralUnitarizedInduction2 : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom

variable [LocallyCompactSpace (RationalPoint k G.X)]
  [NonarchimedeanGroup (RationalPoint k G.X)]
  (hZ : HasPointCentralizerComparison i)
  {S : CommGroupScheme (Spec (CommRingCat.of k))} (s : S.toGrp ⟶ G)
  (hs : GroupScheme.IsCentral s)
  (hindex : (Plancherel.RenardCartan.splitValuationImage s).FiniteIndex)
  (hK : IsCompact ((Plancherel.rationalCommonNormKernel G).subgroupOf
    (Subgroup.center (GroupScheme.rationalPoints G)) :
      Set (Subgroup.center (GroupScheme.rationalPoints G))))
  (J : Finset (SimpleRoot i ν))
  (χ : Subgroup.center (levi i ν J) →* ℂˣ)
  (hχ : IsOpen (χ.ker : Set (Subgroup.center (levi i ν J))))

/-- The actual rational-character valuation image constructs the ambient
positive smooth character, using the inherited inducing central character. -/
def rationalInductionCentralUnitarizingCharacter :
    Induction.SmoothCharacter ℂ (RationalPoint k G.X) := by
  have := hG.smooth
  exact positiveSmoothCharacter
    (CentralUnitarization.rationalCentralUnitarizer G s hs hindex hK
      (normalizedInductionCentralCharacter (levi i ν J)
        (center_le_standardLevi i ν hZ J) χ)
      (isOpen_ker_normalizedInductionCentralCharacter (levi i ν J)
        (center_le_standardLevi i ν hZ J) χ hχ))
    (CentralUnitarization.isOpen_ker_rationalCentralUnitarizer G s hs hindex hK _ _)

omit [LocallyCompactSpace (RationalPoint k G.X)] in
/-- The constructed ambient character is trivial on every compact-limit
subgroup, in particular on each actual standard radical. -/
theorem rationalInductionCentralUnitarizingCharacter_radical
    (U : Subgroup (RationalPoint k G.X))
    (hUc : Jacquet.Localization.IsLimitOfCompactSubgroups U) :
    U ≤ (rationalInductionCentralUnitarizingCharacter
      i ν hG hZ s hs hindex hK J χ hχ).toMonoidHom.ker := by
  have := hG.smooth
  exact positiveSmoothCharacter_radical
    (CentralUnitarization.rationalCentralUnitarizer G s hs hindex hK
      (normalizedInductionCentralCharacter (levi i ν J)
        (center_le_standardLevi i ν hZ J) χ)
      (isOpen_ker_normalizedInductionCentralCharacter (levi i ν J)
        (center_le_standardLevi i ν hZ J) χ hχ))
    (CentralUnitarization.isOpen_ker_rationalCentralUnitarizer G s hs hindex hK
      (normalizedInductionCentralCharacter (levi i ν J)
        (center_le_standardLevi i ν hZ J) χ)
      (isOpen_ker_normalizedInductionCentralCharacter (levi i ν J)
        (center_le_standardLevi i ν hZ J) χ hχ)) U hUc

/-- The actual finite-length inducing object after the restricted ambient
twist. Its finite length follows from irreducibility, without any induction
finite-length preservation premise. -/
def rationalCentralUnitarizedInducingObject
    (σ : FiniteLengthObject.{0, u, max (u + 1) v} ℂ (levi i ν J))
    (hσ : σ.val.IsIrreducible) :
    FiniteLengthObject.{0, u, max (u + 1) v} ℂ (levi i ν J) := by
  let eta := subgroupSmoothCharacter
    (rationalInductionCentralUnitarizingCharacter i ν hG hZ s hs hindex hK J χ hχ)
    (levi i ν J)
  exact ⟨σ.val.twist eta.toMonoidHom eta.isOpen_ker,
    hasFiniteLength_of_isIrreducible
      ((SmoothRep.isIrreducible_twist_iff eta.toMonoidHom eta.isOpen_ker σ.val).mpr hσ)⟩

omit [LocallyCompactSpace (RationalPoint k G.X)] in
theorem rationalCentralUnitarizedInducingObject_isIrreducible
    (σ : FiniteLengthObject.{0, u, max (u + 1) v} ℂ (levi i ν J))
    (hσ : σ.val.IsIrreducible) :
    (rationalCentralUnitarizedInducingObject
      i ν hG hZ s hs hindex hK J χ hχ σ hσ).val.IsIrreducible :=
  by
    let eta := subgroupSmoothCharacter
      (rationalInductionCentralUnitarizingCharacter i ν hG hZ s hs hindex hK J χ hχ)
      (levi i ν J)
    exact (SmoothRep.isIrreducible_twist_iff eta.toMonoidHom eta.isOpen_ker σ.val).mpr hσ

omit [LocallyCompactSpace (RationalPoint k G.X)] in
theorem rationalCentralUnitarizedInducingObject_isAdmissible_iff
    (σ : FiniteLengthObject.{0, u, max (u + 1) v} ℂ (levi i ν J))
    (hσ : σ.val.IsIrreducible) :
    (rationalCentralUnitarizedInducingObject
      i ν hG hZ s hs hindex hK J χ hχ σ hσ).val.IsAdmissible ↔
      σ.val.IsAdmissible :=
  by
    let eta := subgroupSmoothCharacter
      (rationalInductionCentralUnitarizingCharacter i ν hG hZ s hs hindex hK J χ hχ)
      (levi i ν J)
    exact SmoothRep.isAdmissible_twist_iff eta.toMonoidHom eta.isOpen_ker σ.val

variable (hi : IsMaximalSplitTorus i) (hν : IsGenericCocharacter i ν)
  (hStandard : StandardCocharacterStatement.{u})
  (hU : ∀ I, IsClosed (unipotent i ν I : Set (RationalPoint k G.X)))

/-- A unitary action of the full abstract center on the actual induction of
the twisted finite-length inducing object. Compact-limit radical triviality
is derived from the original standard-cocharacter premise. -/
def rationalCentralUnitarizedInductionUnitaryCentralCharacter
    (σ : FiniteLengthObject.{0, u, max (u + 1) v} ℂ (levi i ν J))
    (hσ : σ.val.IsIrreducible)
    (hact : ∀ (z : Subgroup.center (levi i ν J)) (v : σ.val),
      σ.val.representation z v = (χ z : ℂ) • v) :
    UnitaryCentralCharacter
      ((normalizedInductionFunctor
        (isSemidirectDecomposition_of_standardCocharacterStatement
          i ν hStandard hG hi hν J) (hU J)).obj
        (rationalCentralUnitarizedInducingObject
          i ν hG hZ s hs hindex hK J χ hχ σ hσ).val).representation := by
  have := hG.smooth
  let d := isSemidirectDecomposition_of_standardCocharacterStatement
    i ν hStandard hG hi hν J
  let eta := rationalInductionCentralUnitarizingCharacter
    i ν hG hZ s hs hindex hK J χ hχ
  have hetaU : unipotent i ν J ≤ eta.toMonoidHom.ker :=
    rationalInductionCentralUnitarizingCharacter_radical
      i ν hG hZ s hs hindex hK J χ hχ _
      (standardUnipotent_isLimitOfCompactSubgroups_of_standardCocharacterStatement
        i ν hStandard hG hi hν J)
  exact (CentralUnitarization.rationalTwistUnitaryCentralCharacter G s hs hindex hK
    ((normalizedInductionFunctor d (hU J)).obj σ.val).representation
    (normalizedInductionCentralCharacter (levi i ν J)
      (center_le_standardLevi i ν hZ J) χ)
    (isOpen_ker_normalizedInductionCentralCharacter (levi i ν J)
      (center_le_standardLevi i ν hZ J) χ hχ)
    (normalizedInductionCentralCharacter_acts d (hU J)
      (center_le_standardLevi i ν hZ J) σ.val χ hact)).pullbackEquiv
    (normalizedInductionCharacterTwistEquiv d (hU J) eta hetaU σ.val).symm

include hStandard hi hν in
/-- Reducibility of the exact actual normalized induction is preserved. -/
theorem rationalCentralUnitarizedInduction_isIrreducible_iff
    (σ : FiniteLengthObject.{0, u, max (u + 1) v} ℂ (levi i ν J))
    (hσ : σ.val.IsIrreducible) :
    ((normalizedInductionFunctor
      (isSemidirectDecomposition_of_standardCocharacterStatement
        i ν hStandard hG hi hν J) (hU J)).obj
      (rationalCentralUnitarizedInducingObject
        i ν hG hZ s hs hindex hK J χ hχ σ hσ).val).IsIrreducible ↔
      ((normalizedInductionFunctor
        (isSemidirectDecomposition_of_standardCocharacterStatement
          i ν hStandard hG hi hν J) (hU J)).obj σ.val).IsIrreducible :=
  normalizedInduction_isIrreducible_characterTwist_iff _ _
    (rationalInductionCentralUnitarizingCharacter i ν hG hZ s hs hindex hK J χ hχ)
    (rationalInductionCentralUnitarizingCharacter_radical
      i ν hG hZ s hs hindex hK J χ hχ _
      (standardUnipotent_isLimitOfCompactSubgroups_of_standardCocharacterStatement
        i ν hStandard hG hi hν J)) σ.val

variable (hInter : StandardLeviIntersectionStatement.{u})
  (hM : IsClosed (levi i ν J : Set (RationalPoint k G.X)))

include hStandard in
/-- The exact original inside-Levi cuspidality condition is preserved. -/
theorem rationalCentralUnitarizedInducingObject_isCuspidal_iff
    (σ : FiniteLengthObject.{0, u, max (u + 1) v} ℂ (levi i ν J))
    (hσ : σ.val.IsIrreducible) :
    IsCorollaryLeviCuspidal.{u, u, max (u + 1) v} (parabolic i ν) (levi i ν) (unipotent i ν) J hM
        (isSemidirectDecomposition_in_levi i ν hInter hG hi hν J) hU
        (rationalCentralUnitarizedInducingObject
          i ν hG hZ s hs hindex hK J χ hχ σ hσ).val ↔
      IsCorollaryLeviCuspidal.{u, u, max (u + 1) v} (parabolic i ν) (levi i ν) (unipotent i ν) J hM
        (isSemidirectDecomposition_in_levi i ν hInter hG hi hν J) hU σ.val :=
  by
    apply isCorollaryLeviCuspidal_characterTwist_iff.{u, max (u + 1) v, u}
      (parabolic i ν) (levi i ν) (unipotent i ν) J hM
      (isSemidirectDecomposition_in_levi i ν hInter hG hi hν J) hU
      (subgroupSmoothCharacter
        (rationalInductionCentralUnitarizingCharacter i ν hG hZ s hs hindex hK J χ hχ)
        (levi i ν J))
    intro I _ w hw
    exact rationalInductionCentralUnitarizingCharacter_radical
      i ν hG hZ s hs hindex hK J χ hχ _
      (standardUnipotent_isLimitOfCompactSubgroups_of_standardCocharacterStatement
        i ν hStandard hG hi hν _) hw

include hZ hs hindex hK in
/-- For an admissible irreducible inducing object, admissible Schur supplies
its scalar character. The resulting actual twist retains admissibility,
irreducibility, reducibility of induction and exact Levi cuspidality. -/
theorem exists_rationalCentralUnitarizedInducingObject
    (σ : FiniteLengthObject.{0, u, max (u + 1) v} ℂ (levi i ν J))
    (hσ : σ.val.IsIrreducible) (ha : σ.val.IsAdmissible) :
    ∃ τ : FiniteLengthObject.{0, u, max (u + 1) v} ℂ (levi i ν J),
      τ.val.IsIrreducible ∧ τ.val.IsAdmissible ∧
      Nonempty (UnitaryCentralCharacter
        ((normalizedInductionFunctor
          (isSemidirectDecomposition_of_standardCocharacterStatement
            i ν hStandard hG hi hν J) (hU J)).obj τ.val).representation) ∧
      (((normalizedInductionFunctor
          (isSemidirectDecomposition_of_standardCocharacterStatement
            i ν hStandard hG hi hν J) (hU J)).obj τ.val).IsIrreducible ↔
        ((normalizedInductionFunctor
          (isSemidirectDecomposition_of_standardCocharacterStatement
            i ν hStandard hG hi hν J) (hU J)).obj σ.val).IsIrreducible) ∧
      (IsCorollaryLeviCuspidal.{u, u, max (u + 1) v}
          (parabolic i ν) (levi i ν) (unipotent i ν) J hM
          (isSemidirectDecomposition_in_levi i ν hInter hG hi hν J) hU τ.val ↔
        IsCorollaryLeviCuspidal.{u, u, max (u + 1) v}
          (parabolic i ν) (levi i ν) (unipotent i ν) J hM
          (isSemidirectDecomposition_in_levi i ν hInter hG hi hν J) hU σ.val) := by
  obtain ⟨chi, ⟨hlc, hact⟩, _⟩ :=
    admissibleSchur_centralCharacter σ.val.representation ha hσ
  have hchi : IsOpen (chi.ker : Set (Subgroup.center (levi i ν J))) :=
    hlc.isOpen_fiber 1
  refine ⟨rationalCentralUnitarizedInducingObject
    i ν hG hZ s hs hindex hK J chi hchi σ hσ, ?_, ?_, ?_, ?_, ?_⟩
  · exact rationalCentralUnitarizedInducingObject_isIrreducible
      i ν hG hZ s hs hindex hK J chi hchi σ hσ
  · exact (rationalCentralUnitarizedInducingObject_isAdmissible_iff
      i ν hG hZ s hs hindex hK J chi hchi σ hσ).mpr ha
  · exact ⟨rationalCentralUnitarizedInductionUnitaryCentralCharacter
      i ν hG hZ s hs hindex hK J chi hchi hi hν hStandard hU σ hσ hact⟩
  · exact rationalCentralUnitarizedInduction_isIrreducible_iff
      i ν hG hZ s hs hindex hK J chi hchi hi hν hStandard hU σ hσ
  · exact rationalCentralUnitarizedInducingObject_isCuspidal_iff
      i ν hG hZ s hs hindex hK J chi hchi hi hν hStandard hU hInter hM σ hσ

end Langlands.Aubert.General.RationalPointFamily
