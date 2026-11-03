import Langlands.Representation.Aubert.General.InductionCentralCharacter
import Langlands.Representation.Aubert.General.CharacterTwistEquivalences
import Langlands.Representation.Aubert.General.JacquetStages
import Langlands.Representation.Unitary.CentralUnitarizer

/-! # Ambient central unitarization of actual normalized induction -/

noncomputable section

open CategoryTheory

namespace Langlands

universe uG uA uV uW uI

namespace UnitaryCentralCharacter

variable {G : Type uG} [Group G] [TopologicalSpace G]
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {W : Type uW} [AddCommGroup W] [Module ℂ W]
  {ρ : Representation ℂ G V} {σ : Representation ℂ G W}

/-- Pull the same central scalar character through an actual equivariant
linear equivalence. -/
def pullbackEquiv (c : UnitaryCentralCharacter σ) (e : ρ.Equiv σ) :
    UnitaryCentralCharacter ρ where
  character := c.character
  isOpen_ker := c.isOpen_ker
  norm_eq_one := c.norm_eq_one
  acts z v := by
    apply e.toLinearEquiv.injective
    change e.toIntertwiningMap (ρ z v) =
      e.toIntertwiningMap ((c.character z : ℂ) • v)
    rw [e.toIntertwiningMap.isIntertwining, map_smul, c.acts]

end UnitaryCentralCharacter

namespace Aubert.General

section PositiveTwist

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- The complex smooth character attached to a positive open-kernel character. -/
def positiveSmoothCharacter (ν : G →* NNRealˣ)
    (hν : IsOpen (ν.ker : Set G)) : Induction.SmoothCharacter ℂ G where
  toMonoidHom := positiveUnitsToComplex.comp ν
  isOpen_ker := by
    apply Subgroup.isOpen_mono (H₁ := ν.ker) ?_ hν
    intro g hg
    change positiveUnitsToComplex (ν g) = 1
    rw [show ν g = 1 from hg, map_one]

/-- Compact-limit radicals are killed by this actual complex character. -/
theorem positiveSmoothCharacter_radical
    (ν : G →* NNRealˣ) (hν : IsOpen (ν.ker : Set G))
    (U : Subgroup G) (hUc : Jacquet.Localization.IsLimitOfCompactSubgroups U) :
    U ≤ (positiveSmoothCharacter ν hν).toMonoidHom.ker := by
  intro u hu
  change positiveUnitsToComplex (ν u) = 1
  rw [positiveCharacter_eq_one_on_compactLimit ν hν U hUc ⟨u, hu⟩, map_one]

end PositiveTwist

section Induction

variable {G : Type uG} [Group G] [TopologicalSpace G] [LocallyCompactSpace G]
  [NonarchimedeanGroup G] {A : Type uA} [CommGroup A]
  {P M U : Subgroup G} (h : IsSemidirectDecomposition P M U)
  (hU : IsClosed (U : Set G)) (hZM : Subgroup.center G ≤ M)
  (q : G →* A) (hq : IsOpen (q.ker : Set G))
  (hK : IsCompact ((q.comp (Subgroup.center G).subtype).ker :
    Set (Subgroup.center G)))
  [(q.comp (Subgroup.center G).subtype).range.FiniteIndex]
  (χ : Subgroup.center M →* ℂˣ)
  (hχ : IsOpen (χ.ker : Set (Subgroup.center M)))

/-- The ambient smooth character that cancels the modulus of the inherited
ambient central character. It is defined on G, before restriction to M. -/
def inductionCentralUnitarizingCharacter : Induction.SmoothCharacter ℂ G :=
  positiveSmoothCharacter
    (CentralUnitarization.centralUnitarizer q hK
      (normalizedInductionCentralCharacter M hZM χ)
      (isOpen_ker_normalizedInductionCentralCharacter M hZM χ hχ))
    (CentralUnitarization.isOpen_ker_centralUnitarizer q hq hK _ _)

/-- The induced representation after the actual restricted ambient twist. -/
def centralUnitarizedInduction (B : SmoothRep.{0, uG, uV} ℂ M) :
    SmoothRep.{0, uG, max uG uV} ℂ G :=
  (normalizedInductionFunctor h hU).obj
    (B.twist
      (subgroupSmoothCharacter
        (inductionCentralUnitarizingCharacter hZM q hq hK χ hχ) M).toMonoidHom
      (subgroupSmoothCharacter
        (inductionCentralUnitarizingCharacter hZM q hq hK χ hχ) M).isOpen_ker)

variable (hUc : Jacquet.Localization.IsLimitOfCompactSubgroups U)

/-- Character multiplication on actual induced functions identifies the
constructed induction with the actual ambient scalar twist. -/
def centralUnitarizedInductionEquiv (B : SmoothRep.{0, uG, uV} ℂ M) :
    (Langlands.twist
      (inductionCentralUnitarizingCharacter hZM q hq hK χ hχ).toMonoidHom
      ((normalizedInductionFunctor h hU).obj B).representation).Equiv
      (centralUnitarizedInduction h hU hZM q hq hK χ hχ B).representation :=
  normalizedInductionCharacterTwistEquiv h hU
    (inductionCentralUnitarizingCharacter hZM q hq hK χ hχ)
    (positiveSmoothCharacter_radical _ _ U hUc) B

/-- The full ambient center acts through a unitary character on the actual
normalized induction of the restricted ambient twist. -/
def centralUnitarizedInductionUnitaryCentralCharacter
    (B : SmoothRep.{0, uG, uV} ℂ M)
    (hact : ∀ (z : Subgroup.center M) (v : B),
      B.representation z v = (χ z : ℂ) • v) :
    UnitaryCentralCharacter
      (centralUnitarizedInduction h hU hZM q hq hK χ hχ B).representation :=
  (CentralUnitarization.unitaryCentralCharacter q hq hK
    ((normalizedInductionFunctor h hU).obj B).representation
    (normalizedInductionCentralCharacter M hZM χ)
    (isOpen_ker_normalizedInductionCentralCharacter M hZM χ hχ)
    (normalizedInductionCentralCharacter_acts h hU hZM B χ hact)).pullbackEquiv
      (centralUnitarizedInductionEquiv h hU hZM q hq hK χ hχ hUc B).symm

include hUc in
/-- Central unitarization by the ambient twist preserves irreducibility of
the actual normalized induction, hence also its reducibility. -/
theorem centralUnitarizedInduction_isIrreducible_iff
    (B : SmoothRep.{0, uG, uV} ℂ M) :
    (centralUnitarizedInduction h hU hZM q hq hK χ hχ B).IsIrreducible ↔
      ((normalizedInductionFunctor h hU).obj B).IsIrreducible :=
  normalizedInduction_isIrreducible_characterTwist_iff h hU
    (inductionCentralUnitarizingCharacter hZM q hq hK χ hχ)
    (positiveSmoothCharacter_radical _ _ U hUc) B

end Induction

section Cuspidality

variable {G : Type uG} [Group G] [TopologicalSpace G] [LocallyCompactSpace G]
  [NonarchimedeanGroup G] {ι : Type uI}
  (P M U : Finset ι → Subgroup G) (J : Finset ι) (hM : IsClosed (M J : Set G))
  (hJ : ∀ I : Finset J, IsSemidirectDecomposition
    ((P (leviIndex J I)).subgroupOf (M J))
    ((M (leviIndex J I)).subgroupOf (M J))
    ((U (leviIndex J I)).subgroupOf (M J)))
  (hU : ∀ I, IsClosed (U I : Set G))
  (hUc : ∀ I, Jacquet.Localization.IsLimitOfCompactSubgroups (U I))

include hUc in
/-- A positive ambient open-kernel twist preserves the exact existing
inside-Levi cuspidality condition; compact limits discharge radical triviality. -/
theorem isCorollaryLeviCuspidal_positiveAmbientTwist_iff
    (ν : G →* NNRealˣ) (hν : IsOpen (ν.ker : Set G))
    (B : SmoothRep.{0, uG, max uG uV} ℂ (M J)) :
    IsCorollaryLeviCuspidal P M U J hM hJ hU
        (B.twist (subgroupSmoothCharacter (positiveSmoothCharacter ν hν) (M J)).toMonoidHom
          (subgroupSmoothCharacter (positiveSmoothCharacter ν hν) (M J)).isOpen_ker) ↔
      IsCorollaryLeviCuspidal P M U J hM hJ hU B := by
  apply isCorollaryLeviCuspidal_characterTwist_iff P M U J hM hJ hU
    (subgroupSmoothCharacter (positiveSmoothCharacter ν hν) (M J))
  intro I _ w hw
  exact positiveSmoothCharacter_radical ν hν (U (leviIndex J I))
    (hUc (leviIndex J I)) hw

end Cuspidality

end Aubert.General
end Langlands
