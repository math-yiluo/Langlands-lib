import Langlands.Representation.Exponents.TemperedJacquetStructure
import Langlands.Representation.Exponents.TemperedUnitaryJacquetEmbedding
import Langlands.Representation.CuspidalSupport.GroupTransport
import Langlands.Representation.Compact.SurjectivityProof
import Langlands.Representation.Smooth.Admissibility.CofinalProof
import Langlands.Representation.Smooth.Schur.Proof

/-! # Admissibility and full-center characters of unitary Jacquet quotients -/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme

variable {k : Type u} [Field k] [ValuativeRel k] [TopologicalSpace k]
  [IsNonarchimedeanLocalField k] [T2Space k]
  {G P M U : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]

local instance quotientStructureAmbientTopology : TopologicalSpace (rationalPoints G) :=
  RationalPointFamily.pointTopology

variable [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
  (p : P ⟶ G) (l : M ⟶ P) (r : U ⟶ P)
  (hp : IsParabolicSubgroup p) (hl : IsRationalLeviSubgroup l)
  (hr : LeviSubgroup.IsGeometricUnipotentRadical r)
  (hmul : IsIso (subgroupMultiplication l r))
  {A : CommGroupScheme (Spec (CommRingCat.of k))} {a : A.toGrp ⟶ M}
  (ha : IsSplitComponent a)
  {hG : IsConnectedReductive G} {π : SmoothRep.{0, u, v} ℂ (rationalPoints G)}

namespace UnitaryJacquetIrreducibleQuotientData

/-- A selected irreducible quotient of a tempered source's unitary Jacquet
part is admissible on the actual Levi points. No temperedness of the unitary
Jacquet module or compactness of the parabolic quotient is assumed. -/
theorem isAdmissible
    (htemp : IsNormalizedExponentTempered hG π)
    (D : UnitaryJacquetIrreducibleQuotientData p l r hp hl hr hmul ha π) :
    letI := leviPointTopology l hl
    D.quotient.IsAdmissible := by
  let := hl.isConnectedReductive.isAffineHom
  let : TopologicalSpace (rationalPoints M) := leviPointTopology l hl
  let : LocallyCompactSpace (rationalPoints M) := leviPoints_locallyCompactSpace p l hp hl
  let : NonarchimedeanGroup (rationalPoints M) :=
    leviPoints_nonarchimedeanGroup p l hp hl
  let J := (leviJacquetFunctor p l r hp hr hl hmul).obj π
  have hJ : J.IsAdmissible :=
    isAdmissible_comp_continuousMulEquiv
      ((jacquetFunctor p l r hp hr hl hmul).obj π).representation
      (leviPointsEquiv p l hp hl)
      (htemp.isAdmissible_jacquetFunctor_obj p l r hp hl hr hmul ha)
  let f := SmoothRep.hom (unitaryJacquetQuotientFullMap p l r hp hl hr hmul ha π
    (htemp.unitaryJacquetPart_isCompl p l r hp hl hr hmul ha) D)
  have hf : Function.Surjective f :=
    unitaryJacquetQuotientFullMap_surjective p l r hp hl hr hmul ha π
      (htemp.unitaryJacquetPart_isCompl p l r hp hl hr hmul ha) D
  refine ⟨D.quotient.isSmooth, ?_⟩
  intro H
  obtain ⟨K, hK, hKH⟩ := compactOpenSubgroupBasis (rationalPoints M)
    (H : Set (rationalPoints M)) (H.isOpen.mem_nhds H.one_mem)
  have : Module.Finite ℂ (fixedVectors J.representation K.toSubgroup) := hJ.2 K
  have : Module.Finite ℂ (fixedVectors D.quotient.representation K.toSubgroup) :=
    Module.Finite.of_surjective
      (Compact.fixedVectorMap J.representation D.quotient.representation f K.toSubgroup)
      (Compact.fixedVectorSurjectivity _ _ _ _ _ J.isSmooth D.quotient.isSmooth K hK f hf)
  exact finite_fixedVectors_of_le (ρ := D.quotient.representation)
    (show K.toSubgroup ≤ H.toSubgroup from hKH)

/-- The actual irreducible quotient has a unique locally constant scalar
character of the full center of the Levi point group. -/
theorem existsUnique_centralCharacter
    (htemp : IsNormalizedExponentTempered hG π)
    (D : UnitaryJacquetIrreducibleQuotientData p l r hp hl hr hmul ha π) :
    letI := leviPointTopology l hl
    ∃! ω : Subgroup.center (rationalPoints M) →* ℂˣ,
      IsLocallyConstant (ω : Subgroup.center (rationalPoints M) → ℂˣ) ∧
        D.quotient.HasCentralCharacter ω := by
  let := hl.isConnectedReductive.isAffineHom
  let : TopologicalSpace (rationalPoints M) := leviPointTopology l hl
  let : LocallyCompactSpace (rationalPoints M) := leviPoints_locallyCompactSpace p l hp hl
  let : NonarchimedeanGroup (rationalPoints M) :=
    leviPoints_nonarchimedeanGroup p l hp hl
  exact admissibleSchur_centralCharacter D.quotient.representation
    (D.isAdmissible p l r hp hl hr hmul ha htemp) D.irreducible

/-- The scalar character of the full center of the selected irreducible
quotient, obtained from its proved admissibility. -/
def centralCharacter
    (htemp : IsNormalizedExponentTempered hG π)
    (D : UnitaryJacquetIrreducibleQuotientData p l r hp hl hr hmul ha π) :
    Subgroup.center (rationalPoints M) →* ℂˣ :=
  Classical.choose (D.existsUnique_centralCharacter p l r hp hl hr hmul ha htemp).exists

/-- The constructed full-center character is locally constant and acts by
scalars on the actual quotient. -/
theorem centralCharacter_spec
    (htemp : IsNormalizedExponentTempered hG π)
    (D : UnitaryJacquetIrreducibleQuotientData p l r hp hl hr hmul ha π) :
    letI := leviPointTopology l hl
    IsLocallyConstant
        (D.centralCharacter p l r hp hl hr hmul ha htemp :
          Subgroup.center (rationalPoints M) → ℂˣ) ∧
      D.quotient.HasCentralCharacter (D.centralCharacter p l r hp hl hr hmul ha htemp) :=
  Classical.choose_spec
    (D.existsUnique_centralCharacter p l r hp hl hr hmul ha htemp).exists

end UnitaryJacquetIrreducibleQuotientData

end Langlands.Aubert.General.RepresentedParabolic
