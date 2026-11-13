import Langlands.Representation.Plancherel.ParabolicGenericIrreducibilityReduction
import Langlands.Representation.Plancherel.RegularSquareIntegrableJacquetMultiplicityProof
import Langlands.Representation.Families.AdmissibleInducedIrreducibilityOpen
import Langlands.Representation.Aubert.General.RationalReductiveUnimodularityProof
import Langlands.GroupScheme.Rational.StandardCocharacterProof

/-! # Generic irreducibility of actual unramified parabolic induction

This module proves `ConditionalParabolicGenericIrreducibilityStatement`. The
argument is that of `exists_open_irreducible_of_statements`, with its two
hypotheses discharged:

* irreducibility at regular unitary points comes from
  `unitaryRegularParabolicIrreducibility_of_statements` applied to the
  unconditional Jacquet multiplicity bound `regularSquareIntegrableJacquetMultiplicity`
  and the published unimodularity, standard-cocharacter and quotient-compactness
  theorems;
* Renard VI.8.4 openness is used only for the inducing representation at hand,
  which is admissible because square integrability modulo a central subgroup
  includes admissibility; for admissible inducing representations it is
  `Renard.AlgebraicFamily.admissibleInducedIrreducibilityOpen`. -/

noncomputable section

open CategoryTheory AlgebraicGeometry MeasureTheory MeasureTheory.Measure
open scoped CategoryTheory.MonObj NNReal
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.Plancherel

universe u uV

open Aubert.General Aubert.General.RepresentedParabolic

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {A : CommGroupScheme (Spec (CommRingCat.of F))}
  {G M P U : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [IsAffine M.X.left]
  {p : P ⟶ G} {l : M ⟶ P} {a : A.toGrp ⟶ M} {n : U ⟶ P}
  (pres : ParabolicRootPresentation p l a)

local instance genericProofAmbientAffine : IsAffine G.X.left :=
  isAffine_of_isAffineHom G.X.hom
local instance genericProofAmbientPointTopology :
    TopologicalSpace (rationalPoints G) := rationalPointTopology F G.X
local instance genericProofLeviPointTopology :
    TopologicalSpace (rationalPoints M) := rationalPointTopology F M.X
local instance genericProofFieldT2 : T2Space F := BruhatTits.localField_t2Space F

variable [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
  [T2Space (rationalPoints G)]
  (hn : LeviSubgroup.IsGeometricUnipotentRadical n)
  (h : IsSemidirectDecomposition
    ((SubgroupFunctor.range p).carrier (Over.mk (𝟙 _)))
    (parabolicLeviPointSubgroup p l)
    ((SubgroupFunctor.range (n ≫ p)).carrier (Over.mk (𝟙 _))))
  (hU : IsClosed (((SubgroupFunctor.range (n ≫ p)).carrier (Over.mk (𝟙 _))) :
    Set (rationalPoints G)))

include pres hn in
set_option maxHeartbeats 1600000 in
/-- For an irreducible representation of the literal Levi that is
square-integrable modulo the split center, there is a nonempty open set of
unramified characters on which the actual Levi-normalized induction is
irreducible: it is irreducible at a regular unitary point, and the irreducible
locus of the admissible inducing representation is open around that point. -/
theorem exists_open_irreducible_unconditional
    (hG : IsConnectedReductive G)
    (hP : IsClosed (((SubgroupFunctor.range p).carrier (Over.mk (𝟙 _))) :
      Set (rationalPoints G)))
    (hr : Continuous h.projection)
    (π : SmoothRep.{0, u, uV} ℂ (parabolicLeviPointSubgroup p l)) (hirr : π.IsIrreducible) :
    let C := (parabolicSplitComponentPointHom pres).range
    let hC := parabolicSplitComponentPointHom_range_le_center pres
    letI : C.Normal := C.normal_of_le_center hC
    ∀ [MeasurableSpace (parabolicLeviPointSubgroup p l ⧸ C)]
      [BorelSpace (parabolicLeviPointSubgroup p l ⧸ C)]
      (qMeasure : Measure (parabolicLeviPointSubgroup p l ⧸ C)) [IsHaarMeasure qMeasure],
      IsSquareIntegrableModCentralSubgroup C hC π.representation qMeasure →
      ∃ D : Set (unramifiedCharacters (parabolicLeviRationalNormCharacters pres)),
        IsOpen D ∧ D.Nonempty ∧
          ∀ χ ∈ D, (UnramifiedLeviInduction h hU
            (parabolicLeviRationalNormCharacters pres) χ π).IsIrreducible := by
  intro C hC _ _ qMeasure _ hsq
  have : C.Normal := C.normal_of_le_center hC
  have := hG.smooth
  have hunit := unitaryRegularParabolicIrreducibility_of_statements.{u, uV}
    regularSquareIntegrableJacquetMultiplicity.{u, uV}
    RationalPointFamily.rationalReductiveUnimodularity.{u}
    GroupScheme.standardCocharacter.{u}
    arbitraryParabolicQuotientCompact.{u}
  let c := hsq.2.choose
  have hω : π.HasCentralCharacter c.character := c.acts
  have : Nontrivial π := by
    have : IsSimpleModule (MonoidAlgebra ℂ (parabolicLeviPointSubgroup p l))
        π.representation.asModule :=
      (Representation.irreducible_iff_isSimpleModule_asModule _).mp hirr
    exact IsSimpleModule.nontrivial (MonoidAlgebra ℂ (parabolicLeviPointSubgroup p l))
      π.representation.asModule
  obtain ⟨χ0, hχ0u, hreg⟩ := exists_unitary_twist_isNormalizerRegular pres hG π c.character hω
  have hirr0 := hunit F G hG A M P U p l a n pres hn h hU hP hr qMeasure π hirr hsq χ0 hχ0u hreg
  let hp := pres.isCompatible.parabolic
  let hl := pres.isCompatible.levi
  let hmul := parabolicRadical_isIso_subgroupMultiplication pres hG hn
  have := leviPoints_locallyCompactSpace p l hp hl
  have := leviPoints_nonarchimedeanGroup p l hp hl
  have hρ : (intrinsicLeviRep pres π).IsIrreducible :=
    (intrinsicLeviRep_isIrreducible_iff pres π).mpr hirr
  have hadm : (intrinsicLeviRep pres π).IsAdmissible :=
    isAdmissible_comp_continuousMulEquiv π.representation
      (parabolicLeviPointHomeomorph pres) hsq.1
  let Φ := parabolicLeviUnramifiedCharactersHomeomorph pres
  have hrep0 := SmoothRep.isIrreducible_of_equiv
    (representedInductionLeviEquiv pres hG hn hmul hn h hU π χ0).symm hirr0
  obtain ⟨f, hf0, hf⟩ := Renard.AlgebraicFamily.admissibleInducedIrreducibilityOpen.{u, uV}
    F G hG P M U p l n hp hl hn hmul (intrinsicLeviRep pres π) hρ hadm (Φ.symm χ0) hrep0
  refine ⟨Φ.symm ⁻¹' rationalUnramifiedPrincipalOpen M hl.isConnectedReductive f,
    (isOpen_rationalUnramifiedPrincipalOpen M hl.isConnectedReductive f).preimage
      Φ.symm.continuous, ⟨χ0, hf0⟩, ?_⟩
  intro χ hχ
  exact SmoothRep.isIrreducible_of_equiv
    (representedInductionLeviEquiv pres hG hn hmul hn h hU π χ) (hf (Φ.symm χ) hχ)

/-- **Generic irreducibility of actual unramified parabolic induction**:
`ConditionalParabolicGenericIrreducibilityStatement` holds. -/
theorem conditionalParabolicGenericIrreducibility :
    ConditionalParabolicGenericIrreducibilityStatement.{u, uV} := by
  intro F _ _ _ _ G hG _ _ _ A M P U _ p l a n r hn Ppt Mpt Upt h hU hP hr
    C hC _ _ qMeasure _ π hirr hsq
  have := hG.isAffineHom
  exact exists_open_irreducible_unconditional r hn h hU hG hP hr π hirr qMeasure hsq

end Langlands.Plancherel
