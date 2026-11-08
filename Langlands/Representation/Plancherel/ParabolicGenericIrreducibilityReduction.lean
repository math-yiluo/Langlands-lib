import Langlands.Representation.Plancherel.ParabolicUnitaryPointIrreducibility
import Langlands.Representation.Plancherel.RegularSquareIntegrableJacquetMultiplicityReduction
import Langlands.Representation.Plancherel.ParabolicRegularUnitaryTwist
import Langlands.Representation.Plancherel.RepresentedInductionComparison
import Langlands.Representation.Plancherel.RationalUnramifiedCharacterDensity
import Langlands.Representation.Families.RenardGenericIrreducibilityStatements

/-! # A reduction of actual generic irreducibility of unramified parabolic induction -/

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

local instance genericReductionAmbientAffine : IsAffine G.X.left :=
  isAffine_of_isAffineHom G.X.hom
local instance genericReductionAmbientPointTopology :
    TopologicalSpace (rationalPoints G) := rationalPointTopology F G.X
local instance genericReductionLeviPointTopology :
    TopologicalSpace (rationalPoints M) := rationalPointTopology F M.X
local instance genericReductionFieldT2 : T2Space F := BruhatTits.localField_t2Space F

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
square-integrable modulo the split center, irreducibility at regular unitary
points and Renard VI.8.4 give a nonempty open set of unramified characters on
which the actual Levi-normalized induction is irreducible. -/
theorem exists_open_irreducible_of_statements
    (hunit : UnitaryRegularParabolicIrreducibilityStatement.{u, uV})
    (hopen : Renard.AlgebraicFamily.InducedIrreducibilityOpenStatement.{u, uV})
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
  let Φ := parabolicLeviUnramifiedCharactersHomeomorph pres
  have hrep0 := SmoothRep.isIrreducible_of_equiv
    (representedInductionLeviEquiv pres hG hn hmul hn h hU π χ0).symm hirr0
  obtain ⟨f, hf0, hf⟩ := hopen F G hG P M U p l n hp hl hn hmul (intrinsicLeviRep pres π) hρ
    (Φ.symm χ0) hrep0
  refine ⟨Φ.symm ⁻¹' rationalUnramifiedPrincipalOpen M hl.isConnectedReductive f,
    (isOpen_rationalUnramifiedPrincipalOpen M hl.isConnectedReductive f).preimage
      Φ.symm.continuous, ⟨χ0, hf0⟩, ?_⟩
  intro χ hχ
  exact SmoothRep.isIrreducible_of_equiv
    (representedInductionLeviEquiv pres hG hn hmul hn h hU π χ) (hf (Φ.symm χ) hχ)

/-- The reduction of the generic-irreducibility target: irreducibility at regular
unitary points, together with Renard VI.8.4 openness of the irreducible locus of
represented unramified induction, implies
`ConditionalParabolicGenericIrreducibilityStatement`. Regular unitary points
exist by `regularUnitaryTwistExistence`. -/
def ParabolicGenericIrreducibilityReductionStatement : Prop :=
  UnitaryRegularParabolicIrreducibilityStatement.{u, uV} →
    Renard.AlgebraicFamily.InducedIrreducibilityOpenStatement.{u, uV} →
      ConditionalParabolicGenericIrreducibilityStatement.{u, uV}

/-- The reduction holds. -/
theorem conditionalParabolicGenericIrreducibility_of_statements :
    ParabolicGenericIrreducibilityReductionStatement.{u, uV} := by
  intro hunit hopen F _ _ _ _ G hG _ _ _ A M P U _ p l a n r hn Ppt Mpt Upt h hU hP hr
    C hC _ _ qMeasure _ π hirr hsq
  have := hG.isAffineHom
  exact exists_open_irreducible_of_statements r hn h hU hunit hopen hG hP hr π hirr
    qMeasure hsq

/-- The complete reduction of the generic-irreducibility target to eight
structural statements of the Library: the represented geometric lemma, the
Renard VII.2.4 criterion, compactness of actual parabolic quotients,
temperedness of square-integrable representations, Jacquet admissibility,
unimodularity of actual reductive point groups, the standard-cocharacter
statement and Renard VI.8.4 openness. -/
def ParabolicGenericIrreducibilityStructuralReductionStatement : Prop :=
  RepresentedParabolic.RepresentedGeometricLemmaStatement.{u, uV} →
    RepresentedParabolic.TemperedSquareIntegrableUnitaryPartStatement.{u, uV} →
      RepresentedParabolic.ArbitraryParabolicQuotientCompactStatement.{u} →
        RepresentedParabolic.SquareIntegrableNormalizedTemperedStatement.{u, uV} →
          RepresentedParabolic.ArbitraryParabolicJacquetAdmissibilityStatement.{u, uV} →
            RationalPointFamily.RationalReductiveUnimodularityStatement.{u} →
              GroupScheme.StandardCocharacterStatement.{u} →
                Renard.AlgebraicFamily.InducedIrreducibilityOpenStatement.{u, uV} →
                  ConditionalParabolicGenericIrreducibilityStatement.{u, uV}

/-- The complete reduction holds, by composing the three reductions. -/
theorem conditionalParabolicGenericIrreducibility_of_structuralStatements :
    ParabolicGenericIrreducibilityStructuralReductionStatement.{u, uV} := by
  intro hgeom hcrit hcompact htemp hjac hunimod hStandard hopen
  exact conditionalParabolicGenericIrreducibility_of_statements
    (unitaryRegularParabolicIrreducibility_of_statements
      (regularSquareIntegrableJacquetMultiplicity_of_statements hgeom hcrit hcompact htemp hjac)
      hunimod hStandard hcompact)
    hopen

end Langlands.Plancherel
