import Langlands.Representation.Exponents.ArbitraryParabolicJacquetAdmissibilityReduction
import Langlands.Representation.Exponents.NormalizedTemperedSubrepresentation
import Langlands.Representation.Exponents.UnitaryJacquetSplitting
import Langlands.Representation.Exponents.TemperedJacquetRestriction

/-! # Actual Jacquet structure supplied by normalized temperedness -/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme

variable {k : Type u} [Field k] [ValuativeRel k] [TopologicalSpace k]
  [IsNonarchimedeanLocalField k] [T2Space k]
  {G P M U : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]

local instance structureAmbientPointTopology : TopologicalSpace (rationalPoints G) :=
  RationalPointFamily.pointTopology

variable [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
  (p : P ⟶ G) (l : M ⟶ P) (r : U ⟶ P)
  (hp : IsParabolicSubgroup p) (hl : IsRationalLeviSubgroup l)
  (hr : LeviSubgroup.IsGeometricUnipotentRadical r)
  (hmul : IsIso (subgroupMultiplication l r))
  {A : CommGroupScheme (Spec (CommRingCat.of k))} {a : A.toGrp ⟶ M}

/-- A supplied compatible root presentation gives admissibility of the actual
normalized Jacquet module of any admissible source. -/
theorem isAdmissible_jacquetFunctor_obj_of_presentation
    (hG : IsConnectedReductive G) (pres : ParabolicRootPresentation p l a)
    (π : SmoothRep.{0, u, v} ℂ (rationalPoints G)) (hπ : π.IsAdmissible) :
    ((jacquetFunctor p l r hp hr hl hmul).obj π).IsAdmissible := by
  have := hG.smooth
  let χ := CommGroupScheme.groupHom pres.splitComponentCocharacter ≫ a ≫ l ≫ p
  have hN : pointImage (r ≫ p) =
      (Dynamic.unipotent χ).carrier (Over.mk (𝟙 _)) := by
    rw [pointImage_eq_range_carrier, pres.range_comp_radical_eq hr]
  have hL : pointImage (l ≫ p) =
      (Dynamic.centralizer χ).carrier (Over.mk (𝟙 _)) := by
    rw [pointImage_eq_range_carrier, pres.levi_eq_splitComponentCocharacter]
  obtain ⟨g, hBasis⟩ :=
    RationalPointFamily.dynamic_hasOppositeIwahoriContractionBasis G hG χ
  have hBasis' := hBasis.hasIwahoriContractionBasis
  rw [← hN, ← hL] at hBasis'
  exact isAdmissible_normalizedJacquetFunctor_obj_of_iwahoriContraction
    (pointImage (r ≫ p)) (pointImage (l ≫ p))
    ((Dynamic.unipotent (Dynamic.inverseCocharacter χ)).carrier (Over.mk (𝟙 _)))
    (isClosed_pointImage_comp p r hp.isClosedSubgroup hr.1.isClosedSubgroup)
    (pointImage_le_normalizer p l r hr) hBasis' π hπ

variable (ha : IsSplitComponent a)
  {hG : IsConnectedReductive G} {π : SmoothRep.{0, u, v} ℂ (rationalPoints G)}

include ha in
/-- Temperedness supplies both admissibility of the source and a compatible
presentation, hence admissibility of each specified normalized Jacquet module. -/
theorem IsNormalizedExponentTempered.isAdmissible_jacquetFunctor_obj
    (htemp : IsNormalizedExponentTempered hG π) :
    ((jacquetFunctor p l r hp hr hl hmul).obj π).IsAdmissible := by
  obtain ⟨pres⟩ := htemp.nonempty_presentation p l a hp hl ha
  exact isAdmissible_jacquetFunctor_obj_of_presentation p l r hp hl hr hmul
    hG pres π htemp.isAdmissible

include l hl ha in
/-- The supplied radical is unimodular for every tempered source, using
the compatible presentation already contained in the temperedness predicate. -/
theorem IsNormalizedExponentTempered.radical_isUnimodularModulus
    (htemp : IsNormalizedExponentTempered hG π) :
    IsUnimodularModulus (pointImage (r ≫ p))
      (isClosed_pointImage_comp p r hp.isClosedSubgroup hr.1.isClosedSubgroup) := by
  obtain ⟨pres⟩ := htemp.nonempty_presentation p l a hp hl ha
  exact isUnimodularModulus_of_isLimitOfCompactSubgroups _ _
    (pointImage_radical_isLimitOfCompactSubgroups_of_presentation hG pres hr)

/-- Every actual normalized Jacquet module of a tempered representation
splits as its unitary and nonunitary characteristic parts. -/
theorem IsNormalizedExponentTempered.unitaryJacquetPart_isCompl
    (htemp : IsNormalizedExponentTempered hG π) :
    IsCompl (unitaryJacquetPart p l r hp hl hr hmul ha π).toSubmodule
      (nonunitaryJacquetPart p l r hp hl hr hmul ha π).toSubmodule :=
  unitaryJacquetPart_isCompl_nonunitaryJacquetPart_of_admissible p l r hp hl hr hmul ha π
    (htemp.isAdmissible_jacquetFunctor_obj p l r hp hl hr hmul ha)

/-- The actual projection onto the unitary Jacquet module of a tempered source,
with complementarity supplied by temperedness. The Levi has its canonical
point topology, with affine structure derived from the rational Levi witness. -/
def temperedLeviUnitaryJacquetRetraction
    (htemp : IsNormalizedExponentTempered hG π) :
    letI := leviPointTopology l hl
    (leviJacquetFunctor p l r hp hr hl hmul).obj π ⟶
      leviUnitaryJacquetModule p l r hp hl hr hmul ha π := by
  let := hl.isConnectedReductive.isAffineHom
  let : TopologicalSpace (rationalPoints M) := leviPointTopology l hl
  let : LocallyCompactSpace (rationalPoints M) := leviPoints_locallyCompactSpace p l hp hl
  let : NonarchimedeanGroup (rationalPoints M) := leviPoints_nonarchimedeanGroup p l hp hl
  exact leviUnitaryJacquetRetraction p l r hp hl hr hmul ha π
    (htemp.unitaryJacquetPart_isCompl p l r hp hl hr hmul ha)

/-- The tempered projection is a retraction of the literal inclusion. -/
@[simp] theorem leviUnitaryJacquetModuleι_temperedRetraction
    (htemp : IsNormalizedExponentTempered hG π) :
    letI := leviPointTopology l hl
    leviUnitaryJacquetModuleι p l r hp hl hr hmul ha π ≫
      temperedLeviUnitaryJacquetRetraction p l r hp hl hr hmul ha htemp = 𝟙 _ := by
  let := hl.isConnectedReductive.isAffineHom
  let : TopologicalSpace (rationalPoints M) := leviPointTopology l hl
  exact leviUnitaryJacquetModuleι_retraction p l r hp hl hr hmul ha π
    (htemp.unitaryJacquetPart_isCompl p l r hp hl hr hmul ha)

end Langlands.Aubert.General.RepresentedParabolic
