import Langlands.Representation.Exponents.TemperedJacquetStructure
import Langlands.Representation.CuspidalSupport.GroupTransport
import Langlands.Representation.Smooth.Admissibility.EmbeddingProof

/-! # Admissible complementary Jacquet parts on the actual Levi points -/

noncomputable section

universe u v

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme

variable {k : Type u} [Field k] [ValuativeRel k] [TopologicalSpace k]
  [IsNonarchimedeanLocalField k] [T2Space k]
  {G P M U : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]

local instance temperedLeviDecompositionAmbientPointTopology :
    TopologicalSpace (rationalPoints G) :=
  RationalPointFamily.pointTopology

variable [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
  (p : P ⟶ G) (l : M ⟶ P) (r : U ⟶ P)
  (hp : IsParabolicSubgroup p) (hl : IsRationalLeviSubgroup l)
  (hr : LeviSubgroup.IsGeometricUnipotentRadical r)
  (hmul : IsIso (subgroupMultiplication l r))
  {A : CommGroupScheme (Spec (CommRingCat.of k))} {a : A.toGrp ⟶ M}
  (ha : IsSplitComponent a)
  {hG : IsConnectedReductive G} {π : SmoothRep.{0, u, v} ℂ (rationalPoints G)}

include ha in
/-- Admissibility of the specified normalized Jacquet module, transported to
the actual Levi points with their canonical topology. -/
theorem IsNormalizedExponentTempered.isAdmissible_leviJacquetFunctor_obj
    (htemp : IsNormalizedExponentTempered hG π) :
    letI := leviPointTopology l hl
    ((leviJacquetFunctor p l r hp hr hl hmul).obj π).IsAdmissible := by
  let := leviPointTopology l hl
  exact isAdmissible_comp_continuousMulEquiv
    ((jacquetFunctor p l r hp hr hl hmul).obj π).representation
    (leviPointsEquiv p l hp hl)
    (htemp.isAdmissible_jacquetFunctor_obj p l r hp hl hr hmul ha)

/-- The unitary Jacquet module of a tempered source is admissible as a
representation of the actual Levi points. -/
theorem IsNormalizedExponentTempered.isAdmissible_leviUnitaryJacquetModule
    (htemp : IsNormalizedExponentTempered hG π) :
    letI := leviPointTopology l hl
    (leviUnitaryJacquetModule p l r hp hl hr hmul ha π).IsAdmissible := by
  let := leviPointTopology l hl
  exact isAdmissible_of_injective
    (SmoothRep.hom (leviUnitaryJacquetModuleι p l r hp hl hr hmul ha π))
    (leviUnitaryJacquetModuleι_injective p l r hp hl hr hmul ha π)
    (htemp.isAdmissible_leviJacquetFunctor_obj p l r hp hl hr hmul ha)

/-- The nonunitary Jacquet module of a tempered source is also admissible. -/
theorem IsNormalizedExponentTempered.isAdmissible_leviNonunitaryJacquetModule
    (htemp : IsNormalizedExponentTempered hG π) :
    letI := leviPointTopology l hl
    (leviNonunitaryJacquetModule p l r hp hl hr hmul ha π).IsAdmissible := by
  let := leviPointTopology l hl
  exact isAdmissible_of_injective
    (SmoothRep.hom (leviNonunitaryJacquetModuleι p l r hp hl hr hmul ha π))
    (leviNonunitaryJacquetModuleι_injective p l r hp hl hr hmul ha π)
    (htemp.isAdmissible_leviJacquetFunctor_obj p l r hp hl hr hmul ha)

/-- The literal inclusions of the unitary and nonunitary Jacquet modules
into the normalized Jacquet module of the actual Levi. -/
def leviJacquetPartsCofan (π : SmoothRep.{0, u, v} ℂ (rationalPoints G)) :
    letI := leviPointTopology l hl
    Cofan (fun b : Bool => match b with
      | false => leviNonunitaryJacquetModule p l r hp hl hr hmul ha π
      | true => leviUnitaryJacquetModule p l r hp hl hr hmul ha π) := by
  let := leviPointTopology l hl
  exact Cofan.mk ((leviJacquetFunctor p l r hp hr hl hmul).obj π) (fun b => match b with
    | false => leviNonunitaryJacquetModuleι p l r hp hl hr hmul ha π
    | true => leviUnitaryJacquetModuleι p l r hp hl hr hmul ha π)

/-- For a tempered source, the actual normalized Jacquet module and its
literal inclusions form a coproduct of the two admissible Jacquet parts. -/
def temperedLeviJacquetPartsCofanIsColimit
    (htemp : IsNormalizedExponentTempered hG π) :
    letI := leviPointTopology l hl
    IsColimit (leviJacquetPartsCofan p l r hp hl hr hmul ha π) := by
  have := hl.isConnectedReductive.isAffineHom
  let : TopologicalSpace (rationalPoints M) := leviPointTopology l hl
  have : LocallyCompactSpace (rationalPoints M) := leviPoints_locallyCompactSpace p l hp hl
  have : NonarchimedeanGroup (rationalPoints M) := leviPoints_nonarchimedeanGroup p l hp hl
  exact SmoothRep.complementaryCofanIsColimit
    ((leviJacquetFunctor p l r hp hr hl hmul).obj π)
    (leviUnitaryJacquetSubrepresentation p l r hp hl hr hmul ha π)
    (leviNonunitaryJacquetSubrepresentation p l r hp hl hr hmul ha π)
    (htemp.unitaryJacquetPart_isCompl p l r hp hl hr hmul ha)

end Langlands.Aubert.General.RepresentedParabolic
