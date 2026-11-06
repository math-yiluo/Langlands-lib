import Langlands.Representation.Exponents.TemperedJacquetStructure
import Langlands.Representation.Exponents.TemperedUnitaryJacquetEmbedding

/-! # Induction embeddings from a tempered unitary Jacquet part -/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme

variable {k : Type u} [Field k] [ValuativeRel k] [TopologicalSpace k]
  [IsNonarchimedeanLocalField k] [T2Space k]
  {G P M U : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]

local instance temperedEmbeddingAmbientPointTopology : TopologicalSpace (rationalPoints G) :=
  RationalPointFamily.pointTopology

variable [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
  (p : P ⟶ G) (l : M ⟶ P) (r : U ⟶ P)
  (hp : IsParabolicSubgroup p) (hl : IsRationalLeviSubgroup l)
  (hr : LeviSubgroup.IsGeometricUnipotentRadical r)
  (hmul : IsIso (subgroupMultiplication l r))
  {A : CommGroupScheme (Spec (CommRingCat.of k))} {a : A.toGrp ⟶ M}

variable (ha : IsSplitComponent a)
  {hG : IsConnectedReductive G} {π : SmoothRep.{0, u, v} ℂ (rationalPoints G)}

section Embedding

variable [IsAffineHom M.X.hom]

local instance temperedEmbeddingLeviPointTopology : TopologicalSpace (rationalPoints M) :=
  RationalPointFamily.pointTopology

/-- The actual induction map adjoint to a selected unitary Jacquet quotient,
with radical unimodularity and complementary splitting derived from temperedness. -/
def temperedUnitaryJacquetQuotientInductionMap
    (htemp : IsNormalizedExponentTempered hG π)
    (D : UnitaryJacquetIrreducibleQuotientData p l r hp hl hr hmul ha π) :
    π.representation.IntertwiningMap
      ((leviInductionFunctor p l r hp hr hl hmul).obj D.quotient).representation :=
  unitaryJacquetQuotientInductionMap p l r hp hl hr hmul ha π
    (htemp.radical_isUnimodularModulus p l r hp hl hr ha)
    (htemp.unitaryJacquetPart_isCompl p l r hp hl hr hmul ha) D

/-- For an irreducible tempered source the selected quotient's induction map
is injective, without a separate splitting or radical-modulus input. -/
theorem temperedUnitaryJacquetQuotientInductionMap_injective
    (htemp : IsNormalizedExponentTempered hG π) (hπ : π.IsIrreducible)
    (D : UnitaryJacquetIrreducibleQuotientData p l r hp hl hr hmul ha π) :
    Function.Injective
      (temperedUnitaryJacquetQuotientInductionMap p l r hp hl hr hmul ha htemp D) :=
  unitaryJacquetQuotientInductionMap_injective p l r hp hl hr hmul ha π
    (htemp.radical_isUnimodularModulus p l r hp hl hr ha) hπ
    (htemp.unitaryJacquetPart_isCompl p l r hp hl hr hmul ha) D

end Embedding

/-- For an irreducible tempered source, a nonzero unitary Jacquet part yields
an irreducible Levi representation with an actual induction embedding.
Compactness of the parabolic quotient and nontriviality remain explicit. -/
theorem IsNormalizedExponentTempered.exists_irreducible_induction_embedding
    [CompactSpace (Induction.LeftQuotient (pointImage p))]
    (htemp : IsNormalizedExponentTempered hG π) (hπ : π.IsIrreducible)
    (hne : Nontrivial
      (SmoothRep.subrepresentation ((jacquetFunctor p l r hp hr hl hmul).obj π)
        (unitaryJacquetPart p l r hp hl hr hmul ha π))) :
    letI := leviPointTopology l hl
    ∃ σ : SmoothRep.{0, u, v} ℂ (rationalPoints M), σ.IsIrreducible ∧
      ∃ f : π.representation.IntertwiningMap
        ((leviInductionFunctor p l r hp hr hl hmul).obj σ).representation,
        Function.Injective f :=
  exists_irreducible_induction_embedding_of_unitaryJacquetPart p l r hp hl hr hmul ha π
    (htemp.radical_isUnimodularModulus p l r hp hl hr ha) hπ
    (htemp.unitaryJacquetPart_isCompl p l r hp hl hr hmul ha) hne

end Langlands.Aubert.General.RepresentedParabolic
