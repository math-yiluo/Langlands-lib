import Langlands.Representation.Exponents.ArbitraryParabolicUnitaryJacquetPart
import Langlands.Representation.Category.ComplementaryCoproduct
import Langlands.Representation.Aubert.General.JacquetCommonConstituent

/-!
# Irreducible quotients of the actual unitary Jacquet summand

The supplied complementary splitting and compactness of the actual parabolic
quotient give finite generation of the unitary summand. Its nontriviality then
gives a selected irreducible quotient, on the Levi's own rational points.
-/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj MonoidAlgebra

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme

variable {k : Type u} [Field k] [ValuativeRel k] [TopologicalSpace k]
  [IsNonarchimedeanLocalField k] [T2Space k]
  {G P M U : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]

local instance quotientAmbientPointTopology : TopologicalSpace (rationalPoints G) :=
  RationalPointFamily.pointTopology

variable [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
  (p : P ⟶ G) (l : M ⟶ P) (r : U ⟶ P)
  (hp : IsParabolicSubgroup p) (hl : IsRationalLeviSubgroup l)
  (hr : LeviSubgroup.IsGeometricUnipotentRadical r)
  (hmul : IsIso (subgroupMultiplication l r))
  {A : CommGroupScheme (Spec (CommRingCat.of k))} {a : A.toGrp ⟶ M}
  (ha : IsSplitComponent a) (π : SmoothRep.{0, u, v} ℂ (rationalPoints G))

/-- The actual unitary Jacquet summand is finitely generated when the ambient
representation is irreducible and the supplied splitting is complementary. -/
theorem unitaryJacquetPart_moduleFinite_of_isCompl
    [CompactSpace (Induction.LeftQuotient (pointImage p))]
    (hπ : π.IsIrreducible)
    (hcompl : IsCompl
      (unitaryJacquetPart p l r hp hl hr hmul ha π).toSubmodule
      (nonunitaryJacquetPart p l r hp hl hr hmul ha π).toSubmodule) :
    Module.Finite ℂ[pointImage (l ≫ p)]
      (SmoothRep.subrepresentation ((jacquetFunctor p l r hp hr hl hmul).obj π)
        (unitaryJacquetPart p l r hp hl hr hmul ha π)).representation.asModule := by
  let J := (jacquetFunctor p l r hp hr hl hmul).obj π
  let S := unitaryJacquetPart p l r hp hl hr hmul ha π
  let Q := nonunitaryJacquetPart p l r hp hl hr hmul ha π
  have : π.representation.IsIrreducible := hπ
  have hfinite : Module.Finite ℂ[pointImage (l ≫ p)] J.representation.asModule :=
    JacquetFiniteGeneration.finite_of_compactQuotient
      (isSemidirectDecomposition_pointImage p l r hp.isClosedSubgroup hr hmul)
      (isClosed_pointImage_comp p r hp.isClosedSubgroup hr.1.isClosedSubgroup)
      π inferInstance
  let := hfinite
  let q : J ⟶ SmoothRep.subrepresentation J S :=
    SmoothRep.complementaryDesc (Q := Q) hcompl (𝟙 _) 0
  have hq : Function.Surjective (SmoothRep.hom q) := by
    intro s
    refine ⟨s.val, ?_⟩
    have he := SmoothRep.subtype_complementaryDesc_left hcompl
      (𝟙 (SmoothRep.subrepresentation J S)) (0 : SmoothRep.subrepresentation J Q ⟶ _)
    exact congrArg (fun f => SmoothRep.hom f s) he
  exact Module.Finite.of_surjective
    (Representation.IntertwiningMap.equivLinearMapAsModule _ _ (SmoothRep.hom q)) hq

/-- A selected irreducible smooth quotient of the actual unitary Jacquet module
on the Levi's rational points, including its actual surjective morphism. -/
structure UnitaryJacquetIrreducibleQuotientData where
  quotient : letI := leviPointTopology l hl
    SmoothRep.{0, u, v} ℂ (rationalPoints M)
  irreducible : letI := leviPointTopology l hl
    quotient.IsIrreducible
  quotientMap : letI := leviPointTopology l hl
    leviUnitaryJacquetModule p l r hp hl hr hmul ha π ⟶ quotient
  surjective : letI := leviPointTopology l hl
    Function.Surjective (SmoothRep.hom quotientMap)

/-- Choose an actual irreducible quotient after finite generation and
nontriviality of the literal unitary summand have been established. -/
def unitaryJacquetIrreducibleQuotient
    [CompactSpace (Induction.LeftQuotient (pointImage p))]
    (hπ : π.IsIrreducible)
    (hcompl : IsCompl
      (unitaryJacquetPart p l r hp hl hr hmul ha π).toSubmodule
      (nonunitaryJacquetPart p l r hp hl hr hmul ha π).toSubmodule)
    (hne : Nontrivial
      (SmoothRep.subrepresentation ((jacquetFunctor p l r hp hr hl hmul).obj π)
        (unitaryJacquetPart p l r hp hl hr hmul ha π))) :
    UnitaryJacquetIrreducibleQuotientData p l r hp hl hr hmul ha π := by
  classical
  let S := SmoothRep.subrepresentation ((jacquetFunctor p l r hp hr hl hmul).obj π)
    (unitaryJacquetPart p l r hp hl hr hmul ha π)
  have hfinite := unitaryJacquetPart_moduleFinite_of_isCompl
    p l r hp hl hr hmul ha π hπ hcompl
  have hex : Nonempty
      (UnitaryJacquetIrreducibleQuotientData p l r hp hl hr hmul ha π) := by
    obtain ⟨τ, hτ, q, hq⟩ :=
      JacquetCommonConstituent.exists_irreducible_quotient_of_moduleFinite S hne hfinite
    let := leviPointTopology l hl
    let e := leviPointsEquiv p l hp hl
    refine ⟨⟨SmoothRep.pullback e τ, ?_,
      (SmoothRep.pullbackFunctor e).map q, hq⟩⟩
    exact (isIrreducible_comp_continuousMulEquiv_iff τ.representation e).mpr hτ
  exact Classical.choice hex

end Langlands.Aubert.General.RepresentedParabolic
