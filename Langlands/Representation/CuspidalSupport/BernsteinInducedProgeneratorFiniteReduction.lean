import Langlands.Representation.CuspidalSupport.BernsteinInducedProgeneratorStatement
import Langlands.Representation.CuspidalSupport.BernsteinRepresentedInduction
import Langlands.Representation.CuspidalSupport.RationalSummandSmallProgeneratorReduction
import Langlands.Representation.Exponents.LeviInductionFiniteTypeStatement

/-! # Finite generation of the induced Bernstein progenerator (Renard VI.10.1)

`bernsteinInducedProgenerator` names Renard's `Π_Ω = i_P^G(Π_D)`, the representation `piOmega`
of `BernsteinInducedProgeneratorStatement`.
The finite-generation conjunct of the VI.10.1 Theorem follows from the VI.7.5 Theorem
`LeviInductionFiniteTypeStatement`, which is retained as a premise, and the published
unconditional finite generation of `Π_D = ind_{⁰M}^M ρ₀`
(`finite_rationalNormKernelSummandInduction`).
-/

noncomputable section

set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology
open Langlands.Aubert.General Langlands.Aubert.General.RationalPointFamily
open Langlands.GroupScheme
open scoped CategoryTheory.MonObj

namespace Langlands.CuspidalSupport

universe uF uV uG uW

/-- Finite generation over the group algebra transfers along an isomorphism of smooth
representations. -/
theorem moduleFinite_of_smoothRepIso {H : Type uG} [Group H] [TopologicalSpace H]
    {A B : SmoothRep.{0, uG, uW} ℂ H} (e : A ≅ B)
    (hA : Module.Finite (MonoidAlgebra ℂ H) A.representation.asModule) :
    Module.Finite (MonoidAlgebra ℂ H) B.representation.asModule :=
  Module.Finite.of_surjective (hM := hA)
    (Representation.IntertwiningMap.equivLinearMapAsModule _ _ (SmoothRep.hom e.hom))
    ((SmoothRep.epi_iff_surjective e.hom).1 inferInstance)

section Standard

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom]
  {T : CommGroupScheme (Spec (CommRingCat.of F))}
  (i : T.toGrp ⟶ G) (ν : cocharacterLattice T)

local instance bernsteinProgeneratorFiniteInstance1 : IsAffine G.X.left :=
  isAffine_of_isAffineHom G.X.hom
local instance bernsteinProgeneratorFiniteInstance2 : T2Space F :=
  Langlands.HarmonicAnalysis.GeneralLocalField.t2Space F
local instance bernsteinProgeneratorFiniteInstance3 : TopologicalSpace (rationalPoints G) :=
  pointTopology
local instance bernsteinProgeneratorFiniteInstance4 (I : Finset (SimpleRoot i ν)) :
    IsClosedImmersion (Standard.leviHom i ν (rootSet i ν I)).hom.hom.left :=
  Standard.isClosedSubgroup_leviHom i ν (rootSet i ν I)
local instance bernsteinProgeneratorFiniteInstance5 (I : Finset (SimpleRoot i ν)) :
    IsAffine (bernsteinLeviScheme i ν I).X.left :=
  isAffine_of_isAffineHom (Standard.leviHom i ν (rootSet i ν I)).hom.hom.left
local instance bernsteinProgeneratorFiniteInstance6 (I : Finset (SimpleRoot i ν)) :
    LocallyOfFiniteType (bernsteinLeviScheme i ν I).X.hom := by
  rw [← (Standard.leviHom i ν (rootSet i ν I)).hom.hom.w]
  infer_instance
local instance bernsteinProgeneratorFiniteInstance7 (I : Finset (SimpleRoot i ν)) :
    TopologicalSpace (rationalPoints (bernsteinLeviScheme i ν I)) :=
  rationalPointTopology F (bernsteinLeviScheme i ν I).X

variable [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
  (family : BernsteinStandardFamily i ν)

omit [LocallyOfFiniteType G.X.hom] in
/-- Under the VI.7.5 Theorem, the literal standard normalized induction of a finitely
generated representation of a standard rational Levi is finitely generated. -/
theorem finite_bernsteinStandardInduction_of_leviInductionFiniteType
    (hFT : RepresentedParabolic.LeviInductionFiniteTypeStatement.{uF, max uF uV})
    (I : Finset (SimpleRoot i ν))
    (ρ : SmoothRep.{0, uF, max uF uV} ℂ (rationalPoints (bernsteinLeviScheme i ν I)))
    (hρ : Module.Finite (MonoidAlgebra ℂ (rationalPoints (bernsteinLeviScheme i ν I)))
      ρ.representation.asModule) :
    Module.Finite (MonoidAlgebra ℂ (rationalPoints G))
      ((normalizedInductionFunctor (family.decomposition I) (family.closedUnipotent I)).obj
        (bernsteinLiteralLeviRep i ν I ρ)).representation.asModule := by
  have h := bernsteinStandardRepresentativesGeometric i ν family I
  have hrep := hFT F G family.connectedReductive _ _ _
    (Standard.parabolicHom i ν (rootSet i ν I))
    (Standard.leviToParabolic i ν (rootSet i ν I))
    (Standard.unipotentToParabolic i ν (rootSet i ν I))
    h.1 h.2.1 h.2.2.1 h.2.2.2 ρ hρ
  exact moduleFinite_of_smoothRepIso
    (bernsteinStandardRepresentedInductionIso i ν family I ρ) hrep

/-- Renard's representation `Π_Ω = i_P^G(Π_D)` of VI.10.1: for a cuspidal datum `a` of the
standard family (standard Levi `M` with index `a.roots`) and a smooth representation `ρ₀` of
the common norm kernel `⁰M(F)`, the normalized induction along the standard parabolic of
`a.roots` of `Π_D = ind_{⁰M(F)}^{M(F)} ρ₀`. This is literally the representation `piOmega` of
`BernsteinInducedProgeneratorStatement`. -/
def bernsteinInducedProgenerator (a : BernsteinCuspidalDatum.{uF, max uF uV} i ν family)
    (ρ₀ : SmoothRep.{0, uF, max uF uV} ℂ
      (Plancherel.rationalCommonNormKernel (bernsteinLeviScheme i ν a.roots))) :
    SmoothRep.{0, uF, max uF uV} ℂ (rationalPoints G) :=
  (normalizedInductionFunctor (family.decomposition a.roots)
    (family.closedUnipotent a.roots)).obj
      (bernsteinLiteralLeviRep i ν a.roots
        (rationalNormKernelSummandInduction (bernsteinLeviScheme i ν a.roots) ρ₀))

/-- The defining unfolding of `bernsteinInducedProgenerator`. -/
theorem bernsteinInducedProgenerator_eq (a : BernsteinCuspidalDatum.{uF, max uF uV} i ν family)
    (ρ₀ : SmoothRep.{0, uF, max uF uV} ℂ
      (Plancherel.rationalCommonNormKernel (bernsteinLeviScheme i ν a.roots))) :
    bernsteinInducedProgenerator.{uF, uV} i ν family a ρ₀ =
      (normalizedInductionFunctor (family.decomposition a.roots)
        (family.closedUnipotent a.roots)).obj
          (bernsteinLiteralLeviRep i ν a.roots
            (rationalNormKernelSummandInduction (bernsteinLeviScheme i ν a.roots) ρ₀)) :=
  rfl

/-- The finite-generation conjunct of the VI.10.1 Theorem, conditional on the VI.7.5
Theorem: `Π_Ω = i_P^G(Π_D)` is finitely generated over `ℂ[G(F)]`. -/
theorem finite_bernsteinInducedProgenerator_of_leviInductionFiniteType
    (hFT : RepresentedParabolic.LeviInductionFiniteTypeStatement.{uF, max uF uV})
    (a : BernsteinCuspidalDatum.{uF, max uF uV} i ν family)
    (ρ₀ : SmoothRep.{0, uF, max uF uV} ℂ
      (Plancherel.rationalCommonNormKernel (bernsteinLeviScheme i ν a.roots)))
    (hρ₀ : ρ₀.IsIrreducible) :
    Module.Finite (MonoidAlgebra ℂ (rationalPoints G))
      (bernsteinInducedProgenerator.{uF, uV} i ν family a ρ₀).representation.asModule :=
  finite_bernsteinStandardInduction_of_leviInductionFiniteType i ν family hFT a.roots _
    (finite_rationalNormKernelSummandInduction (bernsteinLeviScheme i ν a.roots) ρ₀ hρ₀)

end Standard

end Langlands.CuspidalSupport
