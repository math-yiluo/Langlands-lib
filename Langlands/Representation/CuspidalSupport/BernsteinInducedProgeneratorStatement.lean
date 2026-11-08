import Langlands.Representation.CuspidalSupport.BernsteinBlock
import Langlands.Representation.CuspidalSupport.RationalSummandSmallProgeneratorStatement

/-! # The induced progenerator of a Bernstein block (Renard VI.10.1, Theorem)

For an actual standard cuspidal datum `(M, ρ)` with inertial class `𝔰`, an irreducible summand
`ρ₀` of `ρ|_{⁰M}` and `Π_D = ind_{⁰M}^M(ρ₀)`, the normalized induction `Π_Ω = i_P^G(Π_D)`
along the standard parabolic lies in the Bernstein block of `𝔰` and is a finitely generated
projective generator of that block.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology
open Langlands.Aubert.General Langlands.Aubert.General.RationalPointFamily
open Langlands.GroupScheme
open scoped CategoryTheory.MonObj

namespace Langlands.CuspidalSupport

universe uF uV

/-- Renard VI.10.1, Theorem, for the actual standard cuspidal data of a standard family: let
`a` be a cuspidal datum (standard Levi `M` with index `a.roots` and irreducible cuspidal
`a.representation`), `ρ₀` an irreducible representation of the common norm kernel `⁰M(F)`
embedded in the restriction of `a.representation`, `Π_D = ind_{⁰M(F)}^{M(F)} ρ₀` and
`Π_Ω` its normalized induction along the standard parabolic of `a.roots`. Then `Π_Ω` belongs
to the Bernstein block of the inertial class of `a`, and in that block it is projective,
finitely generated over `ℂ[G(F)]`, and a generator: `Hom(Π_Ω, -)` separates morphisms. -/
def BernsteinInducedProgeneratorStatement : Prop :=
  ∀ (F : Type uF) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffineHom G.X.hom]
    [LocallyOfFiniteType G.X.hom]
    (T : CommGroupScheme (Spec (CommRingCat.of F))) (i : T.toGrp ⟶ G)
    (ν : cocharacterLattice T),
    haveI : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
    letI : TopologicalSpace (rationalPoints G) := pointTopology
    ∀ [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
      (family : BernsteinStandardFamily i ν)
      (a : BernsteinCuspidalDatum.{uF, max uF uV} i ν family),
      haveI : IsClosedImmersion (Standard.leviHom i ν (rootSet i ν a.roots)).hom.hom.left :=
        Standard.isClosedSubgroup_leviHom i ν (rootSet i ν a.roots)
      haveI : IsAffine (bernsteinLeviScheme i ν a.roots).X.left :=
        isAffine_of_isAffineHom (Standard.leviHom i ν (rootSet i ν a.roots)).hom.hom.left
      haveI : LocallyOfFiniteType (bernsteinLeviScheme i ν a.roots).X.hom := by
        rw [← (Standard.leviHom i ν (rootSet i ν a.roots)).hom.hom.w]
        infer_instance
      letI : TopologicalSpace (rationalPoints (bernsteinLeviScheme i ν a.roots)) :=
        rationalPointTopology F (bernsteinLeviScheme i ν a.roots).X
      ∀ ρ₀ : SmoothRep.{0, uF, max uF uV} ℂ
          (Plancherel.rationalCommonNormKernel (bernsteinLeviScheme i ν a.roots)),
        ρ₀.IsIrreducible →
        ∀ j : ρ₀ ⟶ SmoothRep.restrictSubgroup
            (Plancherel.rationalCommonNormKernel (bernsteinLeviScheme i ν a.roots))
            a.representation,
          Function.Injective (SmoothRep.hom j) →
          let piOmega : SmoothRep.{0, uF, max uF uV} ℂ (rationalPoints G) :=
            (normalizedInductionFunctor (family.decomposition a.roots)
              (family.closedUnipotent a.roots)).obj
                (bernsteinLiteralLeviRep i ν a.roots
                  (rationalNormKernelSummandInduction (bernsteinLeviScheme i ν a.roots) ρ₀))
          ∃ hmem : bernsteinSaturatedBlockProperty i ν family
              (bernsteinInertialClass i ν family a) piOmega,
            let P : BernsteinSaturatedBlock i ν family (bernsteinInertialClass i ν family a) :=
              ⟨piOmega, hmem⟩
            (∀ (Y Z : BernsteinSaturatedBlock i ν family (bernsteinInertialClass i ν family a))
                (q : Y ⟶ Z), Epi q → ∀ f : P ⟶ Z, ∃ g : P ⟶ Y, g ≫ q = f) ∧
              Module.Finite (MonoidAlgebra ℂ (rationalPoints G)) piOmega.representation.asModule ∧
              ∀ (X Y : BernsteinSaturatedBlock i ν family (bernsteinInertialClass i ν family a))
                (f g : X ⟶ Y), f ≠ g → ∃ h : P ⟶ X, h ≫ f ≠ h ≫ g

end Langlands.CuspidalSupport
