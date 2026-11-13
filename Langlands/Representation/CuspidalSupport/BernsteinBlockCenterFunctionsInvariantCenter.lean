import Langlands.Representation.CuspidalSupport.BernsteinRepresentedInduction
import Langlands.Representation.CuspidalSupport.RationalSummandSmallProgeneratorStatement
import Langlands.Representation.Plancherel.UnramifiedOperatorFamilies

/-! # `ℨ_D^{W(D)} ⊂ ℨ_Ω` (Renard VI.10.4, proof of the Theorem)

For an actual standard cuspidal datum `a = (M, ρ)`, an irreducible `ρ₀` of `⁰M` embedded in
`ρ|_{⁰M}`, `Π_D = ind_{⁰M}^M ρ₀` and `i_P^G` the actual represented normalized induction along
the standard parabolic of `a`: every element of the centre `ℨ_D` of `End_M(Π_D)` whose scalars
on the `ρ ⊗ ω` are invariant under association (that is, under `W(D)`) induces a central
element of `End_G(i_P^G Π_D)`.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology Langlands.Plancherel
open Langlands.Aubert.General Langlands.Aubert.General.RationalPointFamily
open Langlands.GroupScheme
open scoped CategoryTheory.MonObj

namespace Langlands.CuspidalSupport

universe uF uV

/-- Renard VI.10.4, proof of the Theorem, the inclusion `ℨ_D^{W(D)} ⊂ ℨ_Ω` (printed
pp.211–212 / PDF pp.217–218), for the actual standard cuspidal data of a standard family. Fix
a cuspidal datum `a = (M, ρ)` (carriers in `Type (max uF uV)`), `X = X(M)`, `ρ ⊗ ω` for
`ω ∈ X`, and `ω ~ ω'` when `(M, ρ ⊗ ω)` and `(M, ρ ⊗ ω')` are associated, exactly as in
`BernsteinBlockCenterFunctionsStatement`. Let `ρ₀` be an irreducible smooth representation of
`⁰M` with an injective `⁰M`-map `j : ρ₀ → ρ|_{⁰M}`, `Π_D = ind_{⁰M}^M ρ₀` and `I` the actual
represented normalized induction `bernsteinStandardRepresentedInductionFunctor` along the
standard parabolic of `a`. Let `ζ` be central in `End_M(Π_D)` and suppose that whenever
`ω ~ ω'` and `ζ` acts by a scalar `c` on all maps `Π_D → ρ ⊗ ω`, it acts by the same `c` on all
maps `Π_D → ρ ⊗ ω'` (the `W(D)`-invariance of the function of `ζ` on `Irr(M)_D`). Then
`I(ζ)` is central in `End_G(I(Π_D))`. -/
def BernsteinInvariantCenterInclusionStatement : Prop :=
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
      ∀ (ρ₀ : SmoothRep.{0, uF, max uF uV} ℂ
          (rationalCommonNormKernel (bernsteinLeviScheme i ν a.roots))),
        ρ₀.IsIrreducible →
        ∀ (j : ρ₀ ⟶ SmoothRep.restrictSubgroup
          (rationalCommonNormKernel (bernsteinLeviScheme i ν a.roots)) a.representation),
        Function.Injective (SmoothRep.hom j) →
        let X := unramifiedCharacters
          (fun χ => (rationalNormCharacters (bernsteinLeviScheme i ν a.roots) χ).toMul)
        let twist : X →
            SmoothRep.{0, uF, max uF uV} ℂ (rationalPoints (bernsteinLeviScheme i ν a.roots)) :=
          fun ω => rationalUnramifiedTwist (bernsteinLeviScheme i ν a.roots) ω a.representation
        let Assoc : X → X → Prop := fun ω ω' =>
          ∃ c : RationalLeviConjugacy (Standard.leviHom i ν (rootSet i ν a.roots))
              (Standard.leviHom i ν (rootSet i ν a.roots)),
            Nonempty (twist ω ≅ rationalIsoPullback c.iso (twist ω'))
        let piD := rationalNormKernelSummandInduction (bernsteinLeviScheme i ν a.roots) ρ₀
        let I := bernsteinStandardRepresentedInductionFunctor.{uF, uV} i ν family a.roots
        ∀ ζ ∈ Subring.center (End piD),
          (∀ ω ω', Assoc ω ω' → ∀ c : ℂ, (∀ φ : piD ⟶ twist ω, ζ ≫ φ = c • φ) →
            ∀ φ' : piD ⟶ twist ω', ζ ≫ φ' = c • φ') →
          I.map ζ ∈ Subring.center (End (I.obj piD))

end Langlands.CuspidalSupport
