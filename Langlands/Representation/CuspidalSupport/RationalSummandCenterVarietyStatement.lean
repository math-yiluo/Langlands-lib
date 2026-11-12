import Langlands.Representation.CuspidalSupport.RationalSummandCenterGroupAlgebraStatement
import Langlands.Representation.CuspidalSupport.RationalInertiaOrbitTorusStatement

/-! Renard VI.4.4, Proposition, last sentence: the center `Z` of `A = End(ind_{H⁰}^G ρ)` is
isomorphic to the algebra of polynomial functions on the variety `Irr(G)[π]`, a central element
going to the function whose value at the point `π ⊗ ω` is the scalar by which it acts on
`Hom_G(ind_{H⁰}^G ρ, π ⊗ ω)`. -/

noncomputable section

open CategoryTheory AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology Langlands.Plancherel
open scoped CategoryTheory.MonObj

namespace Langlands.CuspidalSupport

universe uF uV

open Aubert.General Aubert.General.RationalPointFamily GroupScheme Induction

/-- Renard VI.4.4, Proposition, "Ceci montre que `Z` est isomorphe à l'algèbre des fonctions de
la variété `Irr(G)[π]`", in the setting of the published `RationalSummandCenterGroupAlgebraStatement`
(irreducible cuspidal `π`, irreducible smooth `ρ` of `H⁰` occurring in `Res π`,
`I = ind_{H⁰}^G ρ`). Write `X(G)` for the unramified characters, `Stab = {s | π ⊗ s ≃ π}` and
`F^S` for the `Stab`-invariant elements of the published algebra `unramifiedRegularFunctions` of
polynomial functions on `X(G)`, the algebra of polynomial functions on `Irr(G)[π] ≃ X(G)/Stab`
(V.2.7). There is an injective `ℂ`-algebra homomorphism `Ψ` from the center of `End I` to the
functions on `X(G)`, with range exactly `F^S`, such that every central `z` acts on every map
`I → π ⊗ ω`, by precomposition, as multiplication by `Ψ z ω`. -/
def RationalSummandCenterVarietyStatement : Prop :=
  ∀ (F : Type uF) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) (hG : IsConnectedReductive G)
    (S : CommGroupScheme (Spec (CommRingCat.of F))) (i : S.toGrp ⟶ G)
    (hi : IsMaximalSplitTorus i),
    haveI := hG.isAffineHom
    haveI : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
    haveI := hG.smooth
    haveI := hi.isSplitSubtorus.mono
    letI : TopologicalSpace (GroupScheme.rationalPoints G) := rationalPointTopology F G.X
    haveI : IsTopologicalGroup (GroupScheme.rationalPoints G) :=
      rationalPoint_isTopologicalGroup F G
    ∀ [LocallyCompactSpace (GroupScheme.rationalPoints G)]
      [NonarchimedeanGroup (GroupScheme.rationalPoints G)]
      [T2Space (GroupScheme.rationalPoints G)]
      (ν : cocharacterLattice S) (hν : IsGenericCocharacter i ν)
      (hStandard : StandardCocharacterStatement.{uF})
      (hRoots : HasRelativeRootSystem i)
      (hU : ∀ I, IsClosed (unipotent i ν I : Set (GroupScheme.rationalPoints G))),
      letI := simpleRelativeRootFintype i hRoots hi.isSplitSubtorus.1 ν
      let h := isSemidirectDecomposition_of_standardCocharacterStatement
        i ν hStandard hG hi hν
      ∀ π : SmoothRep.{0, uF, uV} ℂ (GroupScheme.rationalPoints G),
        π.IsIrreducible →
        IsCuspidal (parabolic i ν) (levi i ν) (unipotent i ν) h hU π →
        ∀ ρ : SmoothRep.{0, uF, uV} ℂ (rationalCommonNormKernel G),
          ρ.IsIrreducible →
          ∀ j : ρ ⟶ SmoothRep.restrictSubgroup (rationalCommonNormKernel G) π,
            Function.Injective (SmoothRep.hom j) →
            let I := (compactInductionFunctor (rationalCommonNormKernel G)).obj
              (SmoothRep.toRep.obj ρ)
            let X := unramifiedCharacters (fun χ => (rationalNormCharacters G χ).toMul)
            let Stab : Set X := {s | Nonempty (rationalUnramifiedTwist G s π ≅ π)}
            ∃ Ψ : Subalgebra.center ℂ (End I) →ₐ[ℂ] (X → ℂ),
              Function.Injective Ψ ∧
              Set.range Ψ =
                {φ | φ ∈ unramifiedRegularFunctions
                    (fun χ => (rationalNormCharacters G χ).toMul) ∧
                  ∀ s ∈ Stab, ∀ χ, φ (χ * s) = φ χ} ∧
              ∀ (z : Subalgebra.center ℂ (End I)) (ω : X)
                (φ : I ⟶ rationalUnramifiedTwist G ω (rationalInertiaBaseLift G π)),
                (z : End I) ≫ φ = Ψ z ω • φ

end Langlands.CuspidalSupport
