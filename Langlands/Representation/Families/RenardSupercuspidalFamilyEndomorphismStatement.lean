import Langlands.Representation.Families.RenardFamilyParabolicFunctors
import Langlands.Representation.Exponents.ArbitraryParabolicLeviPoints
import Langlands.Representation.Exponents.LeviSupercuspidalInductionSupport
import Langlands.Representation.Plancherel.RationalCharacterValuation
import Langlands.Representation.Plancherel.UnramifiedUniversalTwist
import Langlands.GroupScheme.Reductive.Basic

/-!
# Renard VI.8.6 Example: endomorphisms of the induced universal supercuspidal family

For a rational parabolic `P = MN` of `G` and an irreducible supercuspidal representation
`(ρ, W)` of `M(F)`, let `B` be the published algebra of regular functions on the
unramified characters `X(M)` and `(ρ_B, W_B)` the universal unramified family
`B ⊗ W`, on which `m` acts by `χ_un(m) ⊗ ρ(m)`. Every endomorphism of the
`(G(F), B)`-module `V_B = i_P^G(ρ_B, W_B)` is the action of an element of `B`.
-/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct NNReal

namespace Langlands.Renard.AlgebraicFamily

open Langlands.Aubert.General Langlands.Aubert.General.RepresentedParabolic GroupScheme

set_option synthInstance.maxHeartbeats 400000 in
/-- VI.8.6 Example: for an irreducible supercuspidal representation `ρ` of `M(F)`, every
`G(F)`-equivariant `B`-linear endomorphism of the normalized induction `i_P^G(ρ_B)` of the
universal unramified family `ρ_B` over `B = ℂ[X(M)]` is the action of some `b ∈ B`. -/
def SupercuspidalFamilyEndomorphismStatement : Prop :=
  ∀ (k : Type u) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] [T2Space k]
    (G : GroupScheme (Spec (CommRingCat.of k))) (hG : IsConnectedReductive G),
    haveI := hG.isAffineHom
    letI : TopologicalSpace (rationalPoints G) := RationalPointFamily.pointTopology
    ∀ [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
      (P M U : GroupScheme (Spec (CommRingCat.of k)))
      (p : P ⟶ G) (l : M ⟶ P) (r : U ⟶ P)
      (hp : IsParabolicSubgroup p) (hl : IsRationalLeviSubgroup l)
      (hr : LeviSubgroup.IsGeometricUnipotentRadical r)
      (hmul : IsIso (subgroupMultiplication l r)),
      haveI := hl.isConnectedReductive.isAffineHom
      letI : TopologicalSpace (rationalPoints M) := leviPointTopology l hl
      haveI : LocallyCompactSpace (rationalPoints M) := leviPoints_locallyCompactSpace p l hp hl
      haveI : NonarchimedeanGroup (rationalPoints M) := leviPoints_nonarchimedeanGroup p l hp hl
      ∀ (W : Type v) [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ (rationalPoints M) W)
        (hσ : IsSmooth σ), (SmoothRep.of σ hσ).IsIrreducible →
        IsSupercuspidal (SmoothRep.of σ hσ) →
          let ν := fun χ : rationalCharacters M => (Plancherel.rationalNormCharacters M χ).toMul
          letI : AddCommGroup (Plancherel.unramifiedRegularFunctions ν ⊗[ℂ] W) :=
            TensorProduct.addCommGroup
          letI : Module (Plancherel.unramifiedRegularFunctions ν)
              (Plancherel.unramifiedRegularFunctions ν ⊗[ℂ] W) := TensorProduct.leftModule
          let ρB := Plancherel.universalUnramifiedRepresentation ν σ
          ∀ φ : LeviInduced p l r hp hr hl hmul ρB →ₗ[Plancherel.unramifiedRegularFunctions ν]
              LeviInduced p l r hp hr hl hmul ρB,
            (∀ (g : rationalPoints G) (f : LeviInduced p l r hp hr hl hmul ρB),
              φ (leviInducedRepresentation p l r hp hr hl hmul ρB g f) =
                leviInducedRepresentation p l r hp hr hl hmul ρB g (φ f)) →
            ∃ b : Plancherel.unramifiedRegularFunctions ν,
              ∀ f : LeviInduced p l r hp hr hl hmul ρB, φ f = b • f

end Langlands.Renard.AlgebraicFamily
