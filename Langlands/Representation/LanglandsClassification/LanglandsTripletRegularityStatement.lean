import Langlands.Representation.LanglandsClassification.LanglandsTriplet
import Langlands.Representation.Intertwining.PQRegularity
import Langlands.Representation.Category.Twist
import Langlands.GroupScheme.Reductive.Basic

/-! # `PP̄`-regularity of Langlands triplets (Renard VII.4.1, Lemma)

For a Langlands triplet `(P = MN, σ, ψ)` and an opposite parabolic `P̄ = M N̄`, the twist
`σ ⊗ ψ` is `PP̄`-regular, and the space of intertwining maps `i_P^G(σ ⊗ ψ) → i_{P̄}^G(σ ⊗ ψ)`
has dimension one.
-/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme

/-- Renard VII.4.1, Lemma: let `(P = MN, σ, ψ)` be a Langlands triplet for a fixed minimal
parabolic, and let `P̄ = M N̄` be an actual rational parabolic with the same Levi and
`P(F) ∩ P̄(F) = M(F)`. Then `σ ⊗ ψ` is `PP̄`-regular, and the intertwining maps
`i_P^G(σ ⊗ ψ) → i_{P̄}^G(σ ⊗ ψ)` form a complex vector space of dimension one: there is a
nonzero intertwining operator, unique up to a scalar. -/
def LanglandsTripletOppositeRegularityStatement : Prop :=
  ∀ (k : Type u) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] [T2Space k]
    (G : GroupScheme (Spec (CommRingCat.of k))) (hG : IsConnectedReductive G),
    haveI := hG.isAffineHom
    letI : TopologicalSpace (rationalPoints G) := RationalPointFamily.pointTopology
    ∀ [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
      (T : CommGroupScheme (Spec (CommRingCat.of k))) (i : T.toGrp ⟶ G)
      [Mono i.hom.hom.left] (ν : cocharacterLattice T) (D : RelativeRootReflectionData i)
      (P M U : GroupScheme (Spec (CommRingCat.of k)))
      (A : CommGroupScheme (Spec (CommRingCat.of k)))
      (p : P ⟶ G) (l : M ⟶ P) (r : U ⟶ P) (a : A.toGrp ⟶ M)
      (hp : IsParabolicSubgroup p) (hl : IsRationalLeviSubgroup l)
      (hr : LeviSubgroup.IsGeometricUnipotentRadical r)
      (hmul : IsIso (subgroupMultiplication l r)) (ha : IsSplitComponent a)
      (J : Set (characterLattice T)) (f : A ⟶ T)
      (σ : letI := leviPointTopology l hl; SmoothRep.{0, u, v} ℂ (rationalPoints M))
      (ψ : leviUnramifiedCharacters l hl)
      (Pbar Ubar : GroupScheme (Spec (CommRingCat.of k)))
      (pbar : Pbar ⟶ G) (lbar : M ⟶ Pbar) (rbar : Ubar ⟶ Pbar)
      (hpbar : IsParabolicSubgroup pbar) (hlbar : IsRationalLeviSubgroup lbar)
      (hrbar : LeviSubgroup.IsGeometricUnipotentRadical rbar)
      (hmulbar : IsIso (subgroupMultiplication lbar rbar)),
      lbar ≫ pbar = l ≫ p →
      pointImage p ⊓ pointImage pbar = pointImage (l ≫ p) →
      IsLanglandsTriplet i ν D p l a hp hl ha J f σ ψ →
        letI : TopologicalSpace (rationalPoints M) := leviPointTopology l hl
        haveI : NonarchimedeanGroup (rationalPoints M) :=
          leviPoints_nonarchimedeanGroup p l hp hl
        let τ := σ.twist ψ.val.toMonoidHom (Plancherel.unramifiedCharacter_isOpen_ker _ ψ)
        IsPQRegular p l r hp hr hl hmul pbar lbar rbar hpbar hrbar hlbar hmulbar a τ ∧
          Module.finrank ℂ
            (((leviInductionFunctor p l r hp hr hl hmul).obj τ).representation.IntertwiningMap
              ((leviInductionFunctor pbar lbar rbar hpbar hrbar hlbar hmulbar).obj τ).representation)
            = 1

end Langlands.Aubert.General.RepresentedParabolic
