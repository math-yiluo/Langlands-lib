import Langlands.Representation.Exponents.ArbitraryParabolicTempered

/-! # Reduction of normalized-exponent temperedness to standard parabolics

The standard family is defined by one fixed maximal split torus and generic
cocharacter whose dynamic parabolic is minimal. Both subgroup images must
agree with the shared standard functors and one simultaneous cocharacter
realization. The paired Markdown explains this derived form of Renard VII.2.1.
-/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme

/-- Admissibility and the normalized exponent condition on every actual
standard parabolic/Levi/split-component triple for one fixed standard family
are equivalent to the condition on all actual rational parabolics. -/
def NormalizedTemperedStandardReductionStatement : Prop :=
  ∀ (k : Type u) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] [T2Space k]
    (G : GroupScheme (Spec (CommRingCat.of k))) (hG : IsConnectedReductive G),
    haveI := hG.isAffineHom
    haveI := hG.smooth
    letI : TopologicalSpace (rationalPoints G) := RationalPointFamily.pointTopology
    ∀ [LocallyCompactSpace (rationalPoints G)]
      [NonarchimedeanGroup (rationalPoints G)]
      (T : CommGroupScheme (Spec (CommRingCat.of k))) (i : T.toGrp ⟶ G)
      (ν : cocharacterLattice T),
      IsMaximalSplitTorus i →
      IsGenericCocharacter i ν →
      IsMinimalParabolicFunctor (Dynamic.parabolic (CommGroupScheme.groupHom ν ≫ i)) →
      ∀ π : SmoothRep.{0, u, v} ℂ (rationalPoints G),
        IsNormalizedExponentTempered hG π ↔
          IsAdmissible π.representation ∧
            ∀ (J : Set (characterLattice T)) (ζ : cocharacterLattice T),
              IsStandardCocharacter i ν J ζ →
              ∀ (P M : GroupScheme (Spec (CommRingCat.of k)))
                (A : CommGroupScheme (Spec (CommRingCat.of k)))
                (p : P ⟶ G) (l : M ⟶ P) (a : A.toGrp ⟶ M)
                (hp : IsParabolicSubgroup p) (hl : IsRationalLeviSubgroup l)
                (ha : IsSplitComponent a),
                SubgroupFunctor.range p = standardParabolic i ν J →
                SubgroupFunctor.range (l ≫ p) = standardLevi i ν J →
                SubgroupFunctor.range p =
                  Dynamic.parabolic (CommGroupScheme.groupHom ζ ≫ i) →
                SubgroupFunctor.range (l ≫ p) =
                  Dynamic.centralizer (CommGroupScheme.groupHom ζ ≫ i) →
                SatisfiesNormalizedExponentConeCondition p l a hp hl ha π

end Langlands.Aubert.General.RepresentedParabolic
