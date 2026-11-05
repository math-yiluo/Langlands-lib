import Langlands.Representation.Exponents.ArbitraryParabolicInduction
import Langlands.GroupScheme.Reductive.Basic

/-! # Characteristic-space decompositions and exponents under induction and restriction

Renard 2026, VII.1.1 (printed pp.220–221/PDF pp.226–227): the direct-sum decomposition
(VII.1.1.1) of a normalized Jacquet module into characteristic spaces of the split
component, finiteness of its exponents in finite length, the `P = G` decomposition, and
both parts of the lemma comparing exponents of `W` and `i_P^G W`, and of `V` and
`r_P^G V`. The inclusion `A_G ⊂ A_M` enters as a point-level homomorphism compatible with
the two inclusions into `G(F)`.
-/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme

/-- Renard VII.1.1: (VII.1.1.1) with finiteness in finite length, the `P = G` remark,
and parts (i) and (ii) of the lemma, for every represented parabolic of a connected
reductive group over a nonarchimedean local field. -/
def ArbitraryParabolicExponentStatement : Prop :=
  ∀ (k : Type u) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] [T2Space k]
    (G : GroupScheme (Spec (CommRingCat.of k))) (hG : IsConnectedReductive G),
    haveI := hG.isAffineHom
    letI : TopologicalSpace (rationalPoints G) := RationalPointFamily.pointTopology
    ∀ [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)],
      (∀ (P M U : GroupScheme (Spec (CommRingCat.of k)))
        (A : CommGroupScheme (Spec (CommRingCat.of k)))
        (p : P ⟶ G) (l : M ⟶ P) (r : U ⟶ P) (a : A.toGrp ⟶ M)
        (hp : IsParabolicSubgroup p) (hl : IsRationalLeviSubgroup l)
        (hr : LeviSubgroup.IsGeometricUnipotentRadical r)
        (hmul : IsIso (subgroupMultiplication l r)) (ha : IsSplitComponent a)
        (π : SmoothRep.{0, u, v} ℂ (rationalPoints G)),
        π.IsAdmissible →
          iSupIndep (fun χ : normalizedJacquetExponents p l r hp hl hr hmul ha π =>
              (normalizedJacquetWeightSpace p l r hp hl hr hmul ha π χ).toSubmodule) ∧
            (⨆ χ : normalizedJacquetExponents p l r hp hl hr hmul ha π,
              (normalizedJacquetWeightSpace p l r hp hl hr hmul ha π χ).toSubmodule) = ⊤ ∧
            (π.HasFiniteLength → (normalizedJacquetExponents p l r hp hl hr hmul ha π).Finite)) ∧
      (∀ (AG : CommGroupScheme (Spec (CommRingCat.of k))) (aG : AG.toGrp ⟶ G)
        (haG : IsSplitComponent aG) (V : SmoothRep.{0, u, v} ℂ (rationalPoints G)),
        V.IsAdmissible →
          iSupIndep (fun χ : groupExponents haG V => (groupWeightSpace haG V χ).toSubmodule) ∧
            (⨆ χ : groupExponents haG V, (groupWeightSpace haG V χ).toSubmodule) = ⊤) ∧
      (∀ (P M U : GroupScheme (Spec (CommRingCat.of k)))
        (A AG : CommGroupScheme (Spec (CommRingCat.of k)))
        (p : P ⟶ G) (l : M ⟶ P) (r : U ⟶ P) (a : A.toGrp ⟶ M) (aG : AG.toGrp ⟶ G)
        (hp : IsParabolicSubgroup p) (hl : IsRationalLeviSubgroup l)
        (hr : LeviSubgroup.IsGeometricUnipotentRadical r)
        (hmul : IsIso (subgroupMultiplication l r)) (ha : IsSplitComponent a)
        (haG : IsSplitComponent aG) (e : rationalPoints AG.toGrp →* rationalPoints A.toGrp),
        (∀ t : rationalPoints AG.toGrp,
          ((splitComponentPointsMap (l ≫ p) a (e t) : pointImage (l ≫ p)) :
              rationalPoints G) = rationalPoints.map aG t) →
        (∀ (W : SmoothRep.{0, u, v} ℂ (pointImage (l ≫ p)))
          (χ : rationalPoints AG.toGrp →* ℂˣ),
          W.IsAdmissible →
            groupWeightSpace haG ((inductionFunctor p l r hp hr hl hmul).obj W) χ ≠ ⊥ →
              ∃ ψ : rationalPoints A.toGrp →* ℂˣ,
                IsLeviExponent (l ≫ p) ha W ψ ∧ ψ.comp e = χ) ∧
        (∀ (π : SmoothRep.{0, u, v} ℂ (rationalPoints G)) (χ : rationalPoints A.toGrp →* ℂˣ),
          π.IsAdmissible →
            IsNormalizedJacquetExponent p l r hp hl hr hmul ha π χ →
              IsGroupExponent haG π (χ.comp e)))

end Langlands.Aubert.General.RepresentedParabolic
