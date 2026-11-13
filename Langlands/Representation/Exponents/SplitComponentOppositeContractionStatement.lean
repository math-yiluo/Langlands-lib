import Langlands.Representation.Exponents.PresentationConeContractionStatement

/-! # Uniform two-sided contraction by `A^+(ε)` of compact subsets of `N(F)` and `N̄(F)`

Derived from Renard 2026, V.5.2 Théorème (iii) (printed p.123 / PDF p.129), in the form
used in the proof of Remarque 3 of VI.9.1 (printed p.198 / PDF p.204): for opposite
parabolics `P = MN` and `P̄ = MN̄` of `G` with split component `A`, every compact subset
of `N(F)` is conjugated by `t ∈ A^+(ε)` into any prescribed neighbourhood of `1`, and
every compact subset of `N̄(F)` is conjugated by `t⁻¹` into it, once `ε` is small enough.
This proposition-valued definition states the target; it supplies no proof.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme

/-- Derived two-sided neighbourhood formulation of Renard V.5.2 (iii) on all of `A^+(ε)`.
Let `P = MN` and `P̄ = MN̄` be parabolics of `G` with the same rational Levi `M`, unipotent
radicals `N` and `N̄`, and `P(F) ∩ P̄(F) = M(F)`. Let `a : A → M` be a split component with a
compatible root presentation of `P`, and let `Δ(P)` be the restrictions to `A` of the
simple roots outside the presentation's subset `J`; `t ∈ A(F)` acts on `G(F)` through the
composite `A → M → P → G`. For every compact subset `C` of `N(F)`, every compact subset
`C̄` of `N̄(F)` and every neighbourhood `L` of `1` in `G(F)`, there is `ε > 0` such that
for every `t ∈ A^+(ε) = {t ∈ A(F) | |α(t)|_F < ε for α ∈ Δ(P)}` we have `t c t⁻¹ ∈ L`
for `c ∈ C` and `t⁻¹ c t ∈ L` for `c ∈ C̄`. -/
def SplitComponentOppositeContractionStatement : Prop :=
  ∀ (k : Type u) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] [T2Space k]
    (G : GroupScheme (Spec (CommRingCat.of k))) (hG : IsConnectedReductive G),
    haveI := hG.isAffineHom
    letI : TopologicalSpace (rationalPoints G) := RationalPointFamily.pointTopology
    ∀ [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
      (P Pbar M N Nbar : GroupScheme (Spec (CommRingCat.of k)))
      (p : P ⟶ G) (m : M ⟶ P) (n : N ⟶ P)
      (_hp : IsParabolicSubgroup p) (_hm : IsRationalLeviSubgroup m)
      (_hn : LeviSubgroup.IsGeometricUnipotentRadical n)
      (_hmul : IsIso (subgroupMultiplication m n))
      (pbar : Pbar ⟶ G) (mbar : M ⟶ Pbar) (nbar : Nbar ⟶ Pbar)
      (_hpbar : IsParabolicSubgroup pbar) (_hmbar : IsRationalLeviSubgroup mbar)
      (_hnbar : LeviSubgroup.IsGeometricUnipotentRadical nbar)
      (_hmulbar : IsIso (subgroupMultiplication mbar nbar)),
      mbar ≫ pbar = m ≫ p →
      pointImage p ⊓ pointImage pbar = pointImage (m ≫ p) →
      ∀ (A : CommGroupScheme (Spec (CommRingCat.of k))) (a : A.toGrp ⟶ M)
        (pres : ParabolicRootPresentation p m a),
        let Δ : Set (characterLattice A) :=
          (fun α => pres.data.f ≫ α) ''
            (simpleRelativeRoots pres.data.i pres.data.ν \ pres.data.J)
        let incG : rationalPoints A.toGrp →* rationalPoints G :=
          rationalPoints.map (a ≫ m ≫ p)
        ∀ C : Set (rationalPoints G), IsCompact C → C ⊆ pointImage (n ≫ p) →
        ∀ Cbar : Set (rationalPoints G), IsCompact Cbar → Cbar ⊆ pointImage (nbar ≫ pbar) →
        ∀ L ∈ nhds (1 : rationalPoints G), ∃ ε : ℝ, 0 < ε ∧
          ∀ t : rationalPoints A.toGrp,
            (∀ α ∈ Δ, CocharacterUniformizer.characterNorm k A α t < ε) →
            (∀ c ∈ C, incG t * c * (incG t)⁻¹ ∈ L) ∧
              (∀ c ∈ Cbar, (incG t)⁻¹ * c * incG t ∈ L)

end Langlands.Aubert.General.RepresentedParabolic
