import Langlands.Representation.Exponents.ArbitraryParabolicLeviPoints
import Langlands.GroupScheme.Rational.ParabolicRootPresentation
import Langlands.Geometry.Building.CocharacterUniformizer
import Langlands.GroupScheme.Reductive.Basic

/-! # Uniform contraction of compact subsets of `N(F)` by `C_A^+(ε)`

Derived from Renard 2026, V.5.2 Théorème (iii) (printed p.123/PDF p.129), in
neighbourhood form for compatible represented parabolics: for a parabolic `P = MN` of `G` with split
component `A` and every compact subset `Γ` of `N(F)`, the elements of `C_A^+(ε)` conjugate
`Γ` into any prescribed neighbourhood of `1` once `ε` is small enough.
This proposition-valued definition states the target; it supplies no proof.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme

/-- Derived neighbourhood formulation of Renard V.5.2 (iii) for represented parabolics: let `P = MN`
be a parabolic of `G` with rational Levi `M` and unipotent radical `N`, let `a : A → M` be a
split component with a compatible root presentation of `P`, and let `Δ(P)` be the
restrictions to `A` of the simple roots outside the presentation's subset `J`. For every
compact subset `C` of `N(F)` and every neighbourhood `L` of `1` in `G(F)` there is `ε > 0`
such that `t c t⁻¹ ∈ L` for every `t ∈ C_A^+(ε)` and every `c ∈ C`, where `t` acts through
the composite `A → M → P → G`. -/
def PresentationConeContractionStatement : Prop :=
  ∀ (k : Type u) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] [T2Space k]
    (G : GroupScheme (Spec (CommRingCat.of k))) (hG : IsConnectedReductive G),
    haveI := hG.isAffineHom
    letI : TopologicalSpace (rationalPoints G) := RationalPointFamily.pointTopology
    ∀ [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
      (P M N : GroupScheme (Spec (CommRingCat.of k)))
      (p : P ⟶ G) (m : M ⟶ P) (n : N ⟶ P)
      (_hp : IsParabolicSubgroup p) (_hm : IsRationalLeviSubgroup m)
      (_hn : LeviSubgroup.IsGeometricUnipotentRadical n)
      (_hmul : IsIso (subgroupMultiplication m n))
      (A : CommGroupScheme (Spec (CommRingCat.of k))) (a : A.toGrp ⟶ M)
      (pres : ParabolicRootPresentation p m a),
      let Δ : Set (characterLattice A) :=
        (fun α => pres.data.f ≫ α) ''
          (simpleRelativeRoots pres.data.i pres.data.ν \ pres.data.J)
      ∀ C : Set (rationalPoints G), IsCompact C → C ⊆ pointImage (n ≫ p) →
        ∀ L ∈ nhds (1 : rationalPoints G), ∃ ε : ℝ, 0 < ε ∧
          ∀ t ∈ CocharacterUniformizer.CAepsilon k A Δ ε, ∀ c ∈ C,
            rationalPoints.map (a ≫ m ≫ p) t * c * (rationalPoints.map (a ≫ m ≫ p) t)⁻¹ ∈ L

end Langlands.Aubert.General.RepresentedParabolic
