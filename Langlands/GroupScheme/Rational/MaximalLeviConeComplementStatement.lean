import Langlands.GroupScheme.Rational.ParabolicRootPresentation

/-! # Parabolics with a maximal Levi are determined by a missed direction

In the proof of Renard VII.1.3 (PDF p.231) the maximality of `M` enters through the fact
that `A_M / A_G` has dimension one. A parabolic with Levi `M` then has a single restricted
simple root on `A_M`, up to positive multiples, and the two parabolics with Levi `M` have
opposite positive cones. This module states the consequence used for the exponents: a
nonzero real character of `A_M` vanishing on the central directions of `G` that lies
outside the positive cones of two parabolics with Levi `M` forces the two parabolics, and
their unipotent radicals, to coincide. Nothing is proved here.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TensorProduct
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

open RealTorusSpace

/-- Let `P = MN` be an actual maximal proper rational parabolic of a connected reductive
group `G`, with rational Levi `M` and split component `a : A ⟶ M`. Let `x` be a nonzero real
character of `A` whose pairing with every cocharacter of `A` that is central in `G`
vanishes. If two rational parabolics `Q₁, Q₂` of `G` have Levi factors with source `M` and
the same composite into `G` as `l ≫ p`, and `x` lies in neither positive cone of
compatible root presentations for `a`, then `Q₁` and `Q₂` have the same image in `G`, and
so do their geometric unipotent radicals. -/
def MaximalLeviConeComplementStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))
    (hG : IsConnectedReductive G),
    haveI := hG.isAffineHom
    haveI := hG.smooth
    ∀ (P M : GroupScheme (Spec (CommRingCat.of k)))
      (A : CommGroupScheme (Spec (CommRingCat.of k)))
      (p : P ⟶ G) (l : M ⟶ P) (a : A.toGrp ⟶ M),
      IsParabolicSubgroup p → IsRationalLeviSubgroup l → ¬ IsIso p →
      (∀ (Q' : GroupScheme (Spec (CommRingCat.of k))) (q' : Q' ⟶ G) (j : P ⟶ Q'),
        IsParabolicSubgroup q' → j ≫ q' = p → IsIso j ∨ IsIso q') →
      IsSplitComponent a →
      ∀ x : Vstar A, x ≠ 0 →
        (∀ ν : cocharacterLattice A, IsCentral (CommGroupScheme.groupHom ν ≫ a ≫ l ≫ p) →
          pair A x ((1 : ℝ) ⊗ₜ[ℤ] ν) = 0) →
        ∀ (Q₁ U₁ Q₂ U₂ : GroupScheme (Spec (CommRingCat.of k)))
          (q₁ : Q₁ ⟶ G) (lQ₁ : M ⟶ Q₁) (rQ₁ : U₁ ⟶ Q₁)
          (q₂ : Q₂ ⟶ G) (lQ₂ : M ⟶ Q₂) (rQ₂ : U₂ ⟶ Q₂),
          LeviSubgroup.IsGeometricUnipotentRadical rQ₁ →
          LeviSubgroup.IsGeometricUnipotentRadical rQ₂ →
          lQ₁ ≫ q₁ = l ≫ p → lQ₂ ≫ q₂ = l ≫ p →
          ∀ (pres₁ : ParabolicRootPresentation q₁ lQ₁ a)
            (pres₂ : ParabolicRootPresentation q₂ lQ₂ a),
            x ∉ pres₁.positiveCone → x ∉ pres₂.positiveCone →
              SubgroupFunctor.range q₁ = SubgroupFunctor.range q₂ ∧
                SubgroupFunctor.range (rQ₁ ≫ q₁) = SubgroupFunctor.range (rQ₂ ≫ q₂)

end Langlands.GroupScheme
