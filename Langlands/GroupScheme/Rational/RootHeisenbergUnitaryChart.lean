import Langlands.GroupScheme.Rational.RootHeisenbergChartPoints
import Langlands.Geometry.Building.MultipliableRootGroupCoordinates

/-! # Upgrade of unitary charts of Heisenberg normal forms

The statement that a rational homomorphism from the unitary parameters
`{(u, v) ∈ L² | v + σ(v) = u σ(u)}` of the chart form
`(u, v) ↦ incl(B v + H(u, u)) * sec(A u)` comes from an actual homomorphism
`R_{E/K} U_{L/E} ⟶ U` representing the root subgroup. The rational chart points
`HeisenbergNormalForm.chartPoint` are defined in
`Langlands.GroupScheme.Rational.RootHeisenbergChartPoints`.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.RelativeRoot

/-- **Upgrade of unitary charts.** Over an infinite field `K`, let `U = U_a` be a multipliable
relative root group with no higher multiples, with Heisenberg normal form `N` and weight
vector coordinates `e` (weight `a`, on the quotient) and `e'` (weight `2a`, on `U_{2a}`).
Let `E / K` be finite separable and `L / E` quadratic separable with conjugation `σ`. If a
homomorphism `φ` from the rational unitary parameters to `U(K)` has the chart form
`φ(u, v) = incl(B v + H(u, u)) * sec(A u)` with `K`-linear `A`, `B`, `K`-bilinear `H`, `A`
bijective and `B` bijective on the trace-zero line, then `φ` is the map on rational points of
an actual homomorphism `R_{E/K} U_{L/E} ⟶ U` whose composite with `j` represents `U_a`. -/
def UnitaryChartUpgradeStatement : Prop :=
  ∀ (K : Type u) [Field K] [Infinite K] (S : CommGroupScheme (Spec (CommRingCat.of K)))
    (G U U₂ : GroupScheme (Spec (CommRingCat.of K)))
    [IsAffineHom G.X.hom] [Smooth G.X.hom] [LocallyOfFiniteType G.X.hom]
    [IsAffineHom U.X.hom] [IsAffineHom U₂.X.hom]
    (i : S.toGrp ⟶ G) (a : characterLattice S)
    (j : U ⟶ G) (hj : (subgroup i a).IsRepresentedBy j)
    (j₂ : U₂ ⟶ G) (hj₂ : (subgroup i (2 • a)).IsRepresentedBy j₂)
    (C : DoubleRootCommutatorPairing i a hj hj₂) [IsAffineHom C.V.X.hom]
    (N : HeisenbergNormalForm C),
    IsSplitTorus S.toGrp → a ≠ 0 → (∀ n : ℕ, 3 ≤ n → n • a ∉ relativeRoots i) →
    ∀ {d m : ℕ}
    (e : ∀ T : Over (Spec (CommRingCat.of K)),
      (T ⟶ C.V.X) ≃* Multiplicative (Fin d → Γ(T.left, ⊤)))
    (e' : ∀ T : Over (Spec (CommRingCat.of K)),
      (T ⟶ U₂.X) ≃* Multiplicative (Fin m → Γ(T.left, ⊤))),
    IsWeightVectorCoordinates C.action a e →
    IsWeightVectorCoordinates (subgroupAction i (2 • a) j₂ hj₂) (2 • a) e' →
    ∀ (E L : Type u) [Field E] [Field L] [Algebra K E] [Algebra E L] [Algebra K L]
      [IsScalarTower K E L] [FiniteDimensional K E] [Algebra.IsSeparable K E]
      [Algebra.IsQuadraticExtension E L] [Algebra.IsSeparable E L]
      [FiniteDimensional K L] [Algebra.IsSeparable K L]
      (A : L →ₗ[K] (Fin d → K)) (B : L →ₗ[K] (Fin m → K))
      (H : L →ₗ[K] L →ₗ[K] (Fin m → K))
      (φ : SU3Root.rationalParameters E L →* rationalPoints U),
      Function.Bijective A →
      (∀ w : Fin m → K, ∃! z : L, z + SU3Root.conjugation E L z = 0 ∧ B z = w) →
      (∀ p, φ p = N.chartPoint e e' (A p.first) (B p.second + H p.first p.first)) →
      ∃ ψ : AffineWeil.groupScheme K E (SU3Root.unitaryParameterGroup E L) ⟶ U,
        (∀ p : SU3Root.rationalParameters E L,
          rationalPoints.map ψ
            ((AffineWeil.sectionsEquiv K E (SU3Root.unitaryParameterGroup E L)).symm
              ((SU3Root.unitaryRationalPointsEquiv E L).symm p)) = φ p) ∧
        (subgroup i a).IsRepresentedBy (ψ ≫ j)

end Langlands.GroupScheme.RelativeRoot
