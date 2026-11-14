import Langlands.Geometry.Building.RootDatumValuation
import Langlands.GroupScheme.Rational.RelativeRootGroupAbsoluteGenerationStatement

/-! # Rational points of relative root groups in a split group: statement -/

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme

namespace Langlands.Geometry.Building

/-- **Ordered products of absolute root points.** Let `G` be a connected reductive group over
a field `K` with a split maximal torus `j : T ⟶ G`, let `S` be a split torus with a
homomorphism `f : S ⟶ T`, and let `a ≠ 0` be a character of `S`. Enumerate injectively, in
any order, the roots `β` of `T` whose restriction `f ≫ β` along `f` is a positive integral
multiple of `a`. Then a rational point of `G` lies in the relative root group of `a` for the
composite `groupHom f ≫ j` exactly when it is the ordered product of one rational point of
each absolute root group `U_β`, and these factors are unique.

Borel–Tits, *Groupes réductifs* (1965), proof of Théorème 3.17 (printed p. 82), with 2.3,
3.8 (ii), 3.11 and 5.2. -/
def SplitRelativeRootGroupProductStatement : Prop :=
  ∀ (K : Type u) [Field K]
    (G : GroupScheme (Spec (CommRingCat.of K))) (hG : IsConnectedReductive G),
    letI : IsAffineHom G.X.hom := hG.isAffineHom
    ∀ (S T : CommGroupScheme (Spec (CommRingCat.of K)))
      (j : T.toGrp ⟶ G) (f : S ⟶ T),
      IsSplitTorus T.toGrp → IsMaximalTorus j → IsSplitTorus S.toGrp →
      ∀ (a : characterLattice S), a ≠ 0 →
      ∀ (n : ℕ) (β : Fin n → characterLattice T), Function.Injective β →
        (∀ χ : characterLattice T, χ ∈ Set.range β ↔
          (χ ∈ roots j ∧ ∃ m : ℕ, 0 < m ∧ f ≫ χ = m • a)) →
        (∀ g : rationalPoints G,
          g ∈ rootGroupPoints (CommGroupScheme.groupHom f ≫ j) a ↔
            ∃ x : (r : Fin n) → rootGroupPoints j (β r),
              g = (List.ofFn fun r => (x r : rationalPoints G)).prod) ∧
        ∀ x y : (r : Fin n) → rootGroupPoints j (β r),
          (List.ofFn fun r => (x r : rationalPoints G)).prod =
              (List.ofFn fun r => (y r : rationalPoints G)).prod →
            x = y

end Langlands.Geometry.Building
