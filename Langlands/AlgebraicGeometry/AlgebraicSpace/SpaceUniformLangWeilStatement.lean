import Langlands.AlgebraicGeometry.AlgebraicSpace.SpaceMorphismProperties
import Langlands.Global.AdelicSpaceLevelPointsStatement
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# A uniform Lang–Weil estimate for smooth families of algebraic spaces over the integers

The algebraic-space form of Conrad's Lemma 4.6, which his proof of Theorem 5.9 needs: for a
smooth separated surjective map `f : Y ⟶ B` of algebraic spaces with `B` of finite presentation
over `ℤ`, whose fibres are geometrically connected of dimension `d`, the number of rational
points of the fibre over a point `b ∈ B(κ)` with values in a finite field `κ` differs from
`(#κ) ^ d` by at most `C (#κ) ^ (d - 1/2)`, with one constant `C` for all finite fields and all
such points.
-/

universe u

open CategoryTheory
open _root_.AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

/-- Conrad's Lemma 4.6 for algebraic spaces of finite presentation over `ℤ` (printed p.17,
proof of Theorem 5.9). Let `f : Y ⟶ B` be a separated, quasi-compact, surjective morphism of
algebraic spaces over `Spec ℤ` with geometrically connected fibres, smooth of relative
dimension `d` (an étale chart square with a smooth scheme map of relative dimension `d`), and
let `B` be quasi-separated and of finite type over `ℤ`. Then there is `C > 0` such that for
every finite field `κ` and every `κ`-point `b` of `B`, the number `N_b` of `κ`-points of `Y`
over `b` satisfies `|N_b - (#κ) ^ d| ≤ C (#κ) ^ (d - 1/2)`. -/
def SpaceUniformLangWeilStatement : Prop :=
  ∀ (B Y : AlgebraicSpace (Spec (CommRingCat.of (ULift.{u} ℤ)))) (f : Y ⟶ B) (d : ℕ),
    IsQuasiSeparated B → FiniteTypeOverRing (ULift.{u} ℤ) B →
    (∃ (U V : Over (Spec (CommRingCat.of (ULift.{u} ℤ))))
        (a : (schemeYoneda _).obj U ⟶ Y.presheaf) (b : (schemeYoneda _).obj V ⟶ B.presheaf)
        (φ : U ⟶ V),
        IsEtale a ∧ IsSurjective a ∧ IsEtale b ∧ SmoothOfRelativeDimension d φ.left ∧
          a ≫ hom f = (schemeYoneda _).map φ ≫ b) →
    IsSeparatedMorphism f → IsQuasiCompactMorphism f → IsSurjectiveMorphism f →
    HasGeometricallyConnectedFibres f →
    ∃ C : ℝ, 0 < C ∧ ∀ (κ : Type u) [Field κ] [Finite κ] [Algebra (ULift.{u} ℤ) κ]
      (x : RingPoints (ULift.{u} ℤ) B κ),
      |(Nat.card {y : RingPoints (ULift.{u} ℤ) Y κ // RingPoints.map f y = x} : ℝ) -
          (Nat.card κ : ℝ) ^ d| ≤
        C * (Nat.card κ : ℝ) ^ ((d : ℝ) - 1 / 2)

end Langlands.AlgebraicGeometry.AlgebraicSpace
