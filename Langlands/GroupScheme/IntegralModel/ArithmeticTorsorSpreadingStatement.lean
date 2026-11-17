import Langlands.GroupScheme.IntegralModel.ArithmeticHomSpreading
import Langlands.AlgebraicGeometry.PointTopology.RingPointBaseChange
import Mathlib.CategoryTheory.Monoidal.Cartesian.Mod

/-! # Statement: torsors spread out over rings of `S`-integers -/

universe u

open CategoryTheory AlgebraicGeometry
open Langlands.Global Langlands.AlgebraicGeometry.PointTopology
open Langlands.GroupScheme.IntegralModel.ArithmeticSpreading

namespace Langlands.GroupScheme

/-- **Spreading out torsors** (EGA IV₃, 8.8.2, 8.10.5 and 11.2.6, as used for Conrad,
*Reductive group schemes* (2014), Exercise 5.5.3(iii)). Let `F` be a number field, `S` a
finite set of finite places, `G` a group scheme over `Spec F` with an integral model `M`
over the ring of `S`-integers, and `X` an fpqc torsor under `G`. Then for some finite
`T ⊇ S` there is an fpqc torsor `Y` over the ring of `T`-integers under the enlarged model
of `G`, whose base change to `Spec F` is isomorphic to `X` as a scheme over `Spec F`. -/
def ArithmeticTorsorSpreadingStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] (S : Finset (FinitePlace F))
    (G : GroupScheme (Spec (CommRingCat.of F)))
    (M : IntegralModel ((S : Set (FinitePlace F)).integer F) F G)
    (X : Over (Spec (CommRingCat.of F))) [ModObj G.X X],
    Flat X.hom → Surjective X.hom → QuasiCompact X.hom →
    IsIso (ModObj.leftSMul G.X X) →
    ∃ (T : Finset (FinitePlace F)) (hST : S ⊆ T)
      (Y : Over (Spec (CommRingCat.of ((T : Set (FinitePlace F)).integer F))))
      (_ : ModObj (enlargeModel F M hST).group.X Y),
      Flat Y.hom ∧ Surjective Y.hom ∧ QuasiCompact Y.hom ∧
      IsIso (ModObj.leftSMul (enlargeModel F M hST).group.X Y) ∧
      Nonempty (ringBaseChange ((T : Set (FinitePlace F)).integer F) F Y ≅ X)

end Langlands.GroupScheme
