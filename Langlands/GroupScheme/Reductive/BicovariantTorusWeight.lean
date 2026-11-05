import Langlands.GroupScheme.Reductive.AffineInducedRegular
import Langlands.GroupScheme.InnerAutomorphism

/-! # Weights forced by bi-covariant coordinates at unit points -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace AffineCoordinates

variable {k : Type u} [Field k] {G H Q D : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] [IsAffineHom H.X.hom] [IsAffineHom Q.X.hom]

local instance bicovariantTorusWeightInst1 : IsAffine G.X.left :=
  isAffine_of_isAffineHom G.X.hom
local instance bicovariantTorusWeightInst2 : IsAffine H.X.left :=
  isAffine_of_isAffineHom H.X.hom
local instance bicovariantTorusWeightInst3 : IsAffine Q.X.left :=
  isAffine_of_isAffineHom Q.X.hom

/-- **Bi-covariance obstruction.** Let `d` be left `i`-covariant of weight `χ` and satisfy
`d(g q(h')⁻¹) = ψ(h') d(g)` on all test schemes. If `i(h) m = m q(h')` and `d(m)` is a unit,
then `χ(h) = ψ(h'⁻¹)`. -/
theorem pointAlgebraHom_eq_of_mul_eq_mul (i : H ⟶ G) (q : Q ⟶ G) {χ : algebra H}
    {ψ : algebra Q} {d : algebra G} (hd : d ∈ leftCovariantSubspace i χ)
    (hd' : ∀ (T : Over (Spec (CommRingCat.of k))) (h : T ⟶ Q.X) (g : T ⟶ G.X),
      pointAlgebraHom G T (g * (h ≫ q.hom.hom)⁻¹) d =
        pointAlgebraHom Q T h ψ * pointAlgebraHom G T g d)
    {T : Over (Spec (CommRingCat.of k))} {h : T ⟶ H.X} {h' : T ⟶ Q.X} {m : T ⟶ G.X}
    (hm : (h ≫ i.hom.hom) * m = m * (h' ≫ q.hom.hom))
    (hu : IsUnit (pointAlgebraHom G T m d)) :
    pointAlgebraHom H T h χ = pointAlgebraHom Q T h'⁻¹ ψ := by
  have h1 := pointAlgebraHom_leftCovariant i χ hd T h m
  have h2 := hd' T h'⁻¹ m
  rw [GrpObj.inv_comp, inv_inv, ← hm, h1] at h2
  exact hu.mul_right_cancel h2

/-- A coordinate whose value at a rational point is a unit has unit values at the constant
points over every test scheme. -/
theorem isUnit_pointAlgebraHom_constantPoint {d : algebra G}
    {n : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X}
    (hu : IsUnit (pointAlgebraHom G (Over.mk (𝟙 (Spec (CommRingCat.of k)))) n d))
    (T : Over (Spec (CommRingCat.of k))) :
    IsUnit (pointAlgebraHom G T (constantPoint G n T) d) := by
  rw [constantPoint, pointAlgebraHom_naturality, AlgHom.comp_apply]
  exact hu.map _

/-- The rational point `n` intertwines `i ∘ jH` with `q ∘ jQ ∘ φ`: on every test scheme,
`i(jH(t)) n = n q(jQ(φ(t)))` for all points `t` of `D`. For a torus `D` embedded in both
subgroups and `n` normalizing it, `φ` is the induced automorphism of `D`. -/
def IsIntertwiningPoint (i : H ⟶ G) (q : Q ⟶ G) (jH : D ⟶ H) (jQ : D ⟶ Q) (φ : D ⟶ D)
    (n : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X) : Prop :=
  ∀ (T : Over (Spec (CommRingCat.of k))) (t : T ⟶ D.X),
    (t ≫ jH.hom.hom ≫ i.hom.hom) * constantPoint G n T =
      constantPoint G n T * (t ≫ φ.hom.hom ≫ jQ.hom.hom ≫ q.hom.hom)

/-- **Weights at a normalizing rational point.** Let `d` be as in
`pointAlgebraHom_eq_of_mul_eq_mul`, let `jH : D → H`, `jQ : D → Q` and `φ : D → D` be
homomorphisms, and let `n` be a rational point of `G` with
`i(jH(t)) n = n q(jQ(φ(t)))` for all test points `t` of `D` (`IsIntertwiningPoint`). If
`d(n)` is a unit, then `χ(jH(t)) = ψ(jQ(φ(t))⁻¹)` for all test points `t` of `D`. -/
theorem pointAlgebraHom_comp_eq_of_normalizes (i : H ⟶ G) (q : Q ⟶ G) {χ : algebra H}
    {ψ : algebra Q} {d : algebra G} (hd : d ∈ leftCovariantSubspace i χ)
    (hd' : ∀ (T : Over (Spec (CommRingCat.of k))) (h : T ⟶ Q.X) (g : T ⟶ G.X),
      pointAlgebraHom G T (g * (h ≫ q.hom.hom)⁻¹) d =
        pointAlgebraHom Q T h ψ * pointAlgebraHom G T g d)
    (jH : D ⟶ H) (jQ : D ⟶ Q) (φ : D ⟶ D) (n : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X)
    (hn : IsIntertwiningPoint i q jH jQ φ n)
    (hu : IsUnit (pointAlgebraHom G (Over.mk (𝟙 (Spec (CommRingCat.of k)))) n d))
    (T : Over (Spec (CommRingCat.of k))) (t : T ⟶ D.X) :
    pointAlgebraHom H T (t ≫ jH.hom.hom) χ =
      pointAlgebraHom Q T (t ≫ φ.hom.hom ≫ jQ.hom.hom)⁻¹ ψ := by
  refine pointAlgebraHom_eq_of_mul_eq_mul i q hd hd' ?_
    (isUnit_pointAlgebraHom_constantPoint hu T)
  simpa only [Category.assoc] using hn T t

end AffineCoordinates

end Langlands.GroupScheme
