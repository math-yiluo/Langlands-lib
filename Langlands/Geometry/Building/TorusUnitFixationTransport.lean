import Langlands.Geometry.Building.TorusUnitFixedPoint
import Langlands.Geometry.Building.ConjugateApartmentRealization

/-! # Transport of torus-unit fixation between actual action spaces -/

noncomputable section

universe u v w

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.GroupScheme.GaloisPointComparison

namespace Langlands.Geometry.Building

section ActionSpaces

variable {k K : Type u} [Field k] [Field K] [Algebra k K]
  {valuation : Valuation K (WithZero (Multiplicative ℤ))}
  {A G : GroupScheme (Spec (CommRingCat.of k))}
  {i : A ⟶ G}
  {Y : Type v} {Z : Type w}
  [MulAction (rationalPoints (baseChanged k K G)) Y]
  [MulAction (rationalPoints (baseChanged k K G)) Z]

/-- Any equivariant map preserves fixation by the original scalar-extended
torus-unit subgroup. -/
theorem IsFixedByScalarTorusUnits.map
    {y : Y} (hy : IsFixedByScalarTorusUnits k K valuation i y)
    (f : Y → Z)
    (hf : ∀ (g : rationalPoints (baseChanged k K G)) (y : Y),
      f (g • y) = g • f y) :
    IsFixedByScalarTorusUnits k K valuation i (f y) := by
  intro t ht
  rw [← hf, hy t ht]

/-- An injective equivariant map also reflects unit fixation. -/
theorem IsFixedByScalarTorusUnits.of_map
    (f : Y → Z) (hinj : Function.Injective f)
    (hf : ∀ (g : rationalPoints (baseChanged k K G)) (y : Y),
      f (g • y) = g • f y)
    {y : Y} (hy : IsFixedByScalarTorusUnits k K valuation i (f y)) :
    IsFixedByScalarTorusUnits k K valuation i y := by
  intro t ht
  apply hinj
  rw [hf, hy t ht]

/-- Unit fixation is unchanged through an injective equivariant realization. -/
theorem isFixedByScalarTorusUnits_map_iff
    (f : Y → Z) (hinj : Function.Injective f)
    (hf : ∀ (g : rationalPoints (baseChanged k K G)) (y : Y),
      f (g • y) = g • f y) (y : Y) :
    IsFixedByScalarTorusUnits k K valuation i (f y) ↔
      IsFixedByScalarTorusUnits k K valuation i y :=
  ⟨fun hy => hy.of_map f hinj hf, fun hy => hy.map f hf⟩

/-- Scalar-torus-unit fixation is preserved and reflected by every injective
equivariant map for the same scalar-extended group action. -/
def TorusUnitFixationTransportStatement : Prop :=
  ∀ (f : Y → Z), Function.Injective f →
    (∀ (g : rationalPoints (baseChanged k K G)) (y : Y),
      f (g • y) = g • f y) →
    ∀ y : Y, IsFixedByScalarTorusUnits k K valuation i (f y) ↔
      IsFixedByScalarTorusUnits k K valuation i y

/-- The transport statement follows directly from equivariance and
injectivity, retaining the original torus inclusion. -/
theorem torusUnitFixationTransport :
    TorusUnitFixationTransportStatement
      (valuation := valuation) (i := i) (Y := Y) (Z := Z) := by
  intro f hinj hf y
  exact isFixedByScalarTorusUnits_map_iff f hinj hf y

end ActionSpaces

namespace KPApartmentData

variable {k K : Type u} [Field k] [Field K] [Algebra k K]
  {A G : GroupScheme (Spec (CommRingCat.of k))}
  {S S' : CommGroupScheme (Spec (CommRingCat.of K))}
  {i : S.toGrp ⟶ baseChanged k K G}
  {j : S'.toGrp ⟶ baseChanged k K G}
  [Mono i.hom.hom.left] [Mono j.hom.hom.left]
  [IsAffineHom (baseChanged k K G).X.hom]
  {ω : Kˣ → ℝ}
  (D : KPApartmentData i ω)
  (e : S ≅ S') (g : rationalPoints (baseChanged k K G))
  (h : i ≫ ((baseChanged k K G).innerIso g).hom =
    CommGroupScheme.groupHom e.hom ≫ j)

/-- The actual same-action conjugate quotient realizes precisely the same
torus-unit fixed points in the original building. -/
theorem isFixedByScalarTorusUnits_conjugateReducedBuildingEquiv_iff
    (valuation : Valuation K (WithZero (Multiplicative ℤ)))
    (a : A ⟶ G)
    (q : (D.transport e ((baseChanged k K G).innerIso g) h).ReducedBuilding) :
    IsFixedByScalarTorusUnits k K valuation a
        (D.conjugateReducedBuildingEquiv e g h q) ↔
      IsFixedByScalarTorusUnits k K valuation a q :=
  isFixedByScalarTorusUnits_map_iff _
    (D.conjugateReducedBuildingEquiv e g h).injective
    (D.conjugateReducedBuildingEquiv_smul e g h) q

end KPApartmentData
end Langlands.Geometry.Building
