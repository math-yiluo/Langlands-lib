import Langlands.GroupScheme.Torus.FieldPointMaximality

/-! # Transport of fibrewise maximal tori -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

namespace Langlands.GroupScheme

/-- Maximality at a supplied field point reflects to the residue fibre at
its image, provided the original inclusion is closed. -/
theorem isMaximalTorus_residueFibre_of_fieldPoint
    {S : Scheme.{u}} {T : CommGroupScheme S} {G : GroupScheme S}
    {i : T.toGrp ⟶ G} (hi : IsClosedSubgroup i)
    {k : Type u} [Field k] (b : Spec (CommRingCat.of k) ⟶ S)
    (hmax : IsMaximalTorus (T := (CommGroupScheme.baseChange b).obj T)
      ((baseChange b).map i)) :
    IsMaximalTorus
      (T := (CommGroupScheme.baseChange
        (S.fromSpecResidueField (b (IsLocalRing.closedPoint k)))).obj T)
      ((baseChange (S.fromSpecResidueField (b (IsLocalRing.closedPoint k)))).map i) := by
  let : Algebra (S.residueField (b (IsLocalRing.closedPoint k))) k :=
    (fieldPointResidueMap b).hom.toAlgebra
  let a := S.fromSpecResidueField (b (IsLocalRing.closedPoint k))
  let c := Spec.map (fieldPointResidueMap b)
  have hc : c ≫ a = b := fieldPointResidueMap_factorization b
  have hm := isMaximalTorus_baseChange_comp a (k := k) c T i
    (by rw [hc]; exact hmax)
  exact IsMaximalTorus.of_baseChange
    (k := S.residueField (b (IsLocalRing.closedPoint k))) (K := k)
    (hi.baseChange a) hm

/-- Fibrewise maximality is preserved by arbitrary base change when the
ambient group is smooth and affine. -/
theorem IsFibrewiseMaximalTorus.baseChange
    {S U : Scheme.{u}} {T : CommGroupScheme S} {G : GroupScheme S}
    [Smooth G.X.hom] [IsAffineHom G.X.hom]
    {i : T.toGrp ⟶ G} (hi : IsFibrewiseMaximalTorus i) (a : U ⟶ S) :
    IsFibrewiseMaximalTorus (T := (CommGroupScheme.baseChange a).obj T)
      ((baseChange a).map i) := by
  intro s
  exact isMaximalTorus_baseChange_comp a (U.fromSpecResidueField s) T i
    (hi.fieldPoint (U.fromSpecResidueField s ≫ a))

/-- Composing the ambient group with an isomorphism preserves fibrewise
maximality. -/
theorem IsFibrewiseMaximalTorus.comp_iso
    {S : Scheme.{u}} {T : CommGroupScheme S} {G H : GroupScheme S}
    {i : T.toGrp ⟶ G} (hi : IsFibrewiseMaximalTorus i) (e : G ≅ H) :
    IsFibrewiseMaximalTorus (i ≫ e.hom) := by
  intro s
  simpa only [Functor.map_comp, Functor.mapIso_hom] using
    (hi s).comp_iso ((GroupScheme.baseChange (S.fromSpecResidueField s)).mapIso e)

end Langlands.GroupScheme
