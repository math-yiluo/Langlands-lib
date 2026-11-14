import Langlands.GroupScheme.Torus.FieldPointMaximality

/-! # Fibrewise maximality under base change and source isomorphisms -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme

variable {S S' : Scheme.{u}} {T T' : CommGroupScheme S} {G : GroupScheme S}
  {i : T.toGrp ⟶ G}

/-- Fibrewise maximality is preserved by arbitrary base change when the
ambient group is smooth and affine over the base. -/
theorem IsFibrewiseMaximalTorus.baseChange [Smooth G.X.hom] [IsAffineHom G.X.hom]
    (hi : IsFibrewiseMaximalTorus i) (b : S' ⟶ S) :
    IsFibrewiseMaximalTorus (T := (CommGroupScheme.baseChange b).obj T)
      ((GroupScheme.baseChange b).map i) := by
  intro s
  exact isMaximalTorus_baseChange_comp b (S'.fromSpecResidueField s) T i
    (hi.fieldPoint (S'.fromSpecResidueField s ≫ b))

/-- Replacing the source by an isomorphic commutative group scheme preserves
maximality on every actual residue-field fibre. -/
theorem IsFibrewiseMaximalTorus.iso_comp (hi : IsFibrewiseMaximalTorus i)
    (e : T'.toGrp ≅ T.toGrp) :
    IsFibrewiseMaximalTorus (T := T') (e.hom ≫ i) := by
  intro s
  rw [Functor.map_comp]
  exact IsMaximalTorus.iso_comp
    (T := (CommGroupScheme.baseChange (S.fromSpecResidueField s)).obj T)
    (T' := (CommGroupScheme.baseChange (S.fromSpecResidueField s)).obj T')
    ((GroupScheme.baseChange (S.fromSpecResidueField s)).mapIso e) (hi s)

/-- The source-isomorphism transport is an equivalence of the two
fibrewise-maximality predicates. -/
theorem IsFibrewiseMaximalTorus.iso_comp_iff (e : T'.toGrp ≅ T.toGrp)
    (i : T.toGrp ⟶ G) :
    IsFibrewiseMaximalTorus (T := T') (e.hom ≫ i) ↔ IsFibrewiseMaximalTorus i := by
  constructor
  · intro hi
    simpa only [Iso.symm_hom, Iso.inv_hom_id_assoc] using
      hi.iso_comp (T := T') (T' := T) e.symm
  · exact fun hi => hi.iso_comp (T := T) (T' := T') e

namespace splitTorus

/-- Fibrewise maximality of a coordinate split-torus map is preserved by
arbitrary base change, using the canonical coordinate source on the new base. -/
theorem isFibrewiseMaximalTorus_baseChangedHom
    (I : Type u) [Finite I] (G : GroupScheme S)
    [Smooth G.X.hom] [IsAffineHom G.X.hom]
    (i : splitTorus S I ⟶ G)
    (hi : IsFibrewiseMaximalTorus (T := commGroupScheme S I) i) (b : S' ⟶ S) :
    IsFibrewiseMaximalTorus (T := commGroupScheme S' I)
      ((baseChangeIso b I).inv ≫ (GroupScheme.baseChange b).map i) :=
  (hi.baseChange (T := commGroupScheme S I) b).iso_comp
    (T := (CommGroupScheme.baseChange b).obj (commGroupScheme S I))
    (T' := commGroupScheme S' I) (baseChangeIso b I).symm

end splitTorus

/-- Fibrewise maximality is preserved by arbitrary base change for a smooth
affine ambient group, and is invariant under an isomorphism of its source. -/
def FibrewiseMaximalTransportStatement : Prop :=
  (∀ (S S' : Scheme.{u}) (T : CommGroupScheme S) (G : GroupScheme S)
    [Smooth G.X.hom] [IsAffineHom G.X.hom]
    (i : T.toGrp ⟶ G) (b : S' ⟶ S),
    IsFibrewiseMaximalTorus i →
      IsFibrewiseMaximalTorus (T := (CommGroupScheme.baseChange b).obj T)
        ((GroupScheme.baseChange b).map i)) ∧
  (∀ (S : Scheme.{u}) (T T' : CommGroupScheme S) (G : GroupScheme S)
    (e : T'.toGrp ≅ T.toGrp) (i : T.toGrp ⟶ G),
    IsFibrewiseMaximalTorus (T := T') (e.hom ≫ i) ↔ IsFibrewiseMaximalTorus i)

/-- The general transport statement follows from the two transport methods. -/
theorem fibrewiseMaximalTransport : FibrewiseMaximalTransportStatement.{u} := by
  constructor
  · intro S S' T G _ _ i b hi
    exact hi.baseChange b
  · intro S T T' G e i
    exact IsFibrewiseMaximalTorus.iso_comp_iff e i

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
