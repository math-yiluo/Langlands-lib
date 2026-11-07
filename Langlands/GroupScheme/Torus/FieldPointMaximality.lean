import Langlands.GroupScheme.Reductive.GenericFiberGeometry
import Langlands.GroupScheme.Torus.LocalMaximalPropagation
import Langlands.GroupScheme.Torus.RelativeAdjointWeightBaseChange

/-! # Maximal tori on residue fibres and supplied field-valued fibres -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false

namespace Langlands.GroupScheme

/-- A torus map is fibrewise maximal when its actual pullback to every
residue-field fibre is a maximal torus. -/
def IsFibrewiseMaximalTorus {S : Scheme.{u}} {T : CommGroupScheme S}
    {G : GroupScheme S} (i : T.toGrp ⟶ G) : Prop :=
  ∀ s : S, IsMaximalTorus
    (T := (CommGroupScheme.baseChange (S.fromSpecResidueField s)).obj T)
    ((baseChange (S.fromSpecResidueField s)).map i)

section FieldPoint

variable {S : Scheme.{u}} {T : CommGroupScheme S} {G : GroupScheme S}
  [Smooth G.X.hom] [IsAffineHom G.X.hom] {i : T.toGrp ⟶ G}
  {k : Type u} [Field k] (b : Spec (CommRingCat.of k) ⟶ S)

/-- Maximality on the residue fibre at the image of a supplied field point
implies maximality on that actual field-valued fibre. -/
theorem isMaximalTorus_fieldPoint_of_residueFibre
    (hmax : IsMaximalTorus
      (T := (CommGroupScheme.baseChange
        (S.fromSpecResidueField (b (IsLocalRing.closedPoint k)))).obj T)
      ((baseChange
        (S.fromSpecResidueField (b (IsLocalRing.closedPoint k)))).map i)) :
    IsMaximalTorus (T := (CommGroupScheme.baseChange b).obj T)
      ((baseChange b).map i) := by
  let : Algebra (S.residueField (b (IsLocalRing.closedPoint k))) k :=
    (fieldPointResidueMap b).hom.toAlgebra
  let a := S.fromSpecResidueField (b (IsLocalRing.closedPoint k))
  let c := Spec.map (fieldPointResidueMap b)
  have : Smooth ((baseChange a).obj G).X.hom :=
    inferInstanceAs (Smooth (Limits.pullback.snd G.X.hom a))
  have : IsAffineHom ((baseChange a).obj G).X.hom :=
    inferInstanceAs (IsAffineHom (Limits.pullback.snd G.X.hom a))
  have h := (maximalTorusBaseChange (S.residueField (b (IsLocalRing.closedPoint k))) k
    ((baseChange a).obj G) ((CommGroupScheme.baseChange a).obj T)
    ((baseChange a).map i) hmax.1 hmax.2.1).mp hmax
  have hc := isMaximalTorus_of_baseChange_comp a c T i h
  dsimp only [a, c] at hc
  rwa [fieldPointResidueMap_factorization] at hc

/-- Fibrewise maximality applies to every supplied field-valued point,
with its original coefficient map. -/
theorem IsFibrewiseMaximalTorus.fieldPoint (hi : IsFibrewiseMaximalTorus i) :
    IsMaximalTorus (T := (CommGroupScheme.baseChange b).obj T)
      ((baseChange b).map i) :=
  isMaximalTorus_fieldPoint_of_residueFibre b (hi _)

end FieldPoint

/-- For a smooth affine ambient group, residue-fibre maximality is equivalent
to maximality on every supplied field-valued fibre. -/
theorem isFibrewiseMaximalTorus_iff_forall_fieldPoint
    {S : Scheme.{u}} {T : CommGroupScheme S} {G : GroupScheme S}
    [Smooth G.X.hom] [IsAffineHom G.X.hom] (i : T.toGrp ⟶ G) :
    IsFibrewiseMaximalTorus i ↔
      ∀ (k : Type u) [Field k] (b : Spec (CommRingCat.of k) ⟶ S),
        IsMaximalTorus (T := (CommGroupScheme.baseChange b).obj T)
          ((baseChange b).map i) := by
  constructor
  · intro hi k _ b
    exact hi.fieldPoint b
  · intro hi s
    exact hi (S.residueField s) (S.fromSpecResidueField s)

/-- A closed split torus in a reductive group over a local ring is maximal on
every supplied field-valued fibre once it is maximal on the closed fibre. -/
theorem IsReductive.isMaximalTorus_fieldPoint_of_closedFibre
    {R : Type u} [CommRing R] [IsLocalRing R]
    {G : GroupScheme (Spec (CommRingCat.of R))} (hG : IsReductive G)
    {T : CommGroupScheme (Spec (CommRingCat.of R))} (hT : IsSplitTorus T.toGrp)
    (i : T.toGrp ⟶ G) (hi : IsClosedSubgroup i)
    (hmax : IsMaximalTorus
      (T := (CommGroupScheme.baseChange
        ((Spec (CommRingCat.of R)).fromSpecResidueField (IsLocalRing.closedPoint R))).obj T)
      ((baseChange
        ((Spec (CommRingCat.of R)).fromSpecResidueField (IsLocalRing.closedPoint R))).map i))
    {k : Type u} [Field k] (b : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R)) :
    IsMaximalTorus (T := (CommGroupScheme.baseChange b).obj T)
      ((baseChange b).map i) := by
  let := hG.smooth
  let := hG.isAffineHom
  exact isMaximalTorus_fieldPoint_of_residueFibre b
    (hG.isMaximalTorus_residueFibre_of_closedFibre hT i hi hmax _)

namespace splitTorus

variable {R : Type u} [CommRing R] (I : Type u) [Fintype I] [DecidableEq I]
  (G : GroupScheme (Spec (CommRingCat.of R)))
  [Smooth G.X.hom] [IsAffineHom G.X.hom]
  (i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G)

omit [DecidableEq I] in
/-- Residue-fibre maximality implies maximality of the canonical coordinate
torus map on every supplied field algebra. -/
theorem isMaximalTorus_baseChangeHom_of_fibrewise
    (hi : IsFibrewiseMaximalTorus (T := commGroupScheme _ I) i)
    (k : Type u) [Field k] [Algebra R k] :
    IsMaximalTorus (T := commGroupScheme (Spec (CommRingCat.of k)) I)
      (baseChangeHom (K := k) G I i) := by
  exact IsMaximalTorus.iso_comp
    (T := (CommGroupScheme.baseChange (algebraBaseMap R k)).obj (commGroupScheme _ I))
    (T' := commGroupScheme (Spec (CommRingCat.of k)) I)
    (baseChangeIso (algebraBaseMap R k) I).symm (hi.fieldPoint (algebraBaseMap R k))

omit [Smooth G.X.hom] [IsAffineHom G.X.hom] in
/-- A closed split torus in a reductive group over a local ring is maximal on
every supplied field-valued fibre once it is maximal on the closed fibre. -/
theorem isMaximalTorus_baseChangeHom_of_closedFibre [IsLocalRing R]
    (hG : IsReductive G) (hi : IsClosedSubgroup i)
    (hmax : IsMaximalTorus
      (T := (CommGroupScheme.baseChange
        ((Spec (CommRingCat.of R)).fromSpecResidueField (IsLocalRing.closedPoint R))).obj
          (commGroupScheme _ I))
      ((baseChange
        ((Spec (CommRingCat.of R)).fromSpecResidueField (IsLocalRing.closedPoint R))).map i))
    (k : Type u) [Field k] [Algebra R k] :
    IsMaximalTorus (T := commGroupScheme (Spec (CommRingCat.of k)) I)
      (baseChangeHom (K := k) G I i) := by
  let := hG.smooth
  let := hG.isAffineHom
  exact isMaximalTorus_baseChangeHom_of_fibrewise I G i
    (isMaximalTorus_residueFibre_of_closedFibre I G i hG hi hmax) k

end splitTorus

end Langlands.GroupScheme
