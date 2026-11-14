import Langlands.GroupScheme.RelativeLevi.BorelTransport
import Langlands.GroupScheme.Torus.RelativeDescent
import Langlands.GroupScheme.Torus.MaximalAmbient
import Langlands.CategoryTheory.GroupObjectDescent
import Langlands.GroupScheme.SubgroupFunctor.FpqcDescent

/-! # Effective descent of relative Borels and maximal tori -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme

open Descent

variable {S U : Scheme.{u}} {p : U ⟶ S} {G : GroupScheme S}

/-- An actual relative Borel downstairs, recovering a specified inclusion upstairs. -/
structure RelativeBorelDescentData {B : GroupScheme U}
    (i : B ⟶ (GroupScheme.baseChange p).obj G) where
  obj : GroupScheme S
  inclusion : obj ⟶ G
  affine : IsAffine obj.X.left
  isClosed : IsClosedSubgroup inclusion
  isBorel : IsRelativeBorelSubgroup inclusion
  recoveryIso : (GroupScheme.baseChange p).obj obj ≅ B
  recovery : (GroupScheme.baseChange p).map inclusion = recoveryIso.hom ≫ i

/-- An actual relative maximal torus downstairs with exact pullback recovery. -/
structure RelativeTorusDescentData {T : CommGroupScheme U}
    (t : T.toGrp ⟶ (GroupScheme.baseChange p).obj G) where
  obj : CommGroupScheme S
  inclusion : obj.toGrp ⟶ G
  affine : IsAffine obj.X.left
  isTorus : RelativeTorus.IsTorus obj.toGrp
  isClosed : IsClosedSubgroup inclusion
  maximal : IsFibrewiseMaximalTorus inclusion
  recoveryIso : (GroupScheme.baseChange p).obj obj.toGrp ≅ T.toGrp
  recovery : (GroupScheme.baseChange p).map inclusion = recoveryIso.hom ≫ t

section Borel

variable [IsAffine S] [IsAffine U] [Flat p] [Surjective p]
  [IsAffine G.X.left] {B : GroupScheme U}
  {i : B ⟶ (GroupScheme.baseChange p).obj G}

/-- All-test overlap invariance effectively descends a supplied closed relative Borel. -/
theorem IsRelativeBorelSubgroup.nonempty_descentData_of_overlap_range_eq
    (hi : IsRelativeBorelSubgroup i) (hclosed : IsClosedSubgroup i)
    (h : SubgroupFunctor.range
        ((GroupScheme.baseChange (fst p)).map i ≫ (canonicalOverlap p G).hom) =
      SubgroupFunctor.range ((GroupScheme.baseChange (snd p)).map i)) :
    Nonempty (RelativeBorelDescentData i) := by
  obtain ⟨B₀, j, e, hB₀, hj, he⟩ :=
    hclosed.exists_descent_of_overlap_range_eq p h
  let : IsAffine B₀.X.left := hB₀
  let : IsAffineHom G.X.hom := inferInstance
  have hgeo : IsRelativeBorelSubgroup ((GroupScheme.baseChange p).map j) := by
    rw [he]
    exact hi.iso_comp e
  exact ⟨⟨B₀, j, hB₀, hj,
    IsRelativeBorelSubgroup.of_baseChange p hj hgeo, e, he⟩⟩

/-- Select an effective relative Borel descent from overlap invariance alone. -/
def IsRelativeBorelSubgroup.descentOfOverlap
    (hi : IsRelativeBorelSubgroup i) (hclosed : IsClosedSubgroup i)
    (h : SubgroupFunctor.range
        ((GroupScheme.baseChange (fst p)).map i ≫ (canonicalOverlap p G).hom) =
      SubgroupFunctor.range ((GroupScheme.baseChange (snd p)).map i)) :
    RelativeBorelDescentData i :=
  Classical.choice (hi.nonempty_descentData_of_overlap_range_eq hclosed h)

end Borel

section Torus

variable [IsAffine S] [IsAffine U] [Etale p] [Surjective p]
  [IsAffine G.X.left] {T : CommGroupScheme U}
  {t : T.toGrp ⟶ (GroupScheme.baseChange p).obj G}

/-- All-test overlap invariance effectively descends a supplied closed relative
maximal torus, including its commutative group structure. -/
theorem RelativeTorus.IsTorus.nonempty_descentData_of_overlap_range_eq
    (hT : RelativeTorus.IsTorus T.toGrp) (ht : IsClosedSubgroup t)
    (hmax : IsFibrewiseMaximalTorus t)
    (h : SubgroupFunctor.range
        ((GroupScheme.baseChange (fst p)).map t ≫ (canonicalOverlap p G).hom) =
      SubgroupFunctor.range ((GroupScheme.baseChange (snd p)).map t)) :
    Nonempty (RelativeTorusDescentData t) := by
  obtain ⟨T₀, j, e, hT₀, hj, he⟩ := ht.exists_descent_of_overlap_range_eq p h
  let : IsAffine T₀.X.left := hT₀
  have hcomm : IsCommMonObj ((GroupScheme.baseChange p).obj T₀).X :=
    Langlands.CategoryTheory.GroupObjectDescent.commMonObjOfMono e.hom.hom.hom
  let T' : CommGroupScheme S :=
    { toGrp := T₀
      comm := isCommMonObj_of_baseChange p T₀ hcomm }
  have htorus : RelativeTorus.IsTorus T'.toGrp :=
    RelativeTorus.IsTorus.of_baseChange_of_etale p (RelativeTorus.IsTorus.of_iso e hT)
  have hmax' : IsFibrewiseMaximalTorus
      (T := (CommGroupScheme.baseChange p).obj T') ((GroupScheme.baseChange p).map j) := by
    rw [he]
    exact IsFibrewiseMaximalTorus.iso_comp
      (T' := (CommGroupScheme.baseChange p).obj T') hmax e
  exact ⟨⟨T', j, hT₀, htorus, hj,
    IsFibrewiseMaximalTorus.of_baseChange p hj hmax', e, he⟩⟩

/-- Select an effective relative maximal-torus descent from overlap invariance. -/
def RelativeTorus.IsTorus.descentOfOverlap
    (hT : RelativeTorus.IsTorus T.toGrp) (ht : IsClosedSubgroup t)
    (hmax : IsFibrewiseMaximalTorus t)
    (h : SubgroupFunctor.range
        ((GroupScheme.baseChange (fst p)).map t ≫ (canonicalOverlap p G).hom) =
      SubgroupFunctor.range ((GroupScheme.baseChange (snd p)).map t)) :
    RelativeTorusDescentData t :=
  Classical.choice (hT.nonempty_descentData_of_overlap_range_eq ht hmax h)

end Torus

section Containment

variable [Flat p] [Surjective p] [QuasiCompact p]
  {B : GroupScheme U} {i : B ⟶ (GroupScheme.baseChange p).obj G}
  {T : CommGroupScheme U} {t : T.toGrp ⟶ (GroupScheme.baseChange p).obj G}

/-- Containment of the original torus in the original Borel descends with the
actual inclusions, independently of the selected descent presentations. -/
theorem RelativeTorusDescentData.range_le (dT : RelativeTorusDescentData t)
    (dB : RelativeBorelDescentData i)
    (h : SubgroupFunctor.range t ≤ SubgroupFunctor.range i) :
    SubgroupFunctor.range dT.inclusion ≤ SubgroupFunctor.range dB.inclusion := by
  let : IsClosedImmersion dB.inclusion.hom.hom.left := dB.isClosed
  let : Mono dB.inclusion.hom.hom := Over.mono_of_mono_left _
  apply SubgroupFunctor.le_range_of_baseChange_le p dB.inclusion
  rw [← SubgroupFunctor.range_baseChangeHom, ← SubgroupFunctor.range_baseChangeHom,
    dT.recovery, dB.recovery,
    SubgroupFunctor.range_iso_comp, SubgroupFunctor.range_iso_comp]
  exact h

omit [Flat p] [Surjective p] [QuasiCompact p] in
/-- The descended Borel witnesses relative quasi-splitness of a reductive ambient group. -/
theorem RelativeBorelDescentData.quasiSplit (dB : RelativeBorelDescentData i)
    (hG : IsReductive G) : IsRelativeQuasiSplit G :=
  ⟨hG, dB.obj, dB.inclusion, dB.isBorel⟩

end Containment

end Langlands.GroupScheme
