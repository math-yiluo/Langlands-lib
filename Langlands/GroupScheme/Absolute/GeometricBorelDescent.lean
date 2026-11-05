import Langlands.GroupScheme.Reductive.QuasiSplit
import Langlands.GroupScheme.Descent.ClosedSubgroups
import Langlands.GroupScheme.Rational.UnipotentRadicalProperties
import Langlands.GroupScheme.Absolute.ParabolicBorelFactorization
import Langlands.GroupScheme.Absolute.SolvableFieldExtensionProof

/-! # Descent of an actual geometric Borel subgroup -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]
variable {B G : GroupScheme (Spec (CommRingCat.of k))}
variable [IsAffineHom G.X.hom] {i : B ⟶ G}

/-- A closed inclusion whose algebraic-closure pullback is Borel is already
Borel over the original field. -/
theorem IsBorelSubgroup.of_baseChange_toAlgebraicClosure
    (hi : IsBorelSubgroup ((GroupScheme.baseChange (toAlgebraicClosure k)).map i))
    (hclosed : IsClosedSubgroup i) : IsBorelSubgroup i := by
  let b := toAlgebraicClosure k
  let F := GroupScheme.baseChange b
  let : Surjective b := (fieldExtension_fpqc k (AlgebraicClosure k)).1
  let : Flat b := (fieldExtension_fpqc k (AlgebraicClosure k)).2.1
  let : QuasiCompact b := (fieldExtension_fpqc k (AlgebraicClosure k)).2.2
  have hsol : IsSolvableGroupScheme B :=
    (isSolvableGroupScheme_iff_rationalPoints (F.obj B)).mp hi.isSolvableGroupScheme
  refine ⟨hclosed, smooth_of_baseChange b B hi.smooth,
    connectedSpace_of_baseChange b B hi.connectedSpace, hsol, ?_⟩
  intro C j f hj hsm hconn hsolC hf
  let : IsClosedImmersion j.hom.hom.left := hj
  let : IsAffineHom C.X.hom := by
    rw [← Over.w j.hom.hom]
    infer_instance
  let : Smooth C.X.hom := hsm
  let : ConnectedSpace C.X.left := hconn
  have : IsIso (F.map f) := hi.maximal (F.obj C) (F.map j) (F.map f)
    (hj.baseChange b) (show Smooth (pullback.snd C.X.hom b) from inferInstance)
    (C.connectedSpace_baseChange_of_smooth_affine b)
    (solvableFieldExtensionStatement k (AlgebraicClosure k) b C hsm hsolC)
    (by rw [← F.map_comp, hf])
  exact isIso_of_baseChange b f

/-- The geometric Borel predicate follows from a closed inclusion and its
algebraic-closure Borel property. -/
theorem isGeometricBorelSubgroup_of_baseChange_toAlgebraicClosure
    (hi : IsBorelSubgroup ((GroupScheme.baseChange (toAlgebraicClosure k)).map i))
    (hclosed : IsClosedSubgroup i) : IsGeometricBorelSubgroup i :=
  ⟨hi.of_baseChange_toAlgebraicClosure hclosed, hi⟩

/-- A ground-field geometric Borel together with the actual isomorphism recovering
its prescribed algebraic-closure inclusion. -/
structure GeometricBorelDescentData
    {H : GroupScheme (Spec (CommRingCat.of (AlgebraicClosure k)))}
    (i : H ⟶ (GroupScheme.baseChange (toAlgebraicClosure k)).obj G) where
  obj : GroupScheme (Spec (CommRingCat.of k))
  inclusion : obj ⟶ G
  affine : IsAffine obj.X.left
  geometricBorel : IsGeometricBorelSubgroup inclusion
  recoveryIso : (GroupScheme.baseChange (toAlgebraicClosure k)).obj obj ≅ H
  recovery : (GroupScheme.baseChange (toAlgebraicClosure k)).map inclusion =
    recoveryIso.hom ≫ i

variable {H : GroupScheme (Spec (CommRingCat.of (AlgebraicClosure k)))}
variable {i : H ⟶ (GroupScheme.baseChange (toAlgebraicClosure k)).obj G}

/-- All-test overlap invariance descends an actual algebraic-closure Borel,
including its geometric Borel property and its recovery isomorphism. -/
theorem IsBorelSubgroup.nonempty_descentData_of_overlap_range_eq
    (hi : IsBorelSubgroup i)
    (h : SubgroupFunctor.range
        ((GroupScheme.baseChange (Descent.fst (toAlgebraicClosure k))).map i ≫
          (Descent.canonicalOverlap (toAlgebraicClosure k) G).hom) =
      SubgroupFunctor.range
        ((GroupScheme.baseChange (Descent.snd (toAlgebraicClosure k))).map i)) :
    Nonempty (GeometricBorelDescentData i) := by
  let b := toAlgebraicClosure k
  let F := GroupScheme.baseChange b
  let : Surjective b := (fieldExtension_fpqc k (AlgebraicClosure k)).1
  let : Flat b := (fieldExtension_fpqc k (AlgebraicClosure k)).2.1
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  obtain ⟨B, j, e, hB, hj, he⟩ :=
    hi.isClosedSubgroup.exists_descent_of_overlap_range_eq b h
  have hb : IsBorelSubgroup (F.map j) := by
    rw [he]
    exact hi.iso_comp e
  exact ⟨⟨B, j, hB,
    isGeometricBorelSubgroup_of_baseChange_toAlgebraicClosure hb hj, e, he⟩⟩

/-- A selected actual ground-field descent of an overlap-invariant Borel. -/
def IsBorelSubgroup.descentOfOverlap
    (hi : IsBorelSubgroup i)
    (h : SubgroupFunctor.range
        ((GroupScheme.baseChange (Descent.fst (toAlgebraicClosure k))).map i ≫
          (Descent.canonicalOverlap (toAlgebraicClosure k) G).hom) =
      SubgroupFunctor.range
        ((GroupScheme.baseChange (Descent.snd (toAlgebraicClosure k))).map i)) :
    GeometricBorelDescentData i :=
  Classical.choice (hi.nonempty_descentData_of_overlap_range_eq h)

/-- A reductive group with an overlap-invariant algebraic-closure Borel is
quasi-split over the original field. -/
theorem isQuasiSplit_of_borel_overlap_range_eq
    (hG : IsConnectedReductive G) (hi : IsBorelSubgroup i)
    (h : SubgroupFunctor.range
        ((GroupScheme.baseChange (Descent.fst (toAlgebraicClosure k))).map i ≫
          (Descent.canonicalOverlap (toAlgebraicClosure k) G).hom) =
      SubgroupFunctor.range
        ((GroupScheme.baseChange (Descent.snd (toAlgebraicClosure k))).map i)) :
    IsQuasiSplit G := by
  let D := hi.descentOfOverlap h
  exact ⟨hG, D.obj, D.inclusion, D.geometricBorel⟩

end Langlands.GroupScheme
