import Langlands.GroupScheme.Rational.VectorDiagonalAction
import Langlands.GroupScheme.Rational.VectorCoordinateProduct
import Langlands.GroupScheme.Rational.CoordinateSemigroupStatement
import Langlands.GroupScheme.Rational.ActionWeightTransport
import Langlands.GroupScheme.Rational.SemigroupClosure
import Langlands.GroupScheme.Dynamic.CentralizerReductiveTransport

/-! # Actual coordinate eigenfunctions of homogeneous vector actions -/

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

noncomputable section
universe u
open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.RelativeRoot

variable {k : Type u} [Field k]
    {V : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom V.X.hom]
    {S : CommGroupScheme (Spec (CommRingCat.of k))}
    {b : AutomorphicAction S.toGrp V} {d : ℕ}
    (e : ∀ T : Over (Spec (CommRingCat.of k)),
      (T ⟶ V.X) ≃* Multiplicative (Fin d → Γ(T.left, ⊤)))

/-- The actual affine function given by one natural vector coordinate. -/
def vectorCoordinateFunction (i : Fin d) : CharacterUnits.Coord V :=
  (vectorAffineCoordinates e (CharacterUnits.Coord V)
    (CharacterUnits.universalPoint V)).toAdd i

/-- Evaluation of this function recovers the supplied coordinate. -/
theorem pointCoordinates_vectorCoordinateFunction (he : IsNaturalVectorCoordinates e)
    {A : Type u} [CommRing A] [Algebra k A]
    (x : Lie.AffinePoints V A) (i : Fin d) :
    Lie.pointCoordinates V x (vectorCoordinateFunction e i) =
      (vectorAffineCoordinates e A x).toAdd i := by
  have hx : Lie.affineMap V (Lie.pointCoordinates V x)
      (CharacterUnits.universalPoint V) = x := by
    apply (Lie.pointCoordinates V).injective
    rw [Lie.pointCoordinates_naturality]
    change (Lie.pointCoordinates V x).comp
      ((Lie.pointCoordinates V) ((Lie.pointCoordinates V).symm
        (AlgHom.id k (CharacterUnits.Coord V)))) = _
    rw [Equiv.apply_symm_apply, AlgHom.comp_id]
  have h := congrFun (he.vectorAffineCoordinates_naturality
    (Lie.pointCoordinates V x) (CharacterUnits.universalPoint V)) i
  rw [hx] at h
  exact h.symm

/-- Each vector coordinate vanishes at the actual identity. -/
theorem vectorCoordinateFunction_mem_augmentation (he : IsNaturalVectorCoordinates e)
    (i : Fin d) : vectorCoordinateFunction e i ∈ CoordinateWeights.augmentation V := by
  change Lie.pointCoordinates V (1 : Lie.AffinePoints V k)
    (vectorCoordinateFunction e i) = 0
  rw [pointCoordinates_vectorCoordinateFunction e he, map_one]
  rfl

namespace HomogeneousVectorCoordinates

variable (q : HomogeneousVectorCoordinates b)

omit [IsAffineHom V.X.hom] in
/-- The original action is diagonal in the coefficient-algebra coordinates. -/
theorem affine_action {A : Type u} [CommRing A] [Algebra k A]
    (s : Lie.AffinePoints S.toGrp A) (x : Lie.AffinePoints V A)
    (i : Fin q.dimension) :
    (vectorAffineCoordinates q.coordinates A (b.act s x)).toAdd i =
      (Lie.characterValue (q.weight i) s : A) *
        (vectorAffineCoordinates q.coordinates A x).toAdd i := by
  change (Scheme.ΓSpecIso (CommRingCat.of A)).hom
    ((q.coordinates _ (b.act s x)).toAdd i) = _
  rw [q.action, map_mul]
  rfl

/-- The coordinate function has its original actual character as eigenweight. -/
theorem coordinateFunction_mem_weightSpace (i : Fin q.dimension) :
    vectorCoordinateFunction q.coordinates i ∈ CoordinateWeights.weightSpace b (q.weight i) := by
  intro A _ _ s x
  rw [pointCoordinates_vectorCoordinateFunction q.coordinates q.naturality,
    pointCoordinates_vectorCoordinateFunction q.coordinates q.naturality]
  exact q.affine_action s x i

omit [IsAffineHom V.X.hom] in
/-- Coordinate blocks are invariant under the original action on every test. -/
theorem isStable_coordinateSubgroup (I : Set (Fin q.dimension)) :
    b.IsStable (vectorCoordinateSubgroup q.coordinates q.naturality I) := by
  intro T s x hx i hi
  rw [q.action, hx i hi, mul_zero]

/-- A function that vanishes on the universal point of a represented subgroup
vanishes in that vector coordinate on every test scheme. -/
theorem coordinate_eq_zero_of_pullback_eq_zero
    {H : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom H.X.hom]
    (j : H ⟶ V) (i : Fin q.dimension)
    (hz : CoordinateWeights.pullback j.hom.hom
      (vectorCoordinateFunction q.coordinates i) = 0)
    (T : Over (Spec (CommRingCat.of k))) (x : T ⟶ H.X) :
    (q.coordinates T (x ≫ j.hom.hom)).toAdd i = 0 := by
  have hEval := pointCoordinates_vectorCoordinateFunction q.coordinates q.naturality
    (CharacterUnits.universalPoint H ≫ j.hom.hom) i
  have hAffine : (vectorAffineCoordinates q.coordinates (CharacterUnits.Coord H)
      (CharacterUnits.universalPoint H ≫ j.hom.hom)).toAdd i = 0 :=
    hEval.symm.trans hz
  have hu : (q.coordinates _
      (CharacterUnits.universalPoint H ≫ j.hom.hom)).toAdd i = 0 := by
    apply (Scheme.ΓSpecIso (CommRingCat.of (CharacterUnits.Coord H))).commRingCatIsoToRingEquiv.injective
    exact hAffine.trans (map_zero _).symm
  have hn := congrFun (q.naturality _ T (x ≫ (Lie.coordinateIso H).inv)
    (CharacterUnits.universalPoint H ≫ j.hom.hom)) i
  rw [CharacterUnits.universalPoint_eq, ← Category.assoc,
    Category.assoc x, (Lie.coordinateIso H).inv_hom_id, Category.comp_id] at hn
  rw [CharacterUnits.universalPoint_eq] at hu
  exact hn.trans ((congrArg (x ≫ (Lie.coordinateIso H).inv).left.appTop hu).trans
    (map_zero _))

/-- A smooth connected stable generator has zero coordinates at labels outside
its semigroup, assuming the exact coordinate/Lie support-containment theorem. -/
theorem generator_le_coordinateSubgroup
    (hContain : CoordinateWeights.AugmentationLieContainmentStatement.{u})
    (hS : IsSplitTorus S.toGrp) (A : AddSubsemigroup (characterLattice S))
    {F : SubgroupFunctor V} (hF : IsSemigroupGenerator b A F) :
    F ≤ vectorCoordinateSubgroup q.coordinates q.naturality {i | q.weight i ∈ A} := by
  obtain ⟨H, j, hj, hjc, hsm, hconn⟩ := hF.1
  let : IsAffineHom H.X.hom := hjc.isAffineHom
  let c := b.onRepresentedSubgroup j hj hF.2.1
  have heq : CoordinateWeights.IsEquivariant c b j.hom.hom :=
    CoordinateWeights.represented_inclusion_equivariant b j hj hF.2.1
  have htop : (⊤ : SubgroupFunctor H).map j = F := by
    ext T x
    rw [← hj.2]
    constructor
    · rintro ⟨y, _, rfl⟩
      exact ⟨y, rfl⟩
    · rintro ⟨y, rfl⟩
      exact ⟨y, Subgroup.mem_top _, rfl⟩
  have hLie : actionWeightSupport c ⊤ ⊆ A := by
    rw [← actionWeightSupport_map j hj.1 c b heq, htop]
    exact hF.2.2
  have hSupport : CoordinateWeights.support c ⊆ A :=
    (hContain k H hsm inferInstance hconn S hS c A).mpr hLie
  intro T x hx i hi
  have hχ : q.weight i ∉ A := hi
  let z : CoordinateWeights.augmentation H :=
    CoordinateWeights.augmentationPullback j
      ⟨vectorCoordinateFunction q.coordinates i,
        vectorCoordinateFunction_mem_augmentation q.coordinates q.naturality i⟩
  have hzWeight : z ∈ CoordinateWeights.augmentationWeightSpace c (q.weight i) :=
    CoordinateWeights.augmentationPullback_mem c b j heq (q.weight i)
      (q.coordinateFunction_mem_weightSpace i)
  have hz : z = 0 := by
    by_contra hz
    exact hχ (hSupport ⟨z, hz, hzWeight⟩)
  have hz' : CoordinateWeights.pullback j.hom.hom
      (vectorCoordinateFunction q.coordinates i) = 0 :=
    congrArg (fun w : CoordinateWeights.augmentation H => w.val) hz
  rw [← hj.2] at hx
  obtain ⟨y, rfl⟩ := hx
  exact q.coordinate_eq_zero_of_pullback_eq_zero j i hz' T y

/-- The actual generated semigroup subgroup is contained in its coordinate
block under exact coordinate/Lie support containment. -/
theorem semigroupSubgroup_le_coordinateSubgroup
    (hContain : CoordinateWeights.AugmentationLieContainmentStatement.{u})
    (hS : IsSplitTorus S.toGrp) (A : AddSubsemigroup (characterLattice S)) :
    semigroupSubgroup b A ≤
      vectorCoordinateSubgroup q.coordinates q.naturality {i | q.weight i ∈ A} :=
  (semigroupSubgroup_le_iff b A _).mpr fun _ hF =>
    q.generator_le_coordinateSubgroup hContain hS A hF

end HomogeneousVectorCoordinates
end Langlands.GroupScheme.RelativeRoot
