import Langlands.GroupScheme.Rational.CenterPointQuotientBridge
import Langlands.GroupScheme.Rational.FppfQuotientSmooth

/-! # A supplied algebraic model of the literal full-center point quotient -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Topology
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

open Langlands.AlgebraicGeometry.PointTopology
open RelativeRoot

section Kernel

variable {R : Type u} [CommRing R]
  {A Z C : GroupScheme (Spec (CommRingCat.of R))}

/-- Scheme-theoretic exactness identifies the actual point kernel with the
actual point image, without any point-surjectivity premise on the quotient. -/
theorem rationalPoints_ker_eq_range_of_fppfQuotient (j : A ⟶ Z) (q : Z ⟶ C)
    (hq : IsFppfQuotient (SubgroupFunctor.range j) q) :
    (rationalPoints.map q).ker = (rationalPoints.map j).range := by
  ext x
  change x ≫ q.hom.hom = 1 ↔
    ∃ a : rationalPoints A, a ≫ j.hom.hom = x
  rw [← mem_range_kernelι_iff, hq.2.2.2]
  rfl

end Kernel

section Center

variable {R : Type u} [CommRing R]
  {A M Z C : GroupScheme (Spec (CommRingCat.of R))}
  (z : Z ⟶ M) (hz : IsSchemeTheoreticCenter z)
  (i : A ⟶ M) (hi : IsCentral i) (j : A ⟶ Z) (hj : j ≫ z = i)
  (q : Z ⟶ C)

/-- Read an algebraic quotient map on the full actual scheme-center point group. -/
def schemeCenterQuotientPointMap : schemeCenterPoints M →* rationalPoints C :=
  (rationalPoints.map q).comp
    (hz.isRepresentedBy.pointsEquiv (Over.mk (𝟙 _))).symm.toMonoidHom

include hj in
/-- The quotient map on actual center points has exactly the literal
denominator from `CentralPointQuotient`. -/
theorem schemeCenterQuotientPointMap_ker
    (hq : IsFppfQuotient (SubgroupFunctor.range j) q) :
    (schemeCenterQuotientPointMap z hz q).ker = centralRationalPointImage i hi := by
  let e : rationalPoints Z ≃* schemeCenterPoints M :=
    hz.isRepresentedBy.pointsEquiv (Over.mk (𝟙 _))
  ext x
  change rationalPoints.map q (e.symm x) = 1 ↔ x ∈ centralRationalPointImage i hi
  change e.symm x ∈ (rationalPoints.map q).ker ↔ _
  rw [rationalPoints_ker_eq_range_of_fppfQuotient j q hq,
    mem_centralRationalPointImage]
  constructor
  · rintro ⟨a, ha⟩
    refine ⟨a, ?_⟩
    have hv := congrArg (fun y : rationalPoints Z => (e y).val) ha
    change rationalPoints.map z (rationalPoints.map j a) = (e (e.symm x)).val at hv
    rw [e.apply_symm_apply] at hv
    simpa only [rationalPoints.map_apply,
      Category.assoc, ← Grp.comp_hom_hom, hj] using hv
  · rintro ⟨a, ha⟩
    refine ⟨a, e.injective ?_⟩
    apply Subtype.ext
    change rationalPoints.map z (rationalPoints.map j a) = (e (e.symm x)).val
    rw [e.apply_symm_apply]
    simpa only [rationalPoints.map_apply,
      Category.assoc, ← Grp.comp_hom_hom, hj] using ha

variable [TopologicalSpace R] [IsLocalRing R] [ContinuousMul R] [IsOpenUnits R]
  [IsAffine M.X.left] [IsAffine C.X.left]

/-- Algebraic open sections make the actual center-point quotient map a
quotient map for the fixed inherited and canonical topologies. -/
theorem isQuotientMap_schemeCenterQuotientPointMap
    (hs : HasOpenSectionsAtPoints R R q.hom.hom) :
    @IsQuotientMap (schemeCenterPoints M) (rationalPoints C)
      (schemeCenterPointTopology M) (rationalPointTopology R C.X)
      (schemeCenterQuotientPointMap z hz q) := by
  let : IsClosedImmersion z.hom.hom.left := hz.1
  let : IsAffine Z.X.left := isAffine_of_isAffineHom z.hom.hom.left
  let : TopologicalSpace (rationalPoints Z) := rationalPointTopology R Z.X
  let : TopologicalSpace (rationalPoints C) := rationalPointTopology R C.X
  let : TopologicalSpace (schemeCenterPoints M) := schemeCenterPointTopology M
  exact (isQuotientMap_rationalPointMap_of_open_sections R q.hom.hom hs).comp
    (schemeCenterRepresentativeHomeomorph z hz).symm.isQuotientMap

/-- A supplied fppf quotient and its algebraic open sections identify the
literal full-center point quotient with the quotient scheme's actual points. -/
def centralPointQuotientModelHomeomorph
    (hq : IsFppfQuotient (SubgroupFunctor.range j) q)
    (hs : HasOpenSectionsAtPoints R R q.hom.hom) :
    let : TopologicalSpace (rationalPoints C) := rationalPointTopology R C.X
    let : TopologicalSpace (CentralPointQuotient i hi) := centralPointQuotientTopology i hi
    CentralPointQuotient i hi ≃ₜ* rationalPoints C := by
  let : TopologicalSpace (rationalPoints C) := rationalPointTopology R C.X
  let : TopologicalSpace (schemeCenterPoints M) := schemeCenterPointTopology M
  exact pointQuotientHomeomorph (centralRationalPointImage i hi)
    (schemeCenterQuotientPointMap z hz q)
    (schemeCenterQuotientPointMap_ker z hz i hi j hj q hq)
    (isQuotientMap_schemeCenterQuotientPointMap z hz q hs)

end Center

end Langlands.GroupScheme
