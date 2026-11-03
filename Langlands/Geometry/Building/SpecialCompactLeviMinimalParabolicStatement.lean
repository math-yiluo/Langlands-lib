import Langlands.Geometry.Building.SpecialCompactLevi
import Langlands.GroupScheme.Dynamic.ClosedSubgroup
import Langlands.GroupScheme.Rational.MinimalParabolic

/-!
# The chosen minimal parabolic in the actual standard Levi

The closed-subgroup comparison is proved from the existing dynamic comparison.
Reductivity and minimality remain explicit structural statement targets.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.Standard

variable {F : Type u} [Field F]
  {S : CommGroupScheme (Spec (CommRingCat.of F))}
  {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] (i : S.toGrp ⟶ G)
  (ν : cocharacterLattice S) (J : Set (characterLattice S))

/-- The dynamic parabolic of the same cocharacter in the actual standard Levi.
Its minimality is a separate conclusion of the structural target below. -/
def leviGenericParabolic : SubgroupFunctor (leviScheme i ν J) :=
  Dynamic.parabolic (CommGroupScheme.groupHom ν ≫ leviTorusHom i ν J)

/-- Closed-subgroup functoriality identifies the intrinsic dynamic parabolic
with the pullback of the ambient one, on every test scheme. -/
theorem leviGenericParabolic_eq_comap_dynamic :
    leviGenericParabolic i ν J =
      (Dynamic.parabolic (CommGroupScheme.groupHom ν ≫ i)).comap (leviHom i ν J) := by
  unfold leviGenericParabolic
  rw [Dynamic.parabolic_eq_comap_of_isClosedSubgroup _ _ (isClosedSubgroup_leviHom i ν J)]
  simp only [Category.assoc, leviTorusHom_comp]

/-- The standard empty-index endpoint is the only additional input needed for
the all-test comparison with the chosen ambient standard minimal parabolic. -/
theorem leviGenericParabolic_eq_comap_standard
    (hP : standardParabolic i ν ∅ =
      Dynamic.parabolic (CommGroupScheme.groupHom ν ≫ i)) :
    leviGenericParabolic i ν J = (standardParabolic i ν ∅).comap (leviHom i ν J) := by
  rw [hP]
  exact leviGenericParabolic_eq_comap_dynamic i ν J

/-- On actual rational points the image is the literal intersection with the
same ambient standard minimal parabolic. -/
theorem leviGenericParabolic_points_map
    (hP : standardParabolic i ν ∅ =
      Dynamic.parabolic (CommGroupScheme.groupHom ν ≫ i)) :
    ((leviGenericParabolic i ν J).carrier (Over.mk (𝟙 _))).map
        (rationalPoints.map (leviHom i ν J)) =
      standardParabolicPoints i ν ∅ ⊓ standardLeviPoints i ν J := by
  have h := congrArg (fun Q : SubgroupFunctor G => Q.carrier (Over.mk (𝟙 _)))
    (Dynamic.range_inf_parabolic
      (CommGroupScheme.groupHom ν ≫ leviTorusHom i ν J) (leviHom i ν J)
      (isClosedSubgroup_leviHom i ν J))
  simp only [Category.assoc, leviTorusHom_comp,
    (isRepresentedBy_leviHom i ν J).2] at h
  rw [← hP] at h
  exact h.symm.trans (inf_comm _ _)

/-- Algebraic compatibility of the actual standard Levi with the chosen
ambient minimal parabolic. These are conclusions to establish, not input data
or an assumed building-validity certificate. -/
def LeviMinimalParabolicCompatible : Prop :=
  IsConnectedReductive (leviScheme i ν J) ∧
    IsMinimalParabolicFunctor (standardParabolic i ν ∅) ∧
    IsMinimalParabolicFunctor (leviGenericParabolic i ν J) ∧
    leviGenericParabolic i ν J = (standardParabolic i ν ∅).comap (leviHom i ν J) ∧
    ((leviGenericParabolic i ν J).carrier (Over.mk (𝟙 _))).map
        (rationalPoints.map (leviHom i ν J)) =
      standardParabolicPoints i ν ∅ ⊓ standardLeviPoints i ν J

end Langlands.GroupScheme.Standard

namespace Langlands.GroupScheme

/-- Over every full nonarchimedean local field, each actual standard Levi has
the minimal parabolic induced by the same torus and cocharacter, and its image
is the intersection with the chosen ambient minimal parabolic. -/
def StandardLeviMinimalParabolicCompatibilityStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) (hG : IsConnectedReductive G)
    (S : CommGroupScheme (Spec (CommRingCat.of F))) (i : S.toGrp ⟶ G),
    IsMaximalSplitTorus i → ∀ ν : cocharacterLattice S,
      haveI := hG.isAffineHom
      IsGenericCocharacter i ν →
        ∀ J : Set (characterLattice S), J ⊆ simpleRelativeRoots i ν →
          Standard.LeviMinimalParabolicCompatible i ν J

end Langlands.GroupScheme
