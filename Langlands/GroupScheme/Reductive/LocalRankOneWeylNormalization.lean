import Langlands.GroupScheme.Reductive.LocalRankOneNormalizationDescent
import Langlands.GroupScheme.Rational.RootKernelTorus

/-! # Weyl normalization over arbitrary local rings -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace Langlands.GroupScheme

namespace splitTorus.RelativeCocharacterCentralizer

open LocalSplitCell LocalWeylNormalization

variable {R : Type u} [CommRing R] [IsLocalRing R]
  {I : Type u} [Fintype I] [DecidableEq I]
  {G : GroupScheme (Spec (CommRingCat.of R))} [IsAffineHom G.X.hom]
  (i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G) (mu : I → ℤ)
  (hG : IsReductive G)
  (hmax : IsFibrewiseMaximalTorus (T := commGroupScheme _ I) i)
  {J : Type u} {P : RootDatum J (I → ℤ) (I → ℤ)}
  (hP : IsFibrewiseRootDatumOf I G i P) (a : J)
  (ha : ∑ j, P.root a j * mu j = 0)
  (hmu : ∀ b : J, ∑ j, P.root b j * mu j = 0 →
    P.root b = P.root a ∨ P.root b = -P.root a)
  {xp xm : Ga R ⟶ G}
  (hp : IsRootParametrization i (P.root a) xp)
  (hm : IsRootParametrization i (-P.root a) xm)

include hG hmax hmu in
/-- The pointed etale and dual-number constructions discharge all auxiliary
normalization data over the original local base. -/
theorem exists_normalizing_scalar_local (hi : IsClosedSubgroup i) :
    ∃ d : Rˣ, IsNormalizingPoint (T := commGroupScheme _ I) (torusHom I G i mu)
      (scalarWeylPoint (rootLift i mu hp ha)
        (rootLift i mu hm (by
          simpa only [Pi.neg_apply, neg_mul, Finset.sum_neg_distrib, neg_zero] using
            congrArg Neg.neg ha)) (d : R))
      (LocalRankOneWeylData.corootReflectionIso hP a) := by
  let D := corootCellData i mu hG hmax hP a ha hmu hp hm
  let p := pointedEtaleUnitCellReflection i mu hG hmax hP a ha hmu hp hm hi
    (IsLocalRing.closedPoint R)
  let E := p.affineEtaleUnitCell
  obtain ⟨y, t, x, hx⟩ := D.exists_dualFactorization
  exact exists_normalizing_scalar i mu hG hmax hP a ha hmu hp hm E hi hx

/-- A unit rescaling that realizes the prescribed reflection in the actual
rank-one centralizer over the local ring. -/
def normalizingScalar (hi : IsClosedSubgroup i) : Rˣ :=
  (exists_normalizing_scalar_local i mu hG hmax hP a ha hmu hp hm hi).choose

/-- The chosen scalar gives the whole-base reflection identity. -/
theorem normalizingScalar_isNormalizing (hi : IsClosedSubgroup i) :
    IsNormalizingPoint (T := commGroupScheme _ I) (torusHom I G i mu)
      (scalarWeylPoint (rootLift i mu hp ha)
        (rootLift i mu hm (by
          simpa only [Pi.neg_apply, neg_mul, Finset.sum_neg_distrib, neg_zero] using
            congrArg Neg.neg ha))
        (normalizingScalar i mu hG hmax hP a ha hmu hp hm hi : R))
      (LocalRankOneWeylData.corootReflectionIso hP a) :=
  (exists_normalizing_scalar_local i mu hG hmax hP a ha hmu hp hm hi).choose_spec

end splitTorus.RelativeCocharacterCentralizer

namespace LocalSplitCell

open splitTorus.RelativeCocharacterCentralizer

variable {R : Type u} [CommRing R] [IsLocalRing R]
  {I : Type u} [Fintype I] [DecidableEq I]
  {G : GroupScheme (Spec (CommRingCat.of R))} [IsAffineHom G.X.hom]
  (hG : IsReductive G)
  (i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G)
  (hi : IsClosedSubgroup i)
  (hmax : IsFibrewiseMaximalTorus (T := splitTorus.commGroupScheme _ I) i)
  {J : Type u} {P : RootDatum J (I → ℤ) (I → ℤ)}
  (hP : IsFibrewiseRootDatumOf I G i P) (a : J)
  {xp xm : Ga R ⟶ G}
  (hp : IsRootParametrization i (P.root a) xp)
  (hm : IsRootParametrization i (-P.root a) xm)

include hG hi hmax hP hp hm in
/-- Every pair of actual opposite root parametrizations over a local ring
has a unit rescaling whose Weyl product realizes the root reflection. -/
theorem exists_unit_weylNormalization :
    ∃ d : Rˣ, IsWeylPoint i (weylPoint xp (scaleHom (d : R) ≫ xm))
      (P.reflection a) := by
  classical
  have : Finite J := hP.finite
  have := hP.isReduced
  obtain ⟨mu, ha, hmu⟩ :=
    LocalRootGroup.exists_kernel_exponent P (IsLocalRing.ResidueField R) a
  obtain ⟨d, hn⟩ := exists_normalizing_scalar_local i mu hG hmax hP a ha hmu hp hm hi
  refine ⟨d, isWeylPoint_of_isNormalizingPoint ?_⟩
  have h := hn.comp (inclusion I G i mu)
  rw [torusHom_comp, LocalRankOneWeylData.corootReflectionIso,
    LocalRankOneWeylData.reflectionIso_eq_exponentCommIso hP a] at h
  change IsNormalizingPoint (T := splitTorus.commGroupScheme _ I) i
    (weylPoint (rootLift i mu hp ha) (scaleHom (d : R) ≫ rootLift i mu hm _) ≫
      (inclusion I G i mu).hom.hom) _ at h
  rw [← weylPoint_comp, rootLift_comp, Category.assoc, rootLift_comp] at h
  exact h

end LocalSplitCell

end Langlands.GroupScheme
