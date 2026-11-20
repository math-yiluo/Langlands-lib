import Langlands.Geometry.Analytic.SpaceAnalytificationAffinoidPointDescent
import Langlands.Geometry.Analytic.FiniteEtaleOverRecognition

/-! # Finite étale lifts on charts of an analytification -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Set
open _root_.AlgebraicGeometry

namespace Langlands.Analytic.SpaceAnalytification

open Langlands.AlgebraicGeometry Langlands.AlgebraicGeometry.AlgebraicSpace
open AffineAnalytification SaturatedAtlasPresentation
open PresentedAffinoidAlgebra.AffinoidPushout

variable {K : Type u} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {X : AlgebraicSpace (Spec (CommRingCat.of K))}
  {Y : LocalizedCategory.{u, u, u} (K := K)} {p : PointFamily K X Y}

/-- A finite étale chart above the target chart supplies affinoid points
for every bounded map into the target chart. -/
def AffinoidPointHomFiniteChartStatement
    (hp : IsAnalytification K X Y p) (hX : IsSeparated X) (hft : LocallyOfFiniteTypeOverBase X) :
    Prop :=
  ∀ {D U R : PresentedAffinoidAlgebra K} (f : BoundedAlgHom K D U) (g : BoundedAlgHom K D R),
    f.IsFiniteBanach → f.AlgebraicallyFiniteEtale →
    Function.Surjective (BanachSpectrum.comap f.toBoundedRingHom) →
    ∀ (i : localizedAffinoidSpectrum D ⟶ Y)
      {A : Type u} [CommRing A] [Algebra K A] (P : FinitePolynomialPresentation K A)
      (x : RingPoints K X A) (s : localizedAffinoidSpectrum U ⟶ localized K P),
      s ≫ p A P x = localizationFunctor.map (SmallAffinoidSpectrum.map.{u, u} f) ≫ i →
      ∃ a : RingPoints K X R, affinoidPointHom hp hX hft R a =
        localizationFunctor.map (SmallAffinoidSpectrum.map.{u, u} g) ≫ i

theorem exists_affinoidPointHom_of_finite_chart
    (hp : IsAnalytification K X Y p) (hX : IsSeparated X) (hft : LocallyOfFiniteTypeOverBase X) :
    AffinoidPointHomFiniteChartStatement hp hX hft := by
  intro D U R f g hf he hsurj i A _ _ P x s hs
  let L := SmallAffinoidSpectrum.map.{u, u} (leftMap f g)
  let T := algebra f g
  have hfin := finiteBanachPushout D U R f g hf
  have het : (rightMap f g).AlgebraicallyFiniteEtale :=
    BoundedAlgHom.algebraicallyFiniteEtale_of_isEtaleAtPoint _ hfin.finite
      (fun z => rightMap_isEtaleAtPoint_of_tensorComparison f g
        (finiteTensorComparison D U R f g hf) hf.finite.finiteType z (he.isEtaleAtPoint _))
  have hcov : Function.Surjective (BanachSpectrum.comap (rightMap f g).toBoundedRingHom) := by
    intro z
    obtain ⟨y, hy⟩ := hsurj (BanachSpectrum.comap g.toBoundedRingHom z)
    obtain ⟨w, -, hw⟩ := PresentedAffinoidAlgebra.AffinoidPushout.exists_point f g y z hy
    exact ⟨w, hw⟩
  obtain ⟨φ, hφ⟩ := (localizedAffinoidHomEquiv K P T).surjective (localizationFunctor.map L ≫ s)
  rw [localizedAffinoidHomEquiv_apply] at hφ
  have hpb := SmallAffinoidSpectrum.pushout_localized_isPullback.{u, u} f g
  apply affinoidPointHom_descend hp hX hft (rightMap f g) hfin het hcov _
    (RingPoints.changeRing φ x)
  rw [affinoidPointHom_test hp hX hft T P, hφ, Category.assoc, hs,
    ← Category.assoc, ← Category.assoc]
  exact congrArg (· ≫ i) hpb.w.symm

end Langlands.Analytic.SpaceAnalytification
