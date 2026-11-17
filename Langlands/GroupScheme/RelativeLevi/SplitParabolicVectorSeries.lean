import Langlands.GroupScheme.RelativeLevi.SplitParabolicWeightChart
import Langlands.GroupScheme.RelativeLevi.SplitWeightDynamicComparison

/-! # Vector-bundle series for arbitrary split contracting groups -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme

open LocalSplitCell RelativeUnipotent

variable {R : Type u} [CommRing R]
  {I J : Type u} [Fintype I] [Finite J]
  {G : GroupScheme (Spec (CommRingCat.of R))} [IsAffineHom G.X.hom]
  {i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G}
  {P : RootDatum J (I → ℤ) (I → ℤ)}
  {fam : J → (Ga R ⟶ G)} {wt : I → ℤ}

local instance : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom

namespace SplitParabolicWeightChart

variable (C : SplitParabolicWeightChart i P fam wt)

omit [Finite J] in
/-- Exact natural weights force nonnegative pairings on every chosen positive root. -/
theorem coPairing_nonneg {a : J} (ha : C.base.IsPos a) :
    0 ≤ coPairing (P.root a) wt := by
  obtain ⟨k, hk⟩ := C.index.surjective ⟨a, ha⟩
  have h := C.weight_eq k
  rw [hk] at h
  rw [← h]
  exact Int.natCast_nonneg _

/-- The complementary roots have nonpositive pairings, including the Levi roots. -/
theorem coPairing_nonpos [P.IsReduced] {a : J} (ha : ¬ C.base.IsPos a) :
    coPairing (P.root a) wt ≤ 0 := by
  let := P.indexNeg
  have h := C.coPairing_nonneg ((RootPairing.Base.IsPos.neg_iff_not C.base a).mpr ha)
  have he : P.root (-a) = - P.root a := by
    change P.root (P.reflectionPerm a a) = _
    simp
  change 0 ≤ coPairingLinear wt (P.root (-a)) at h
  rw [he, map_neg] at h
  change 0 ≤ -coPairing (P.root a) wt at h
  omega

variable (hG : IsReductive G)
  (hmax : IsFibrewiseMaximalTorus
    (T := splitTorus.commGroupScheme (Spec (CommRingCat.of R)) I) i)
  (hP : IsFibrewiseRootDatumOf I G i P)
  (hfam : ∀ a, IsRootParametrization i (P.root a) (fam a))

include hG hmax hP hfam in
/-- The chart's weight-cutoff-one inclusion represents the supplied, possibly
nonregular, contracting functor on all scheme tests. -/
theorem isRepresentedBy_weightInclusion :
    (Dynamic.unipotent (AffineRegularBorel.cocharacter i wt)).IsRepresentedBy
      (C.weights.inclusion 0 ≫
        Dynamic.Affine.unipotentHom (AffineRegularBorel.cocharacter i C.cocharacter)) := by
  classical
  let : P.IsReduced := hP.isReduced
  let neg := (Finite.equivFin {a // ¬ C.base.IsPos a}).symm
  let pos : Fin C.chart.dimension ≃ {a // C.base.IsPos a} := C.index
  let := LocalSplitBigCell.isOpenImmersion_cellMap hG hmax hP C.base fam hfam neg pos
  let hu : TorusEquivariant i (fun a => P.root a) fam :=
    fun a Z t c => (hfam a).equivariant Z t c
  let j := Dynamic.Affine.unipotentHom
    (AffineRegularBorel.cocharacter i C.cocharacter)
  let : Mono j.hom.hom :=
    (Dynamic.Affine.isRepresentedBy_unipotentHom
      (AffineRegularBorel.cocharacter i C.cocharacter)).1
  let : IsAffineHom (AffineRegularBorel.contractingGroup i wt).X.hom :=
    AffineRegularBorel.isAffineHom_contractingGroup i wt
  let : IsAffine (AffineRegularBorel.contractingGroup i wt).X.left :=
    isAffine_of_isAffineHom (AffineRegularBorel.contractingGroup i wt).X.hom
  exact isRepresentedBy_positiveWeightInclusion C.chart C.weights j C.root_comp
    hu wt C.weight_eq (fun k => C.coPairing_nonpos (neg k).property)
    (Dynamic.Affine.unipotentHom (AffineRegularBorel.cocharacter i wt))
    (Dynamic.Affine.isRepresentedBy_unipotentHom (AffineRegularBorel.cocharacter i wt))

/-- An actual isomorphism from the chart's positive-weight term to the
contracting group of the originally supplied cocharacter. -/
def dynamicIso : C.weights.groupScheme 0 ≅ AffineRegularBorel.contractingGroup i wt :=
  (C.isRepresentedBy_weightInclusion hG hmax hP hfam).isoOfIsRepresentedBy
    (Dynamic.Affine.isRepresentedBy_unipotentHom (AffineRegularBorel.cocharacter i wt))

/-- The isomorphism recovers the specified ambient inclusion. -/
theorem dynamicIso_hom_comp :
    (C.dynamicIso hG hmax hP hfam).hom ≫
      Dynamic.Affine.unipotentHom (AffineRegularBorel.cocharacter i wt) =
      C.weights.inclusion 0 ≫
        Dynamic.Affine.unipotentHom (AffineRegularBorel.cocharacter i C.cocharacter) :=
  SubgroupFunctor.IsRepresentedBy.isoOfIsRepresentedBy_hom_comp _ _

include C hG hmax hP hfam in
/-- Every supplied adapted chart yields a finite vector-bundle series on
the original cocharacter's actual contracting group. -/
theorem hasFiniteVectorBundleSeries :
    HasFiniteVectorBundleSeries (AffineRegularBorel.contractingGroup i wt) :=
  HasFiniteVectorBundleSeries.of_iso (C.dynamicIso hG hmax hP hfam)
    (RootWeightData.hasFiniteVectorBundleSeries C.weights)

end SplitParabolicWeightChart

/-- Actual root parametrizations give a finite vector-bundle series for
every split-coordinate contracting group; strict regularity is not required. -/
theorem hasFiniteVectorBundleSeries_splitContractingGroup
    (hG : IsReductive G)
    (hmax : IsFibrewiseMaximalTorus
      (T := splitTorus.commGroupScheme (Spec (CommRingCat.of R)) I) i)
    (hP : IsFibrewiseRootDatumOf I G i P)
    (hfam : ∀ a, IsRootParametrization i (P.root a) (fam a)) :
    HasFiniteVectorBundleSeries (AffineRegularBorel.contractingGroup i wt) := by
  obtain ⟨C⟩ := nonempty_splitParabolicWeightChart (wt := wt) hG hmax hP hfam
  exact C.hasFiniteVectorBundleSeries hG hmax hP hfam

end Langlands.GroupScheme
