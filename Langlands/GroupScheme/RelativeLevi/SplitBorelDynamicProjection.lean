import Langlands.GroupScheme.RelativeLevi.SplitBorelVectorSeriesStatement
import Langlands.GroupScheme.Reductive.AffineRegularCentralizer
import Langlands.GroupScheme.RelativeLevi.DynamicReductiveQuotient
import Langlands.GroupScheme.Rational.LeviFactorization
import Langlands.GroupScheme.ClosedSubgroupMonomorphism

/-! # Split projection of the regular dynamic Borel -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.AffineRegularBorel

variable {R : Type u} [CommRing R] {I J : Type u} [Fintype I]
  {G : GroupScheme (Spec (CommRingCat.of R))} [IsAffineHom G.X.hom]
  (i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G) (n : I → ℤ)

local instance : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom

/-- The actual affine contracting group of the chosen coordinate cocharacter. -/
abbrev contractingGroup : GroupScheme (Spec (CommRingCat.of R)) :=
  Dynamic.Affine.unipotentScheme (cocharacter i n)

/-- Its inclusion into the regular dynamic Borel, defined by the all-test
inclusion of contracting points into parabolic points. -/
def contractingInclusion : contractingGroup i n ⟶ borel i n :=
  (Dynamic.Affine.isRepresentedBy_parabolicHom (cocharacter i n)).factorHom
    (Dynamic.Affine.unipotentHom (cocharacter i n)) (by
      rw [(Dynamic.Affine.isRepresentedBy_unipotentHom (cocharacter i n)).2]
      exact Dynamic.unipotent_le_parabolic _)

/-- The contracting inclusion retains its specified map to the ambient group. -/
theorem contractingInclusion_comp :
    contractingInclusion i n ≫ inclusion i n =
      Dynamic.Affine.unipotentHom (cocharacter i n) :=
  SubgroupFunctor.IsRepresentedBy.factorHom_comp _ _ _

/-- The contracting group is a closed subgroup of the Borel. -/
theorem isClosedSubgroup_contractingInclusion :
    IsClosedSubgroup (contractingInclusion i n) := by
  apply IsClosedSubgroup.of_comp (Dynamic.Affine.isClosedSubgroup_parabolicHom _)
  rw [contractingInclusion_comp]
  exact Dynamic.Affine.isClosedSubgroup_unipotentHom _

/-- The represented contracting group is affine over the original ring. -/
theorem isAffineHom_contractingGroup : IsAffineHom (contractingGroup i n).X.hom := by
  have := Dynamic.Affine.isClosedSubgroup_unipotentHom (cocharacter i n)
  exact this.isAffineHom

variable (P : RootDatum J (I → ℤ) (I → ℤ))
  (hP : IsFibrewiseRootDatumOf I G i P)
  (hn : ∀ a : J, ∑ j, P.root a j * n j ≠ 0)
  (hG : IsReductive G) (hi : IsClosedSubgroup i)
  (hmax : IsFibrewiseMaximalTorus
    (T := splitTorus.commGroupScheme (Spec (CommRingCat.of R)) I) i)

include hP hn hG hi hmax in
/-- For regular exponents the original coordinate torus represents the
centralizer on every test scheme. -/
theorem torus_represents_centralizer :
    (Dynamic.centralizer (cocharacter i n)).IsRepresentedBy i :=
  ⟨hi.mono_overHom, (centralizer_eq_range i n P hP hn hG hi hmax).symm⟩

/-- The section given by the original torus inside the regular Borel. -/
def torusSection : splitTorus (Spec (CommRingCat.of R)) I ⟶ borel i n :=
  Dynamic.centralizerToParabolic
    (Dynamic.Affine.isRepresentedBy_parabolicHom (cocharacter i n))
    (torus_represents_centralizer i n P hP hn hG hi hmax)

/-- Limit at zero, with its centralizer identified with the original torus. -/
def torusProjection : borel i n ⟶ splitTorus (Spec (CommRingCat.of R)) I :=
  Dynamic.limitGroupHom
    (Dynamic.Affine.isRepresentedBy_parabolicHom (cocharacter i n))
    (torus_represents_centralizer i n P hP hn hG hi hmax)

/-- The section recovers the specified ambient torus inclusion. -/
theorem torusSection_comp_inclusion :
    torusSection i n P hP hn hG hi hmax ≫ inclusion i n = i :=
  Dynamic.centralizerToParabolic_comp _ _

/-- The original torus section splits the actual limit projection. -/
theorem torusSection_comp_torusProjection :
    torusSection i n P hP hn hG hi hmax ≫
      torusProjection i n P hP hn hG hi hmax = 𝟙 _ :=
  Dynamic.centralizerToParabolic_comp_limitGroupHom _ _

/-- The limit projection is an fppf quotient by the actual affine contracting
inclusion. In particular, its scheme kernel has the stated range on all tests. -/
theorem isFppfQuotient_torusProjection :
    RelativeRoot.IsFppfQuotient (SubgroupFunctor.range (contractingInclusion i n))
      (torusProjection i n P hP hn hG hi hmax) := by
  let : Smooth G.X.hom := hG.smooth
  have hU : (Dynamic.unipotent (cocharacter i n)).IsRepresentedBy
      (contractingInclusion i n ≫ inclusion i n) := by
    rw [contractingInclusion_comp]
    exact Dynamic.Affine.isRepresentedBy_unipotentHom _
  let : Smooth (contractingGroup i n).X.hom :=
    ((dynamicBaseSmoothConnected _ G (cocharacter i n) _ _).1 hU).1
  exact Dynamic.isFppfQuotient_limitGroupHom_range (contractingInclusion i n)
    (Dynamic.Affine.isRepresentedBy_parabolicHom _)
    (torus_represents_centralizer i n P hP hn hG hi hmax) hU

include hP hn hG hi hmax in
/-- A finite vector series for the actual contracting group supplies exactly
the remaining input to split Borel structure. -/
theorem hasSplitBorelVectorSeries_of_contractingSeries
    (hseries : ∃ l : ℕ, HasAffineVectorSeries l (contractingGroup i n)) :
    HasSplitBorelVectorSeries i := by
  exact ⟨borel i n, contractingGroup i n, inclusion i n, contractingInclusion i n,
    torusProjection i n P hP hn hG hi hmax, torusSection i n P hP hn hG hi hmax,
    isRelativeBorel i n P hP hn hG hmax, isClosedSubgroup_contractingInclusion i n,
    isAffineHom_contractingGroup i n, torusSection_comp_inclusion i n P hP hn hG hi hmax,
    torusSection_comp_torusProjection i n P hP hn hG hi hmax,
    isFppfQuotient_torusProjection i n P hP hn hG hi hmax, hseries⟩

end Langlands.GroupScheme.AffineRegularBorel
