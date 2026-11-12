import Langlands.Representation.Exponents.LeviCuspidalEmbeddingSteps
import Langlands.GroupScheme.Rational.StandardCocharacterProof
import Langlands.GroupScheme.Rational.StandardLeviSplitComponentProof
import Langlands.GroupScheme.Rational.StandardParabolicEndpointsProof
import Langlands.GroupScheme.Rational.AffineGeometricUnipotentRadical
import Langlands.GroupScheme.Dynamic.GeometricUnipotentRadicalReduction
import Langlands.GroupScheme.Absolute.DynamicParabolicRecognition
import Langlands.GroupScheme.Rational.MaximalLeviDynamicReduction

/-! # Canonical standard parabolics as actual parabolic data

For every subset of the actual simple relative roots, the existing canonical
standard schemes and maps satisfy all clauses of `ParabolicDatum`. The full
simple-root subset gives an isomorphism onto the ambient group.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.Standard

variable {k : Type u} [Field k]
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  (i : T.toGrp ⟶ G) (ν : cocharacterLattice T)
  (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
  (hν : IsGenericCocharacter i ν)
  (J : Set (characterLattice T)) (hJ : J ⊆ simpleRelativeRoots i ν)

include hG hi hν hJ in
/-- The original canonical standard maps form a rational parabolic with its
rational Levi, full geometric radical and Levi-first multiplication isomorphism. -/
theorem parabolicStructure :
    IsParabolicSubgroup (parabolicHom i ν J) ∧
      IsRationalLeviSubgroup (leviToParabolic i ν J) ∧
      LeviSubgroup.IsGeometricUnipotentRadical (unipotentToParabolic i ν J) ∧
      IsIso (subgroupMultiplication (leviToParabolic i ν J)
        (unipotentToParabolic i ν J)) := by
  have := hi.isSplitSubtorus.mono
  have := hG.smooth
  obtain ⟨⟨ζ, hζ⟩, hcompare⟩ := standardCocharacter k G hG T i hi ν hν J hJ
  have hP : (Dynamic.parabolic (CommGroupScheme.groupHom ζ ≫ i)).IsRepresentedBy
      (parabolicHom i ν J) := by
    rw [← (hcompare ζ hζ).1]
    exact isRepresentedBy_parabolicHom i ν J
  have hL : (Dynamic.centralizer (CommGroupScheme.groupHom ζ ≫ i)).IsRepresentedBy
      (leviHom i ν J) := by
    rw [← (hcompare ζ hζ).2.1]
    exact isRepresentedBy_leviHom i ν J
  have hU : (Dynamic.unipotent (CommGroupScheme.groupHom ζ ≫ i)).IsRepresentedBy
      (unipotentHom i ν J) := by
    rw [← (hcompare ζ hζ).2.2]
    exact isRepresentedBy_unipotentHom i ν J
  have hM := (standardLeviSplitComponentStatement k G hG T i hi ν hν J hJ).1
  have hmul := Dynamic.isIso_subgroupMultiplication hP hL hU
    (leviToParabolic i ν J) (unipotentToParabolic i ν J)
    (leviToParabolic_comp i ν J) (unipotentToParabolic_comp i ν J)
  have hUcomp :
      (Dynamic.unipotent (CommGroupScheme.groupHom ζ ≫ i)).IsRepresentedBy
        (unipotentToParabolic i ν J ≫ parabolicHom i ν J) := by
    rw [unipotentToParabolic_comp]
    exact hU
  have hrad := Dynamic.isGeometricUnipotentRadical_of_centralizer
    (CommGroupScheme.groupHom ζ ≫ i) (leviHom i ν J) (parabolicHom i ν J)
    (unipotentToParabolic i ν J) hP hUcomp hL hM
  let : IsAffineHom (parabolicScheme i ν J).X.hom :=
    (isClosedSubgroup_parabolicHom i ν J).isAffineHom
  have hlc : IsClosedSubgroup (leviToParabolic i ν J) :=
    IsClosedSubgroup.of_comp (isClosedSubgroup_parabolicHom i ν J)
      (by rw [leviToParabolic_comp]; exact isClosedSubgroup_leviHom i ν J)
  exact ⟨isParabolicSubgroup_of_range_eq_dynamicParabolic hG
      (parabolicHom i ν J) (isClosedSubgroup_parabolicHom i ν J) _ hP.2,
    IsRationalLeviSubgroup.of_geometricUnipotentRadical hlc hM hrad hmul,
    hrad.leviSubgroup, hmul⟩

end Langlands.GroupScheme.Standard

namespace Langlands.Aubert.General.RepresentedParabolic.ParabolicDatum

open GroupScheme

variable {k : Type u} [Field k]
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  (i : T.toGrp ⟶ G) (ν : cocharacterLattice T)
  (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
  (hν : IsGenericCocharacter i ν)

/-- Actual standard parabolic data using precisely the existing canonical
standard schemes and their existing inclusions. -/
def standard (J : Set (characterLattice T)) (hJ : J ⊆ simpleRelativeRoots i ν) :
    ParabolicDatum G where
  P := Standard.parabolicScheme i ν J
  M := Standard.leviScheme i ν J
  U := Standard.unipotentScheme i ν J
  p := Standard.parabolicHom i ν J
  l := Standard.leviToParabolic i ν J
  r := Standard.unipotentToParabolic i ν J
  hp := (Standard.parabolicStructure i ν hG hi hν J hJ).1
  hl := (Standard.parabolicStructure i ν hG hi hν J hJ).2.1
  hr := (Standard.parabolicStructure i ν hG hi hν J hJ).2.2.1
  hmul := (Standard.parabolicStructure i ν hG hi hν J hJ).2.2.2

/-- The bundled standard parabolic has exactly the choice-free standard range
on every test scheme. -/
theorem range_standard_p (J : Set (characterLattice T))
    (hJ : J ⊆ simpleRelativeRoots i ν) :
    SubgroupFunctor.range (standard i ν hG hi hν J hJ).p = standardParabolic i ν J :=
  (Standard.isRepresentedBy_parabolicHom i ν J).2

/-- Its bundled Levi has exactly the choice-free standard ambient range. -/
theorem range_standard_l_comp_p (J : Set (characterLattice T))
    (hJ : J ⊆ simpleRelativeRoots i ν) :
    SubgroupFunctor.range
        ((standard i ν hG hi hν J hJ).l ≫ (standard i ν hG hi hν J hJ).p) =
      standardLevi i ν J := by
  change SubgroupFunctor.range
      (Standard.leviToParabolic i ν J ≫ Standard.parabolicHom i ν J) = _
  rw [Standard.leviToParabolic_comp]
  exact (Standard.isRepresentedBy_leviHom i ν J).2

/-- Its bundled radical has exactly the choice-free standard ambient range. -/
theorem range_standard_r_comp_p (J : Set (characterLattice T))
    (hJ : J ⊆ simpleRelativeRoots i ν) :
    SubgroupFunctor.range
        ((standard i ν hG hi hν J hJ).r ≫ (standard i ν hG hi hν J hJ).p) =
      standardUnipotent i ν J := by
  change SubgroupFunctor.range
      (Standard.unipotentToParabolic i ν J ≫ Standard.parabolicHom i ν J) = _
  rw [Standard.unipotentToParabolic_comp]
  exact (Standard.isRepresentedBy_unipotentHom i ν J).2

/-- At the full simple-root subset, the original canonical parabolic inclusion
is an isomorphism onto the ambient group. -/
theorem isIso_standard_full_p :
    IsIso (standard i ν hG hi hν (simpleRelativeRoots i ν) Set.Subset.rfl).p := by
  have := hi.isSplitSubtorus.mono
  have htop : SubgroupFunctor.range (Standard.parabolicHom i ν (simpleRelativeRoots i ν)) =
      ⊤ := by
    rw [(Standard.isRepresentedBy_parabolicHom i ν (simpleRelativeRoots i ν)).2]
    exact (standardParabolicEndpoints k G hG T i hi ν hν).2.2.1
  exact isIso_of_full_range _ (Standard.isRepresentedBy_parabolicHom
    i ν (simpleRelativeRoots i ν)).1 htop

end Langlands.Aubert.General.RepresentedParabolic.ParabolicDatum
