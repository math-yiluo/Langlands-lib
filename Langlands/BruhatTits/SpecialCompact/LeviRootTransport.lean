import Langlands.Geometry.Building.RootDatumValuation
import Langlands.GroupScheme.Rational.DynamicSemigroupProof
import Langlands.GroupScheme.Rational.StandardLeviStandardFamiliesProof
import Langlands.GroupScheme.Dynamic.LieProof
import Langlands.GroupScheme.Rational.DerivedRootTransport
import Langlands.GroupScheme.Rational.CyclicRootFunctorComparisonProof
import Langlands.GroupScheme.Rational.RootKernelTorus

/-! # Actual root-group transport into a cocharacter centralizer -/

noncomputable section
universe u
open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme

namespace Langlands.BruhatTits.SpecialCompact

section General
variable {F : Type u} [Field F]
    {S : CommGroupScheme (Spec (CommRingCat.of F))}
    {G M : GroupScheme (Spec (CommRingCat.of F))}
    [IsAffineHom G.X.hom] [Smooth G.X.hom] [ConnectedSpace G.X.left]
    (hS : IsSplitTorus S.toGrp) (i : S.toGrp ⟶ G)

include hS in
/-- An ambient root subgroup with zero cocharacter pairing lies in the
actual dynamic Levi on every test scheme. -/
theorem rootSubgroup_le_centralizer_of_pairing_zero
    (ζ : cocharacterLattice S) (a : characterLattice S) (ha : a ≠ 0)
    (haz : latticePairing S a ζ = 0) :
    RelativeRoot.subgroup i a ≤ Dynamic.centralizer (CommGroupScheme.groupHom ζ ≫ i) := by
  rw [← RelativeRoot.weightFiltration_one_eq_subgroup hS i a ha,
    (RelativeRoot.dynamicSemigroupComparison F G inferInstance inferInstance
      inferInstance S hS i ζ).2.1]
  apply RelativeRoot.semigroupSubgroup_mono
  rintro _ ⟨n, _, _, rfl⟩
  change latticePairing S (n • a) ζ = 0
  rw [map_nsmul]
  change n • latticePairing S a ζ = 0
  rw [haz, nsmul_zero]

variable [IsAffineHom M.X.hom] [LocallyOfFiniteType M.X.hom]
    (iM : S.toGrp ⟶ M) (j : M ⟶ G) (hcomp : iM ≫ j = i)
    (ζ : cocharacterLattice S)
    (hj : (Dynamic.centralizer (CommGroupScheme.groupHom ζ ≫ i)).IsRepresentedBy j)
    (hjc : IsClosedSubgroup j)

include hS hcomp hj hjc

/-- Closed root-group pullback for every nonzero character at the same torus. -/
theorem leviRootGroupPoints_eq_comap (a : characterLattice S) (ha : a ≠ 0) :
    Langlands.Geometry.Building.rootGroupPoints iM a =
      (Langlands.Geometry.Building.rootGroupPoints i a).comap (rationalPoints.map j) := by
  obtain ⟨hqc, hflat, hsurj⟩ := RelativeRoot.characterFpqc F S hS a ha
  let := hqc
  let := hflat
  let := hsurj
  have hsub := RelativeRoot.subgroup_comap_closedEmbedding iM a j hjc
  rw [hcomp] at hsub
  exact congrArg (fun A : SubgroupFunctor M => A.carrier (Over.mk (𝟙 _))) hsub.symm

/-- The same-torus Levi root group has the literal ambient root group as
its image under the closed inclusion. -/
theorem map_leviRootGroupPoints (a : characterLattice S)
    (ha : a ∈ relativeRoots iM) :
    (Langlands.Geometry.Building.rootGroupPoints iM a).map (rationalPoints.map j) =
      Langlands.Geometry.Building.rootGroupPoints i a := by
  have hroots := relativeRoots_centralizer_factor dynamicLie i iM j hcomp ζ hj
  have haar : a ∈ relativeRoots i := (hroots ▸ ha).1
  have haz : latticePairing S a ζ = 0 := (hroots ▸ ha).2
  obtain ⟨hqc, hflat, hsurj⟩ := RelativeRoot.characterFpqc F S hS a haar.1
  let := hqc
  let := hflat
  let := hsurj
  have hsub := RelativeRoot.subgroup_comap_closedEmbedding iM a j hjc
  rw [hcomp] at hsub
  have heq : Langlands.Geometry.Building.rootGroupPoints iM a =
      (Langlands.Geometry.Building.rootGroupPoints i a).comap (rationalPoints.map j) :=
    congrArg (fun A : SubgroupFunctor M => A.carrier (Over.mk (𝟙 _))) hsub.symm
  rw [heq]
  apply Subgroup.map_comap_eq_self
  intro g hg
  have hle := rootSubgroup_le_centralizer_of_pairing_zero hS i ζ a haar.1 haz
  change g ∈ (SubgroupFunctor.range j).carrier (Over.mk (𝟙 _))
  rw [hj.2]
  exact hle _ hg

section Normalizer
variable [Mono i.hom.hom.left] [Mono iM.hom.hom.left]

omit hS hj hjc in
/-- Transport through the literal Levi inclusion retains the torus automorphism. -/
theorem normalizingAut_leviMap (n : normalizerPoints iM) :
    normalizingAut i (normalizerPointsMap iM j i hcomp n) = normalizingAut iM n :=
  (isNormalizingPoint_normalizingAut i _).unique i
    (hcomp ▸ (isNormalizingPoint_normalizingAut iM n).comp j)

omit hS hj hjc in
/-- Reflections on the whole cocharacter space remain the same reflections
under the literal inclusion of the prescribed Levi. -/
theorem realizesReflection_leviMap (a : characterLattice S) (n : normalizerPoints iM)
    (hn : Langlands.Geometry.Building.RealizesReflection iM a n) :
    Langlands.Geometry.Building.RealizesReflection i a
      (normalizerPointsMap iM j i hcomp n) := by
  refine ⟨?_, ?_⟩
  · rw [weylAction_normalizerPointsMap]
    exact hn.1
  · intro v hv
    have he : Langlands.GroupScheme.RealTorusSpace.normalizerAction i
        (normalizerPointsMap iM j i hcomp n) =
        Langlands.GroupScheme.RealTorusSpace.normalizerAction iM n := by
      change Langlands.GroupScheme.RealTorusSpace.cocharacterRealAut _ =
        Langlands.GroupScheme.RealTorusSpace.cocharacterRealAut _
      rw [normalizingAut_leviMap i iM j hcomp]
    change Langlands.GroupScheme.RealTorusSpace.normalizerAction i _ v = v
    rw [he]
    exact hn.2 v hv

end Normalizer
end General

end Langlands.BruhatTits.SpecialCompact
