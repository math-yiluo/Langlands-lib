import Langlands.AlgebraicGeometry.Picard.SquareZeroRelativeObstructionNaturality
import Langlands.AlgebraicGeometry.Picard.ArtinianKernelQuotientCohomologySupport

/-! # Actual Picard obstruction under an elementary kernel subspace quotient -/

noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxRecDepth 2048
set_option maxHeartbeats 100000

namespace Langlands.AlgebraicGeometry.Picard.PicardGroupoid.ArtinianKernelQuotientObstruction

open Langlands.AlgebraicGeometry.Deformation
open Langlands.AlgebraicGeometry.Modules
open ArtinianTest ArtinianTest.ElementaryKernel
open ArtinianPicardObstructionFinite ArtinianKernelQuotient
open ArtinianKernelQuotientCohomology ArtinianKernelQuotientCohomologySupport
open StructureKernelModule

variable {k K : Type u} [CommRing k] [Field K] [Algebra k K]
  {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))
  {A B : ArtinianTest k K} (q : A ⟶ B)
  [he : Fact (IsElementarySurjection q)]

local notation "hq" => he.out
local instance : Module K (Kernel q) := ElementaryKernel.residueModule q hq
variable (W : Submodule K (Kernel q))

local notation "AQ" => ElementaryKernelSubspaceQuotient.test q W
local notation "π" => ElementaryKernelSubspaceQuotient.projection q W
local notation "r" => ElementaryKernelSubspaceQuotient.reduction q W
local notation "h" => CategoryTheory.Functor.map (relativeSpace f) (ArtinianTest.baseMap π)
local notation "j" => CategoryTheory.Functor.map (relativeSpace f) (ArtinianTest.baseMap r)
local notation "i" => CategoryTheory.Functor.map (relativeSpace f) (ArtinianTest.baseMap q)
local notation "pA" => NatTrans.app (relativeProjection f) (ArtinianTest.base A)
local notation "pQ" => NatTrans.app (relativeProjection f) (ArtinianTest.base AQ)
local notation "φ" => CommRingCat.ofHom (AlgHom.toRingHom (ArtinianTest.toAlgHom π))

local instance : Fact (IsElementarySurjection r) :=
  ⟨ElementaryKernelSubspaceQuotient.reduction_elementary q W⟩
local instance : IsClosedImmersion h :=
  ArtinianSquareZeroPicardLifting.relativeMap_isClosedImmersion f π
    (ElementaryKernelSubspaceQuotient.projection_elementary q W).1
local instance : IsClosedImmersion j :=
  ArtinianSquareZeroPicardLifting.relativeMap_isClosedImmersion f r
    (ElementaryKernelSubspaceQuotient.reduction_elementary q W).1
local instance : IsClosedImmersion i :=
  ArtinianSquareZeroPicardLifting.relativeMap_isClosedImmersion f q hq.1

attribute [local instance] ArtinianPicardObstructionFinite.sourceModule

omit he in
private lemma relativeEquiv_apply (n : ℕ) (x : Cohomology f q n) :
    relativeEquiv f q n x =
      (DerivedSections.relativeCohomologyRestrictScalarsIso pA n).hom.app
        (idealModule f q) x := rfl

variable [QuasiCompact f]
  (M : LineBundle ((relativeSpace f).obj (ArtinianTest.residueBase k K)))

private lemma obstruction_eq (L : ArtinianTestDeformations.Deformations f M B) :
    ArtinianSquareZeroPicardLifting.obstruction f M q hq L =
      SquareZeroPicardObstruction.obstructionMap i
        (ArtinianSquareZeroPicardLifting.relativeMap_ker_sq f q hq)
        L.right.of.classOf := rfl

/-- The canonical actual ideal-cohomology quotient takes the source Picard
obstruction to the actual target obstruction of the same pointed deformation. -/
lemma obstruction_quotient (L : ArtinianTestDeformations.Deformations f M B) :
    cohomologySemilinearMap f q W 2
      (ArtinianSquareZeroPicardLifting.obstruction f M q hq L) =
    ArtinianSquareZeroPicardLifting.obstruction f M r
      (ElementaryKernelSubspaceQuotient.reduction_elementary q W) L := by
  apply (relativeEquiv f r 2).injective
  change (relativeEquiv f r 2) ((relativeEquiv f r 2).symm
      (relativeCohomologyMap f q W 2
        (relativeEquiv f q 2 (ArtinianSquareZeroPicardLifting.obstruction f M q hq L)))) = _
  rw [LinearEquiv.apply_symm_apply, relativeCohomologyMap_eq]
  rw [idealMap_eq_kernelModuleMap, relativeEquiv_apply, relativeEquiv_apply,
    obstruction_eq, obstruction_eq]
  have hn := SquareZeroRelativeObstructionNaturality.obstructionMap_factorization
    h j ⟨2, ArtinianSquareZeroPicardLifting.relativeMap_ker_sq f π
      (ElementaryKernelSubspaceQuotient.projection_elementary q W)⟩
    φ pA pQ (projection_square f q W) (factorization f q W)
    (ArtinianSquareZeroPicardLifting.relativeMap_ker_sq f r
      (ElementaryKernelSubspaceQuotient.reduction_elementary q W))
    (ArtinianSquareZeroPicardLifting.relativeMap_ker_sq f q hq) L.right.of.classOf
  exact hn.symm


variable [Flat f] [IsProper f]
  {ι η : Type u} [Finite ι] [Finite η]
  (b : Module.Basis ι K (Kernel q))
  (e : Module.Basis η K (ArtinianResidueCohomology.ResidueCohomology (K := K) f 2))

/-- The coefficient subspace of the actual source Picard obstruction. -/
def obstructionCoefficientSubspace
    (L : ArtinianTestDeformations.Deformations f M B) : Submodule K (Kernel q) :=
  cohomologyCoefficientSubspace f q b 2 e
    (ArtinianSquareZeroPicardLifting.obstruction f M q hq L)

/-- The obstruction coefficient subspace is bounded by residue-fibre H². -/
lemma obstructionCoefficientSubspace_finrank_le
    (L : ArtinianTestDeformations.Deformations f M B) :
    Module.finrank K (obstructionCoefficientSubspace f q M b e L) ≤
      Module.finrank K (ArtinianResidueCohomology.ResidueCohomology (K := K) f 2) :=
  cohomologyCoefficientSubspace_finrank_le f q b 2 e _

/-- The actual quotient obstruction vanishes exactly when the quotient subspace
contains the coefficient subspace of the actual source obstruction. -/
lemma obstruction_quotient_eq_zero_iff
    (L : ArtinianTestDeformations.Deformations f M B) :
    ArtinianSquareZeroPicardLifting.obstruction f M r
        (ElementaryKernelSubspaceQuotient.reduction_elementary q W) L = 0 ↔
      obstructionCoefficientSubspace f q M b e L ≤ W := by
  rw [← obstruction_quotient f q W M L]
  exact cohomology_quotient_eq_zero_iff f q b 2 e W _

/-- The coefficient criterion gives actual pointed lifts over the quotient test. -/
theorem pointed_lift_quotient_iff
    (L : ArtinianTestDeformations.Deformations f M B) :
    (∃ N : ArtinianTestDeformations.Deformations f M AQ,
      Nonempty ((ArtinianTestDeformations.restrict f M r).obj N ≅ L)) ↔
      obstructionCoefficientSubspace f q M b e L ≤ W :=
  (ArtinianSquareZeroPicardLifting.pointed_lift_iff_obstruction f M r
    (ElementaryKernelSubspaceQuotient.reduction_elementary q W) L).trans
      (obstruction_quotient_eq_zero_iff f q W M b e L)

/-- Every pointed deformation lifts after quotienting an elementary kernel by a
subspace of dimension at most that of the residue fibre's structure H². -/
theorem exists_kernel_subspace_lift
    (L : ArtinianTestDeformations.Deformations f M B) :
    ∃ W' : Submodule K (Kernel q),
      Module.finrank K W' ≤
        Module.finrank K (ArtinianResidueCohomology.ResidueCohomology (K := K) f 2) ∧
      ∃ N : ArtinianTestDeformations.Deformations f M
          (ElementaryKernelSubspaceQuotient.test q W'),
        Nonempty ((ArtinianTestDeformations.restrict f M
          (ElementaryKernelSubspaceQuotient.reduction q W')).obj N ≅ L) := by
  let := ElementaryKernel.finiteDimensional q hq
  let := residueCohomology_finite (K := K) f 2
  let b' := Module.Free.chooseBasis K (Kernel q)
  let e' := Module.Free.chooseBasis K
    (ArtinianResidueCohomology.ResidueCohomology (K := K) f 2)
  let W' := obstructionCoefficientSubspace f q M b' e' L
  refine ⟨W', obstructionCoefficientSubspace_finrank_le f q M b' e' L, ?_⟩
  exact (pointed_lift_quotient_iff f q W' M b' e' L).mpr le_rfl

end Langlands.AlgebraicGeometry.Picard.PicardGroupoid.ArtinianKernelQuotientObstruction
