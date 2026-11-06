import Langlands.AlgebraicGeometry.Deformation.ElementarySourceExtension
import Langlands.AlgebraicGeometry.Picard.ArtinianKernelQuotientObstruction

/-! # Actual Picard families over successive quotients of one local source -/

noncomputable section
universe u
open CategoryTheory AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000

namespace Langlands.AlgebraicGeometry.Picard.PicardGroupoid.ArtinianPicardSourceStep

open Langlands.AlgebraicGeometry.Deformation
open ArtinianTest ArtinianTest.ElementaryKernel
open ArtinianKernelQuotientObstruction ArtinianKernelQuotientCohomologySupport

variable {k K R : Type u} [CommRing k] [Field K] [Algebra k K]
  [CommRing R] [Algebra k R] [IsLocalRing R] [IsNoetherianRing R]
  (ε : R →ₐ[k] K) (hε : Function.Surjective ε)
  {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))
  (M : LineBundle ((relativeSpace f).obj (ArtinianTest.residueBase k K)))

/-- An actual pointed family with a surjective presentation from the fixed source. -/
structure Stage where
  test : ArtinianTest k K
  cover : R →ₐ[k] test.algebra
  cover_surjective : Function.Surjective cover
  augmentation_cover : test.augmentation.comp cover = ε
  family : ArtinianTestDeformations.Deformations f M test

namespace Stage

private def transitionCongr {A B : ArtinianTest k K} (q r : A ⟶ B)
    (w : q = r) (N N' : ArtinianTestDeformations.Deformations f M A) (hN : N = N')
    (L : ArtinianTestDeformations.Deformations f M B)
    (e : (ArtinianTestDeformations.restrict f M r).obj N' ≅ L) :
    (ArtinianTestDeformations.restrict f M q).obj N ≅ L :=
  eqToIso (congrArg (ArtinianTestDeformations.restrict f M q).obj hN) ≪≫
    eqToIso (congrArg (fun a => (ArtinianTestDeformations.restrict f M a).obj N') w) ≪≫ e

variable (s : Stage ε f M)

/-- The actual equation ideal of this source presentation. -/
abbrev equations : Ideal R := RingHom.ker s.cover.toRingHom

/-- The actual elementary source extension before imposing the obstruction. -/
abbrev sourceTest : ArtinianTest k K :=
  ElementarySourceExtension.test ε hε s.test s.cover s.augmentation_cover

/-- The actual quotient from the fixed local source onto the elementary extension. -/
abbrev sourceProjection : R →ₐ[k] (s.sourceTest ε hε f M).algebra :=
  ElementarySourceExtension.projection ε hε s.test s.cover s.augmentation_cover

/-- The elementary source extension maps to the original test. -/
abbrev sourceReduction : s.sourceTest ε hε f M ⟶ s.test :=
  ElementarySourceExtension.reduction ε hε s.test s.cover s.augmentation_cover

local notation "q" => s.sourceReduction ε hε f M

local instance : Fact (IsElementarySurjection q) :=
  ⟨ElementarySourceExtension.reduction_elementary ε hε s.test s.cover
    s.augmentation_cover s.cover_surjective⟩

local instance : Module K (Kernel q) :=
  ElementaryKernel.residueModule q (Fact.out : IsElementarySurjection q)

local instance : FiniteDimensional K (Kernel q) :=
  ElementaryKernel.finiteDimensional q (Fact.out : IsElementarySurjection q)

variable [Flat f] [IsProper f]

local instance : Module.Finite K (ArtinianResidueCohomology.ResidueCohomology (K := K) f 2) :=
  residueCohomology_finite f 2

/-- The actual obstruction coefficient subspace for the canonical elementary extension. -/
def obstructionSubspace : Submodule K (Kernel q) :=
  obstructionCoefficientSubspace f q M
    (Module.Free.chooseBasis K (Kernel q))
    (Module.Free.chooseBasis K (ArtinianResidueCohomology.ResidueCohomology (K := K) f 2))
    s.family

lemma obstructionSubspace_finrank_le :
    Module.finrank K (s.obstructionSubspace ε hε f M) ≤
      Module.finrank K (ArtinianResidueCohomology.ResidueCohomology (K := K) f 2) :=
  obstructionCoefficientSubspace_finrank_le f q M _ _ s.family

/-- This is the least kernel subspace whose actual quotient admits a pointed lift. -/
lemma quotient_lift_iff (W : Submodule K (Kernel q)) :
    (∃ N : ArtinianTestDeformations.Deformations f M
        (ElementaryKernelSubspaceQuotient.test q W),
      Nonempty ((ArtinianTestDeformations.restrict f M
        (ElementaryKernelSubspaceQuotient.reduction q W)).obj N ≅ s.family)) ↔
      s.obstructionSubspace ε hε f M ≤ W :=
  pointed_lift_quotient_iff f q W M _ _ s.family

local notation "W₀" => s.obstructionSubspace ε hε f M
local notation "Q" => ElementaryKernelSubspaceQuotient.test q W₀
local notation "π" => ElementaryKernelSubspaceQuotient.projection q W₀
local notation "r" => ElementaryKernelSubspaceQuotient.reduction q W₀

private def liftData : Σ N : ArtinianTestDeformations.Deformations f M Q,
    (ArtinianTestDeformations.restrict f M r).obj N ≅ s.family :=
  Classical.choice (by
    obtain ⟨N, ⟨e⟩⟩ := (s.quotient_lift_iff ε hε f M W₀).mpr le_rfl
    exact ⟨⟨N, e⟩⟩)

/-- The actual next pointed family over the obstruction-minimal quotient source. -/
def next : Stage ε f M where
  test := Q
  cover := (ArtinianTest.toAlgHom π).comp (s.sourceProjection ε hε f M)
  cover_surjective := (ElementaryKernelSubspaceQuotient.projection_elementary q W₀).1.comp
    (ElementarySourceExtension.projection_surjective ε hε s.test s.cover s.augmentation_cover)
  augmentation_cover := by
    rw [← AlgHom.comp_assoc, ArtinianTest.augmentation_comp,
      ElementarySourceExtension.augmentation_projection]
  family := (s.liftData ε hε f M).1

/-- The actual elementary arrow between consecutive family stages. -/
def reduction : (s.next ε hε f M).test ⟶ s.test := r

lemma reduction_elementary : IsElementarySurjection (s.reduction ε hε f M) :=
  ElementaryKernelSubspaceQuotient.reduction_elementary q W₀

/-- The original fixed-source presentation is retained exactly after reduction. -/
lemma reduction_cover :
    (ArtinianTest.toAlgHom (s.reduction ε hε f M)).comp (s.next ε hε f M).cover =
      s.cover := by
  change ((ArtinianTest.toAlgHom r).comp (ArtinianTest.toAlgHom π)).comp
    (s.sourceProjection ε hε f M) = s.cover
  rw [← ArtinianTest.toAlgHom_comp, ElementaryKernelSubspaceQuotient.projection_reduction]
  exact ElementarySourceExtension.reduction_projection ε hε s.test s.cover s.augmentation_cover

private lemma reduction_eq :
    @Eq (Q ⟶ s.test) (s.reduction ε hε f M) r := rfl

private lemma next_family :
    @Eq (ArtinianTestDeformations.Deformations f M Q)
      (s.next ε hε f M).family (s.liftData ε hε f M).1 := rfl

/-- The next family restricts to the original family with its full residue data. -/
def transition :
    (ArtinianTestDeformations.restrict (A := Q) f M (s.reduction ε hε f M)).obj
      (s.next ε hε f M).family ≅ s.family :=
  transitionCongr (A := Q) (B := s.test) f M (s.reduction ε hε f M) r (s.reduction_eq ε hε f M)
    (s.next ε hε f M).family (s.liftData ε hε f M).1 (s.next_family ε hε f M)
    s.family (s.liftData ε hε f M).2

/-- Multiplying every old equation by the maximal ideal still gives a next-stage equation. -/
lemma maximalIdeal_mul_equations_le :
    IsLocalRing.maximalIdeal R * s.equations ε f M ≤
      (s.next ε hε f M).equations ε f M := by
  intro a ha
  have hp : s.sourceProjection ε hε f M a = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr ha
  change ArtinianTest.toAlgHom π (s.sourceProjection ε hε f M a) = 0
  rw [hp, map_zero]

/-- The next equation ideal is contained in the original equation ideal. -/
lemma next_equations_le :
    (s.next ε hε f M).equations ε f M ≤ s.equations ε f M := by
  intro a ha
  have ha' : (s.next ε hε f M).cover a = 0 := ha
  exact (DFunLike.congr_fun (s.reduction_cover ε hε f M) a).symm.trans
    ((congrArg (ArtinianTest.toAlgHom (s.reduction ε hε f M)) ha').trans (map_zero _))

end Stage
end Langlands.AlgebraicGeometry.Picard.PicardGroupoid.ArtinianPicardSourceStep
