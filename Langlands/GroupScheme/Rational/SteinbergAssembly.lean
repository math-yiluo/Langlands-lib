import Langlands.GroupScheme.CocycleRefinement
import Langlands.GroupScheme.Rational.QuasiSplitCocycleTorusReductionStatement
import Langlands.GroupScheme.Rational.QuasiSplitInnerFormExistenceStatement
import Langlands.GroupScheme.Rational.DimensionLEOneTorusCocycleVanishingStatement
import Langlands.GroupScheme.Rational.DimensionLEOneQuasiSplitStatement

/-! # Conditional assembly of the Steinberg quasi-splitness argument -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

namespace Cocycle.TorusReduction

variable {K : Type u} [Field K]
    {G : GroupScheme (Spec (CommRingCat.of K))}
    {U : Over (Spec (CommRingCat.of K))}
    {ξ : Cocycle G U} (d : ξ.TorusReduction)

/-- The actual torus-valued cocycle obtained from the all-test factorization. -/
def torusCocycle : Cocycle d.torus
    (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K d.carrier)))) := by
  letI : IsClosedImmersion d.inclusion.hom.hom.left := d.isClosedSubgroup
  letI : Mono d.inclusion.hom.hom := Over.mono_of_mono_left _
  exact ((ξ.refine d.refinement).twist d.cochain).lift d.inclusion d.factorization

include d in
/-- Torus-cocycle triviality implies triviality of a cocycle with an actual
finite-Galois torus reduction. -/
theorem isTrivial_of_hasTrivialTorusCocycles (hT : HasTrivialTorusCocycles K) :
    ξ.IsTrivial := by
  let : IsClosedImmersion d.inclusion.hom.hom.left := d.isClosedSubgroup
  let : Mono d.inclusion.hom.hom := Over.mono_of_mono_left _
  let : QuasiCompact d.refinement.left := d.quasiCompact_refinement
  let : Flat d.refinement.left := d.flat_refinement
  let : Surjective d.refinement.left := d.surjective_refinement
  have ht : d.torusCocycle.IsTrivial := hT d.torus d.isTorus d.carrier d.torusCocycle
  have hl : ((ξ.refine d.refinement).twist d.cochain).IsTrivial :=
    Cocycle.IsTrivial.of_lift ht
  exact (ξ.isTrivial_refine_iff d.refinement).mp hl.of_twist

end Cocycle.TorusReduction

/-- Under torus reduction, quasi-split semisimple-group cocycles vanish whenever
actual torus cocycles vanish. -/
theorem cocycle_isTrivial_of_torusReduction
    (hred : QuasiSplitCocycleTorusReductionStatement.{u})
    {K : Type u} [Field K] (hT : HasTrivialTorusCocycles K)
    (G : GroupScheme (Spec (CommRingCat.of K)))
    (hG : IsSemisimple G) (hqs : IsQuasiSplit G)
    (L : Type u) [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (ξ : Cocycle G (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K L))))) :
    ξ.IsTrivial := by
  obtain ⟨d⟩ := hred K G hG hqs L ξ
  exact d.isTrivial_of_hasTrivialTorusCocycles hT

/-- Actual inner forms and torus reduction give quasi-splitness over fields
whose actual torus cocycles vanish. -/
theorem isQuasiSplit_of_structural_inputs
    (hinner : QuasiSplitInnerFormExistenceStatement.{u})
    (hred : QuasiSplitCocycleTorusReductionStatement.{u})
    {K : Type u} [Field K] (hT : HasTrivialTorusCocycles K)
    (G : GroupScheme (Spec (CommRingCat.of K))) (hG : IsConnectedReductive G) :
    IsQuasiSplit G := by
  obtain ⟨d⟩ := hinner K G hG
  apply d.isQuasiSplit_of_isTrivial
  exact cocycle_isTrivial_of_torusReduction hred hT d.adjoint
    d.isAdjointQuotient.isAdjoint.isSemisimple d.isQuasiSplit_adjoint d.carrier d.cocycle

/-- The exact Steinberg target follows from the three named, still independent,
structural and torus-vanishing propositions. -/
theorem dimensionLEOneQuasiSplit_of_structural_inputs
    (hinner : QuasiSplitInnerFormExistenceStatement.{u})
    (hred : QuasiSplitCocycleTorusReductionStatement.{u})
    (htorus : DimensionLEOneTorusCocycleVanishingStatement.{u}) :
    DimensionLEOneQuasiSplitStatement.{u} := by
  intro K _ hK G hG
  exact isQuasiSplit_of_structural_inputs hinner hred (htorus K hK) G hG

end Langlands.GroupScheme
