import Langlands.AlgebraicGeometry.Modules.SmoothProperLineBundleFiniteCohomologyStatement
import Langlands.AlgebraicGeometry.Modules.UniversalPerfectSectionsProof
import Langlands.AlgebraicGeometry.Picard.TensorRankOneProof
import Langlands.Cohomology.PerfectModuleComplexBaseChange

/-! # Finite line-bundle cohomology from an actual perfect representative -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.Modules

attribute [local instance] HasDerivedCategory.standard

/-- Actual smooth proper line-bundle cohomology is finite over the base field. -/
theorem smoothProperLineBundleFiniteCohomology :
    SmoothProperLineBundleFiniteCohomologyStatement.{u} := by
  intro K _ X f hs hp L
  let : (DerivedSections.relativeGlobalSections f).Additive :=
    (inferInstance : ∀ {R : CommRingCat.{u}} (g : X ⟶ Spec R),
      (DerivedSections.relativeGlobalSections g).Additive) f
  obtain ⟨C, hC, ⟨e⟩, _⟩ :=
    universalPerfectSections (CommRingCat.of K) X f hs hp L
  let eH (n : ℕ) : C.homology (n : ℤ) ≅
      (DerivedSections.relativeCohomology f n).obj L.obj :=
    Langlands.Cohomology.DerivedPlus.homologyIsoOfIsoDerivedComplex
      (D := ModuleCat.{u} K)
      (DerivedSections.relativeGlobalSections f) e n
  constructor
  · intro n
    let : Module.Finite K (C.X (n : ℤ)) := (hC.2 n).1
    let : Module.Finite K (C.homology (n : ℤ)) :=
      Langlands.Cohomology.ModuleComplex.finite_homology_of_finite_term C n
    exact Module.Finite.equiv (eH n).toLinearEquiv
  · obtain ⟨a, b, ha, hb⟩ := hC.1
    let : C.IsStrictlyLE b := hb
    refine ⟨b.toNat + 1, fun n hn => ?_⟩
    apply IsZero.of_iso (Y := C.homology (n : ℤ)) _ (eH n).symm
    apply ShortComplex.isZero_homology_of_isZero_X₂
    exact C.isZero_of_isStrictlyLE b n (by omega)

/-- Every actual nonnegative tensor power has finite cohomology, with no
ampleness hypothesis. -/
theorem smoothProperLineBundleTensorPowFiniteCohomology
    (K : Type u) [Field K] (X : Scheme.{u}) (f : X ⟶ Spec (CommRingCat.of K))
    (hs : Smooth f) (hp : IsProper f) (L : Picard.LineBundle X) (n : ℕ) :
    DerivedSections.HasFiniteCohomology f (Langlands.Scheme.Modules.tensorPow L.obj n) :=
  smoothProperLineBundleFiniteCohomology K X f hs hp
    ⟨Langlands.Scheme.Modules.tensorPow L.obj n, Picard.tensorPow_isLocallyFreeRankOne X L n⟩

end Langlands.AlgebraicGeometry.Modules
