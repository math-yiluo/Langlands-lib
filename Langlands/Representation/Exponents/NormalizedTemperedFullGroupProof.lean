import Langlands.Representation.Exponents.NormalizedTemperedFullGroupStatement
import Langlands.GroupScheme.Rational.CentralRootRestriction
import Langlands.Representation.Plancherel.SplitTorusNormFormula

/-! # Unitarity of full-group normalized exponents

For an identity parabolic and Levi, all roots restrict to zero on the central
split component. The actual root-combination cone is therefore `{0}`.
-/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry TensorProduct
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.ParabolicRootPresentation

variable {k : Type u} [Field k]
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom]
  {A : CommGroupScheme (Spec (CommRingCat.of k))} {a : A.toGrp ⟶ G}

/-- Every restricted root of an identity presentation is zero, since its factor
through the ambient torus is the central split-component map. -/
theorem restrictedRoot_eq_zero_identity
    (pres : ParabolicRootPresentation (𝟙 G) (𝟙 G) a)
    {β : RealTorusSpace.Vstar A} (hβ : β ∈ pres.restrictedRoots) : β = 0 := by
  obtain ⟨α, hα, _, rfl⟩ := pres.mem_restrictedRoots.mp hβ
  have hc : IsCentral (CommGroupScheme.groupHom pres.data.f ≫ pres.data.i) := by
    rw [pres.isCompatible.factor_comp, Category.comp_id, Category.comp_id]
    exact pres.isCompatible.splitComponent.isCentralSplitTorus.isCentral
  rw [root_restrict_eq_zero_of_isCentral pres.data.i pres.data.f
    pres.isCompatible.splitComponent.isCentralSplitTorus.1.1 hc hα.1.1,
    TensorProduct.tmul_zero]

/-- The full-group nonnegative root-combination cone is `{0}` in the entire
real character space, including its central directions. -/
theorem nonnegCone_identity
    (pres : ParabolicRootPresentation (𝟙 G) (𝟙 G) a) : pres.nonnegCone = {0} := by
  ext x
  constructor
  · intro hx
    change x ∈ RootCombination.nonneg pres.restrictedRoots pres.finite_restrictedRoots at hx
    obtain ⟨c, _, hc⟩ := hx
    apply Set.mem_singleton_iff.mpr
    rw [← hc]
    apply Finset.sum_eq_zero
    intro β hβ
    rw [pres.restrictedRoot_eq_zero_identity
      (pres.finite_restrictedRoots.mem_toFinset.mp hβ), smul_zero]
  · intro hx
    exact (Set.mem_singleton_iff.mp hx) ▸ pres.zero_mem_nonnegCone

end Langlands.GroupScheme.ParabolicRootPresentation

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme

/-- Every actual full-group normalized Jacquet exponent of a normalized-exponent
tempered representation has zero normalized real part and is pointwise unitary. -/
theorem normalizedTemperedFullGroupExponent :
    NormalizedTemperedFullGroupExponentStatement.{u, v} := by
  intro k _ _ _ _ _ G hG
  have := hG.isAffineHom
  let : TopologicalSpace (rationalPoints G) := RationalPointFamily.pointTopology
  intro _ _ π A a hp hl ha U r hr hmul χ hπ hχ
  have := hG.smooth
  have hcone := hπ.parabolic (𝟙 G) (𝟙 G) a hp hl ha
  obtain ⟨pres⟩ := hcone.1
  have hmem := hcone.2 pres U r hr hmul χ hχ
  have hzero : Plancherel.SplitTorus.normalizedRealPart ha.isCentralSplitTorus.1.1 χ = 0 := by
    simpa only [pres.nonnegCone_identity, Set.mem_singleton_iff] using hmem
  refine ⟨hzero, ?_⟩
  have := ha.isAffine
  exact (Plancherel.SplitTorus.normalizedRealPart_eq_zero_iff
    ha.isCentralSplitTorus.1.1 χ hχ.1).mp hzero

end Langlands.Aubert.General.RepresentedParabolic
