import Langlands.Global.AdelicConvergentCuspidalTestExpansionStatement

/-! # Standard presentations of a parabolic family and twisted intertwining integrals -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option autoImplicit false

namespace Langlands.Global.StandardParabolicFamily

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions AdelicGroupPoints

variable {F : Type u} [Field F] [NumberField F]
  {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  (fam : StandardParabolicFamily F G)

/-- The root presentation of a standard parabolic of the family. -/
abbrev standardPresentation (J : StandardIndex F G fam.i fam.ν) :
    ParabolicRootPresentation (fam.p J) (fam.l J) (fam.a J) :=
  ⟨⟨fam.T, fam.i, fam.ν, J.val, fam.f J⟩, fam.isCompatible J⟩

omit [NumberField F] in
theorem isSplitTorus_splitComponent (J : StandardIndex F G fam.i fam.ν) :
    IsSplitTorus (fam.A J).toGrp :=
  (fam.isCompatible J).splitComponent.isCentralSplitTorus.1.1

omit [NumberField F] in
theorem isSplitTorus_torus : IsSplitTorus fam.T.toGrp :=
  fam.maximalSplit.isSplitSubtorus.1

/-- The intertwining integral is the twist by `wλ` of the intertwining operator. -/
theorem intertwiningIntegral_eq_parameterTwist {I Q : StandardIndex F G fam.i fam.ν}
    [IsClosedImmersion (fam.p I).hom.hom.left] [IsClosedImmersion (fam.p Q).hom.hom.left]
    {K : Subgroup (AdelicGroupPoints F G)}
    (hKI : IsIwasawaCompact (fam.p I) K) (hKQ : IsIwasawaCompact (fam.p Q) K)
    (c : fam.M Q ⟶ fam.M I) (proj : fam.P Q ⟶ fam.M Q)
    (w : Over.mk (𝟙 (Spec (CommRingCat.of F))) ⟶ G.X) (φ : AdelicGroupPoints F G → ℂ)
    (lam : ComplexCharacterParameter F (fam.P I)) :
    hKI.intertwiningIntegral (fam.iU I) (fam.iU Q ≫ fam.p Q) w φ lam =
      hKQ.parameterTwist (hKI.intertwiningOperator hKQ (fam.iU I) (fam.l I) (fam.iU Q) c proj w φ
        lam) (weylParameter (fam.l I) c proj lam) := by
  funext g
  simp only [IsIwasawaCompact.parameterTwist, IsIwasawaCompact.intertwiningOperator,
    IsIwasawaCompact.heightPower, map_neg, LinearMap.neg_apply, Complex.exp_neg]
  rw [mul_comm, ← mul_assoc, mul_inv_cancel₀ (Complex.exp_ne_zero _), one_mul]

end Langlands.Global.StandardParabolicFamily
