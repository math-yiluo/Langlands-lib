import Langlands.GroupScheme.CentralIsogeny.BaseChangeStatement

/-! # Base-change stability of central isogenies -/

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {S S' : Scheme.{u}} (b : S' ⟶ S)
variable {G H : GroupScheme S}

/-- Every point of a pulled-back central homomorphism remains central after every restriction. -/
theorem IsCentral.baseChange {i : H ⟶ G} (hi : IsCentral i) :
    IsCentral ((GroupScheme.baseChange b).map i) := by
  intro T x
  apply mem_center.mpr
  intro T' a y
  change (a ≫ (x ≫ ((GroupScheme.baseChange b).map i).hom.hom)) * y =
    y * (a ≫ (x ≫ ((GroupScheme.baseChange b).map i).hom.hom))
  apply (baseChangePointsEquiv b G T').injective
  rw [map_mul, map_mul, baseChangePointsEquiv_naturality, baseChangePointsEquiv_comp]
  exact (hi ((Over.map b).obj T) (baseChangePointsEquiv b H T x)
    ((Over.map b).obj T') ((Over.map b).map a) (baseChangePointsEquiv b G T' y)).eq

/-- Centrality of the full kernel is preserved using the canonical kernel comparison. -/
theorem IsCentralIsogeny.baseChange {f : G ⟶ H} (hf : IsCentralIsogeny f) :
    IsCentralIsogeny ((GroupScheme.baseChange b).map f) := by
  refine ⟨hf.isIsogeny.baseChange b, ?_, ?_⟩
  · exact MorphismProperty.overPullbackMap (P := @LocallyOfFinitePresentation)
      b f.hom.hom hf.locallyOfFinitePresentation
  · have hc := (hf.isCentral_kernelι.baseChange b).comp (kernelBaseChangeIso b f).inv
    simpa only [kernelBaseChangeIso_inv_ι] using hc

/-- Central isogenies are stable under every morphism of base schemes. -/
theorem centralIsogenyBaseChange : CentralIsogenyBaseChangeStatement.{u} :=
  fun _ _ b _ _ _ hf => hf.baseChange b

end Langlands.GroupScheme
