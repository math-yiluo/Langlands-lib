import Langlands.GroupScheme.Rational.SemigroupWeightSupport

/-! # Intrinsic weights under surjective equivariant Lie maps -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.RelativeRoot

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

variable {k : Type u} [Field k]
    {S : CommGroupScheme (Spec (CommRingCat.of k))}
    {H G : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom H.X.hom] [IsAffineHom G.X.hom]
    [LocallyOfFiniteType H.X.hom] [LocallyOfFiniteType G.X.hom]
    (b : AutomorphicAction S.toGrp H) (d : AutomorphicAction S.toGrp G)
    (hS : IsSplitTorus S.toGrp) (q : H ⟶ G)
    (hqd : ∀ (T : Over (Spec (CommRingCat.of k))) (s : T ⟶ S.X) (x : T ⟶ H.X),
      b.act s x ≫ q.hom.hom = d.act s (x ≫ q.hom.hom))
    (hq : Function.Surjective (Lie.targetMapLinear q k))

include hS hqd hq

/-- A surjective equivariant differential maps each intrinsic character weight
space onto the corresponding target weight space. -/
theorem map_actionWeightSpace_eq_of_surjective (χ : characterLattice S) :
    (actionWeightSpace b χ).map (Lie.targetMapLinear q k) = actionWeightSpace d χ := by
  have htop : (⨆ ψ, (actionWeightSpace b ψ).map (Lie.targetMapLinear q k)) = ⊤ := by
    rw [← Submodule.map_iSup, iSup_actionWeightSpace_eq_top b hS,
      Submodule.map_top, LinearMap.range_eq_top.mpr hq]
  have hle : (fun ψ => (actionWeightSpace b ψ).map (Lie.targetMapLinear q k)) ≤
      actionWeightSpace d := by
    intro ψ X hX
    obtain ⟨Y, hY, rfl⟩ := hX
    exact lieKernelTargetLinear_mem_actionWeightSpace d b q hqd ψ hY
  have heq := ((iSupIndep_actionWeightSpace d hS).le_iff_eq_of_iSup_eq_top htop).mp hle
  exact congrFun heq χ

/-- Restriction of a surjective equivariant differential to each character
weight space is surjective. -/
theorem actionWeightSpaceMap_surjective (χ : characterLattice S) :
    Function.Surjective (actionWeightSpaceMap d b q hqd χ) := by
  intro Y
  have hY : (Y : Additive (lieKernel G k)) ∈
      (actionWeightSpace b χ).map (Lie.targetMapLinear q k) := by
    rw [map_actionWeightSpace_eq_of_surjective b d hS q hqd hq χ]
    exact Y.property
  obtain ⟨X, hX, hXY⟩ := hY
  exact ⟨⟨X, hX⟩, Subtype.ext hXY⟩

/-- Each target weight space is the source weight space modulo the kernel of
the restricted differential. -/
def actionWeightSpaceQuotientEquiv (χ : characterLattice S) :
    ((actionWeightSpace b χ) ⧸ LinearMap.ker (actionWeightSpaceMap d b q hqd χ)) ≃ₗ[k]
      actionWeightSpace d χ :=
  LinearMap.quotKerEquivOfSurjective _
    (actionWeightSpaceMap_surjective b d hS q hqd hq χ)

/-- Absence of any source character weight descends along a surjective
equivariant differential, including absence of the zero character. -/
theorem actionWeightSpace_eq_bot_of_surjective (χ : characterLattice S)
    (hχ : actionWeightSpace b χ = ⊥) : actionWeightSpace d χ = ⊥ := by
  rw [← map_actionWeightSpace_eq_of_surjective b d hS q hqd hq χ, hχ,
    Submodule.map_bot]

/-- A surjective equivariant differential also maps each full semigroup
weight span onto the corresponding target span. -/
theorem map_semigroupWeightSpan_eq_of_surjective
    (A : AddSubsemigroup (characterLattice S)) :
    (semigroupWeightSpan b A).map (Lie.targetMapLinear q k) =
      semigroupWeightSpan d A := by
  simp only [semigroupWeightSpan, Submodule.map_iSup,
    map_actionWeightSpace_eq_of_surjective b d hS q hqd hq]

end Langlands.GroupScheme.RelativeRoot
