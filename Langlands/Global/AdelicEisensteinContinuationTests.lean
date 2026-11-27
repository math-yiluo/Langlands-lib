import Langlands.Global.AdelicEisensteinContinuationComparison
import Langlands.Global.AdelicLeviConstantTermPairing

/-! # Norm-one Levi tests of a function-valued meromorphic continuation -/

universe u

open CategoryTheory AlgebraicGeometry Set
open scoped CategoryTheory.MonObj Manifold

set_option autoImplicit false

namespace Langlands.Global.StandardParabolicFamily

open Langlands.Analysis.Meromorphic Langlands.GroupScheme AdelicGroupPoints
  Langlands.Automorphic.GroupSchemeFunctions

variable {F : Type u} [Field F] [NumberField F]
  {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  (fam : StandardParabolicFamily F G)
  {N d : ℕ} (rho : MatrixRepresentation G (Fin N)) (hN : 0 < N) (hrho : IsClosedSubgroup rho)
  (hsmooth : SmoothOfRelativeDimension d G.X.hom) (hcalc : AdelicDifferentialCommutator F G hsmooth)
  (Kinf : Subgroup (InfiniteAdelicGroupPoints F G))

/-- Local function-valued meromorphic presentations in the uniform-growth spaces give one
open dense domain on which all point evaluations and all norm-one Levi tests of the
standard constant terms are scalar meromorphic, and on which the values are automorphic.
The tests are continuous on each growth stage by their integrable weighted majorants. -/
theorem exists_openDense_continuation_tests {n : ℕ} (E : (Fin n → ℂ) → AdelicGroupPoints F G → ℂ)
    (hmaj : ∀ (J : StandardIndex F G fam.i fam.ν) (ψ : AdelicGroupPoints F (fam.M J) → ℂ),
      fam.IsLeviCuspForm Kinf rho J ψ → ∀ g (R : ℝ), fam.HasLeviPairingMajorant J ψ g rho R)
    (hlocal : ∀ s₀ : Fin n → ℂ, ∃ W : TopologicalSpace.Opens (Fin n → ℂ), s₀ ∈ W ∧
      ∃ (R : ℝ) (L : Subgroup (FiniteAdelicGroupPoints F G)),
        IsOpen (L : Set (FiniteAdelicGroupPoints F G)) ∧
        ∃ (f : W → UniformGrowthFrechetSpace F G rho hsmooth hcalc hN hrho R L) (D : Set W),
          IsMeromorphicOn 𝓘(ℂ, Fin n → ℂ) f D ∧
          ∀ s ∈ D, UniformGrowthFrechetSpace.toFun F G rho hsmooth hcalc hN hrho R L (f s) =
              E s ∧
            IsAutomorphicFunctionOn F G hsmooth hcalc (rationalSubgroup F G) Kinf rho (E s)) :
    ∃ U : Set (Fin n → ℂ), IsOpen U ∧ Dense U ∧
      (∀ g, IsMeromorphicOn 𝓘(ℂ, Fin n → ℂ) (fun s => E s g) U) ∧
      (∀ s ∈ U, IsAutomorphicFunctionOn F G hsmooth hcalc (rationalSubgroup F G) Kinf rho (E s)) ∧
      (∀ (J : StandardIndex F G fam.i fam.ν) (ψ : AdelicGroupPoints F (fam.M J) → ℂ),
        fam.IsLeviCuspForm Kinf rho J ψ → ∀ g,
          IsMeromorphicOn 𝓘(ℂ, Fin n → ℂ)
            (fun s => fam.leviPairing J (fam.constantTerm J (E s)) g ψ) U) := by
  classical
  choose W hW R L _hL f D hf hE using hlocal
  let U : Set (Fin n → ℂ) := ⋃ s₀, Subtype.val '' D s₀
  have hm (g : AdelicGroupPoints F G) :
      IsMeromorphicOn 𝓘(ℂ, Fin n → ℂ) (fun s => E s g) U := by
    refine isMeromorphicOn_of_openCover W D (fun s => ⟨s, hW s⟩) ?_
    intro s₀
    let ev := UniformGrowthFrechetSpace.evaluation F G rho hsmooth hcalc hN hrho (R s₀) (L s₀) g
    exact ((hf s₀).comp_continuousLinearMap ev).congr_domain fun t ht =>
      (congrFun (hE s₀ t ht).1 g).symm
  refine ⟨U, (hm 1).1, (hm 1).2.1, hm, ?_, ?_⟩
  · intro s hs
    obtain ⟨s₀, t, ht, rfl⟩ := mem_iUnion.mp hs
    exact (hE s₀ t ht).2
  · intro J ψ hψ g
    refine isMeromorphicOn_of_openCover W D (fun s => ⟨s, hW s⟩) ?_
    intro s₀
    let test := fam.constantTermLeviPairingCLM J ψ hψ.1.1 g rho hN hrho hsmooth hcalc (R s₀)
      (L s₀) hψ.1.2.1.1 (hmaj J ψ hψ g (R s₀))
    refine ((hf s₀).comp_continuousLinearMap test).congr_domain fun t ht => ?_
    simp only [Function.comp_apply, test, constantTermLeviPairingCLM_apply, (hE s₀ t ht).1]

end Langlands.Global.StandardParabolicFamily
