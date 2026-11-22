import Langlands.Global.AdelicEisensteinContinuationStatement
import Langlands.Global.AdelicEisensteinRegularRegion
import Langlands.Automorphic.GroupSchemeUniformGrowthEvaluation
import Langlands.Analysis.Meromorphic.LocalScalarMeromorphy

/-! # Comparison of pointwise and function-valued Eisenstein continuations -/

universe u

open CategoryTheory AlgebraicGeometry Set
open scoped CategoryTheory.MonObj Manifold

set_option autoImplicit false

namespace Langlands.Global

open Langlands.Analysis.Meromorphic Langlands.GroupScheme AdelicGroupPoints
  Langlands.Automorphic.GroupSchemeFunctions

variable {F : Type u} [Field F] [NumberField F]
  {G P M : GroupScheme (Spec (CommRingCat.of F))}
  {A : CommGroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  {p : P ⟶ G} {l : M ⟶ P} {a : A.toGrp ⟶ M} (r : ParabolicRootPresentation p l a)
  [Mono r.data.i.hom.hom.left] [Fintype (relativeWeylGroup r.data.i)]
  [Mono (CommGroupScheme.groupHom r.data.f).hom.hom.left]
  (hA : IsSplitTorus A.toGrp) (hT : IsSplitTorus r.data.T.toGrp)
  {N d : ℕ} (rho : MatrixRepresentation G (Fin N)) (hN : 0 < N) (hrho : IsClosedSubgroup rho)
  (hsmooth : SmoothOfRelativeDimension d G.X.hom) (hcalc : AdelicDifferentialCommutator F G hsmooth)
  {K : Subgroup (AdelicGroupPoints F G)}
  {EP EC : ComplexCharacterParameter F P → AdelicGroupPoints F G → ℂ}
  {DP : Set (ComplexCharacterParameter F P)}
  {n : ℕ} (e : (Fin n → ℂ) ≃ₗ[ℂ] ComplexCharacterParameter F P)

/-- Locally function-valued continuation yields a common open dense scalar
holomorphy domain, with the same automorphy assertion and equality to the
given pointwise continuation. -/
theorem exists_openDense_eisensteinContinuation_eqOn
    (hEP : ∀ g, IsMeromorphicInCoordinatesOn (fun lam => EP lam g) DP)
    (hagree : ∃ R : ℝ, ∀ lam, r.IsRegularParameter hA hT R lam → EP lam = EC lam)
    (hlocal : ∀ s₀ : Fin n → ℂ, ∃ W : TopologicalSpace.Opens (Fin n → ℂ), s₀ ∈ W ∧
      ∃ (R : ℝ) (L : Subgroup (FiniteAdelicGroupPoints F G)),
        IsOpen (L : Set (FiniteAdelicGroupPoints F G)) ∧
        ∃ (f : W → UniformGrowthFrechetSpace F G rho hsmooth hcalc hN hrho R L) (D : Set W),
          IsMeromorphicOn 𝓘(ℂ, Fin n → ℂ) f D ∧
          ∀ s ∈ D, UniformGrowthFrechetSpace.toFun F G rho hsmooth hcalc hN hrho R L (f s) =
              EC (e s) ∧
            IsAutomorphicFunctionOn F G hsmooth hcalc (rationalSubgroup F G)
              (K.comap (ofInfinite F G).toMonoidHom) rho (EC (e s))) :
    ∃ U : Set (Fin n → ℂ), IsOpen U ∧ Dense U ∧
      (∀ g, IsMeromorphicOn 𝓘(ℂ, Fin n → ℂ) (fun s => EC (e s) g) U) ∧
      (∀ s ∈ U, IsAutomorphicFunctionOn F G hsmooth hcalc (rationalSubgroup F G)
        (K.comap (ofInfinite F G).toMonoidHom) rho (EC (e s))) ∧
      EqOn (EP ∘ e) (EC ∘ e) ((e ⁻¹' DP) ∩ U) := by
  classical
  choose W hW R L _hL f D hf hEC using hlocal
  let U : Set (Fin n → ℂ) := ⋃ s₀, Subtype.val '' D s₀
  have hm (g : AdelicGroupPoints F G) :
      IsMeromorphicOn 𝓘(ℂ, Fin n → ℂ) (fun s => EC (e s) g) U := by
    refine isMeromorphicOn_of_openCover W D (fun s => ⟨s, hW s⟩) ?_
    intro s₀
    let ev := UniformGrowthFrechetSpace.evaluation F G rho hsmooth hcalc hN hrho (R s₀) (L s₀) g
    exact ((hf s₀).comp_continuousLinearMap ev).congr_domain fun t ht =>
      (congrFun (hEC s₀ t ht).1 g).symm
  refine ⟨U, (hm 1).1, (hm 1).2.1, hm, ?_, ?_⟩
  · intro s hs
    obtain ⟨s₀, t, ht, rfl⟩ := mem_iUnion.mp hs
    exact (hEC s₀ t ht).2
  · obtain ⟨R₀, hR₀⟩ := hagree
    intro s hs
    funext g
    have heq := ((hEP g).2 n e).eqOn_of_eqOn_open (hm g)
      (r.isOpen_regularParameter_inCoordinates hA hT R₀ e)
      (r.nonempty_regularParameter_inCoordinates hA hT R₀ e)
      (fun t ht => congrFun (hR₀ (e t) ht.1) g)
    exact heq hs

end Langlands.Global
