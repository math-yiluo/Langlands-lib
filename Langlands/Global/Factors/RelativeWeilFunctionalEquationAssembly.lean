import Langlands.Global.Factors.RelativeWeilLocalHecke
import Langlands.Global.Factors.RelativeWeilAssemblyExceptional
import Langlands.Global.Factors.HeckeFunctionalEquationProof
import Langlands.Global.Factors.HeckeFiniteRamification
import Langlands.VirtualRepresentation.Global.RelativeWeilInductionGenerationProof
import Langlands.VirtualRepresentation.Global.RelativeWeilLocalRestrictionProof
import Langlands.ClassField.Global.RelativeWeilCharacterFactorization
import Langlands.ClassField.Global.RelativeWeilTransferNormProof
import Langlands.ClassFieldTheory.Local.CommonClosureGeometricProof

/-!
# Assembly of the global functional equation for twisted relative Weil pairs

The global functional equation `RelativeWeilTwistFunctionalEquationStatement`, assuming the
transfer reciprocity of local relative Weil maps (`LocalTransferReciprocityStatement`).
-/

noncomputable section

set_option autoImplicit false

universe u uV uE uG uW

namespace Langlands.FiniteRepresentation

variable {G : Type uG} [Group G]

/-- Tensoring with the lifted trivial character line changes nothing but the carrier
universe. -/
def tensorTrivialLineEquiv (A : FiniteRepresentation.{0, uG, uV} ℂ G) :
    Equiv (tensor A (characterLine.{uG, uW} (1 : G →* ℂˣ))) A where
  toLinearEquiv := (TensorProduct.congr (LinearEquiv.refl ℂ A)
    (ULift.moduleEquiv : ULift.{uW} ℂ ≃ₗ[ℂ] ℂ)).trans (TensorProduct.rid ℂ A)
  isIntertwining' g := by
    apply TensorProduct.ext'
    intro x y
    change (((1 : G →* ℂˣ) g : ℂ) * y.down) • A.representation g x =
      A.representation g (y.down • x)
    simp [map_smul]

end Langlands.FiniteRepresentation

namespace Langlands.Global.FunctionalEquationComparison.RelativeWeilEngine

open NumberField IsDedekindDomain
open scoped NumberField
open Langlands.Global Langlands.Global.HeckeFunctionalEquation Langlands.Global.AdelicFunctoriality

variable {F : Type u} [Field F] [NumberField F]

/-- The target conclusion for the product of Hecke packages of a Brauer decomposition. Let
`f` be finite factors that agree with the factors of the product package wherever the Hecke
L-factors involved are nonzero, with epsilon factors equal to those of the package, and with
nonzero meromorphic epsilon factors on `B`. Then, for the archimedean block concentrated at
`w₀`, the partial L-functions outside `B` and the infinite places converge as Euler products,
and the completed functional equation holds with all epsilon factors in the exceptional set. -/
theorem exists_functionalEquation_of_heckeFactors
    (hH : HeckeGlobalFunctionalEquationStatement.{u})
    {E : Type u} [Field E] [NumberField E] [Algebra F E]
    (ψ : HarmonicAnalysis.UnitaryAdditiveCharacter (Adeles F))
    (hψ1 : ∃ x : Adeles F, ψ x ≠ 1) (hψ : ∀ x : F, ψ (diagonal F x) = 1)
    (ψf : ∀ v : FinitePlace F,
      @HarmonicAnalysis.UnitaryAdditiveCharacter (CompletionPadic.padicField v).Carrier _
        (CompletionPadic.topologicalData v).topology)
    (hψf : ∀ v, IsFiniteAdditiveComponent ψ v (ψf v))
    (μ : ∀ v : FinitePlace F,
      LocalFactor.PadicAbelian.SelfDualHaar (CompletionPadic.topologicalData v) (ψf v))
    (d : ℤ) (χ : HeckeCharacter F) (DF : HeckeArchData χ ψ)
    {n : ℕ} (r : Fin n → ℤ) (K : Fin n → IntermediateField F E)
    (lam lam' : ∀ i, HeckeCharacter (K i))
    (μK : ∀ i (u : FinitePlace (K i)),
      LocalFactor.PadicAbelian.SelfDualHaar (CompletionPadic.topologicalData u)
        (traceComponents ψf u))
    (DK : ∀ i, HeckeArchData (lam i) (traceAdditiveCharacter (L := K i) ψ hψ))
    (DK' : ∀ i, HeckeArchData (lam' i) (traceAdditiveCharacter (L := K i) ψ hψ))
    (B : Finset (FinitePlace F))
    (hBF : ∀ z ∉ B, ∀ s : ℂ, finiteEpsilon χ ψf μ z s = 1)
    (hBK : ∀ i, ∀ z ∉ B, ∀ u ∈ placesAbove (K i) z, ∀ s : ℂ,
      finiteEpsilon (lam i) (traceComponents ψf) (μK i) u s = 1)
    (hBK' : ∀ i, ∀ z ∉ B, ∀ u ∈ placesAbove (K i) z, ∀ s : ℂ,
      finiteEpsilon (lam' i) (traceComponents ψf) (μK i) u s = 1)
    [DecidableEq (InfinitePlace F)] [DecidableEq (AllPlaces F)] (w₀ : InfinitePlace F)
    (f : FinitePlace F → LocalFactors)
    (hL : ∀ z s, heckeL χ z s ≠ 0 → (∀ i, ∀ u ∈ placesAbove (K i) z,
        heckeL (lam i) u s ≠ 0 ∧ heckeL (lam' i) u s ≠ 0) →
      (f z).lFactor s = heckeL χ z s ^ d *
        ∏ i, ((∏ u ∈ placesAbove (K i) z, heckeL (lam i) u s) *
          (∏ u ∈ placesAbove (K i) z, heckeL (lam' i) u s)⁻¹) ^ r i)
    (hLd : ∀ z s, heckeL χ⁻¹ z s ≠ 0 → (∀ i, ∀ u ∈ placesAbove (K i) z,
        heckeL (lam i)⁻¹ u s ≠ 0 ∧ heckeL (lam' i)⁻¹ u s ≠ 0) →
      (f z).dualLFactor s = heckeL χ⁻¹ z s ^ d *
        ∏ i, ((∏ u ∈ placesAbove (K i) z, heckeL (lam i)⁻¹ u s) *
          (∏ u ∈ placesAbove (K i) z, heckeL (lam' i)⁻¹ u s)⁻¹) ^ r i)
    (hε : ∀ z s, (f z).epsilonFactor s = finiteEpsilon χ ψf μ z s ^ d *
        ∏ i, ((∏ u ∈ placesAbove (K i) z, finiteEpsilon (lam i) (traceComponents ψf) (μK i) u s) *
          (∏ u ∈ placesAbove (K i) z,
            finiteEpsilon (lam' i) (traceComponents ψf) (μK i) u s)⁻¹) ^ r i)
    (hεnm : ∀ z ∈ B, NonzeroMeromorphic (f z).epsilonFactor) :
    ∃ (σ : ℝ) (Lp Lpd : ℂ → ℂ),
      Admissible (assembledEulerData
        (lumpedArch w₀ (fun s => DF.A s ^ d * ∏ i, ((DK i).A s * ((DK' i).A s)⁻¹) ^ r i)
          (fun s => DF.Ad s ^ d * ∏ i, ((DK i).Ad s * ((DK' i).Ad s)⁻¹) ^ r i)
          (fun s => DF.Ae s ^ d * ∏ i, ((DK i).Ae s * ((DK' i).Ae s)⁻¹) ^ r i)) f Lp Lpd)
        (exceptionalPlaces F B) ∧
      HasEulerProductsOutside (assembledEulerData
        (lumpedArch w₀ (fun s => DF.A s ^ d * ∏ i, ((DK i).A s * ((DK' i).A s)⁻¹) ^ r i)
          (fun s => DF.Ad s ^ d * ∏ i, ((DK i).Ad s * ((DK' i).Ad s)⁻¹) ^ r i)
          (fun s => DF.Ae s ^ d * ∏ i, ((DK i).Ae s * ((DK' i).Ae s)⁻¹) ^ r i)) f Lp Lpd)
        (exceptionalPlaces F B) σ ∧
      FunctionalEquation (assembledEulerData
        (lumpedArch w₀ (fun s => DF.A s ^ d * ∏ i, ((DK i).A s * ((DK' i).A s)⁻¹) ^ r i)
          (fun s => DF.Ad s ^ d * ∏ i, ((DK i).Ad s * ((DK' i).Ad s)⁻¹) ^ r i)
          (fun s => DF.Ae s ^ d * ∏ i, ((DK i).Ae s * ((DK' i).Ae s)⁻¹) ^ r i)) f Lp Lpd)
        (exceptionalPlaces F B) := by
  have P := hasGlobalEquation_brauerProduct hH ψ hψ1 hψ ψf hψf μ d χ DF r K lam lam' μK DK DK'
    B hBF hBK hBK'
  -- A common right half-plane on which all the Hecke L-factors involved are nonzero.
  obtain ⟨σ₁, hσ₁⟩ := exists_heckeL_ne_zero χ
  obtain ⟨σ₂, hσ₂⟩ := exists_heckeL_ne_zero χ⁻¹
  choose σl hσl using fun i => exists_heckeL_ne_zero (lam i)
  choose σl' hσl' using fun i => exists_heckeL_ne_zero (lam' i)
  choose σli hσli using fun i => exists_heckeL_ne_zero (lam i)⁻¹
  choose σli' hσli' using fun i => exists_heckeL_ne_zero (lam' i)⁻¹
  obtain ⟨M, hM⟩ := (Set.finite_range
    (fun i => max (max (σl i) (σl' i)) (max (σli i) (σli' i)))).bddAbove
  have hMi : ∀ i, max (max (σl i) (σl' i)) (max (σli i) (σli' i)) ≤ M :=
    fun i => hM ⟨i, rfl⟩
  -- Nonvanishing products of Hecke L-factors.
  let G : FinitePlace F → ℂ → ℂ := fun z s => heckeL χ z s *
    ∏ i, ∏ u ∈ placesAbove (K i) z, (heckeL (lam i) u s * heckeL (lam' i) u s)
  let Gd : FinitePlace F → ℂ → ℂ := fun z s => heckeL χ⁻¹ z s *
    ∏ i, ∏ u ∈ placesAbove (K i) z, (heckeL (lam i)⁻¹ u s * heckeL (lam' i)⁻¹ u s)
  have hG : ∀ z, NonzeroMeromorphic (G z) := fun z =>
    NonzeroMeromorphic.mul (nonzeroMeromorphic_heckeL χ z)
      (NonzeroMeromorphic.finsetProd _ fun i _ =>
        NonzeroMeromorphic.finsetProd _ fun u _ =>
          NonzeroMeromorphic.mul (nonzeroMeromorphic_heckeL (lam i) u)
            (nonzeroMeromorphic_heckeL (lam' i) u))
  have hGd : ∀ z, NonzeroMeromorphic (Gd z) := fun z =>
    NonzeroMeromorphic.mul (nonzeroMeromorphic_heckeL χ⁻¹ z)
      (NonzeroMeromorphic.finsetProd _ fun i _ =>
        NonzeroMeromorphic.finsetProd _ fun u _ =>
          NonzeroMeromorphic.mul (nonzeroMeromorphic_heckeL (lam i)⁻¹ u)
            (nonzeroMeromorphic_heckeL (lam' i)⁻¹ u))
  have hLG : ∀ z s, G z s ≠ 0 → (f z).lFactor s = heckeL χ z s ^ d *
      ∏ i, ((∏ u ∈ placesAbove (K i) z, heckeL (lam i) u s) *
        (∏ u ∈ placesAbove (K i) z, heckeL (lam' i) u s)⁻¹) ^ r i := by
    intro z s hs
    obtain ⟨h1, h2⟩ := mul_ne_zero_iff.mp hs
    refine hL z s h1 fun i u hu => ?_
    exact mul_ne_zero_iff.mp (Finset.prod_ne_zero_iff.mp
      (Finset.prod_ne_zero_iff.mp h2 i (Finset.mem_univ i)) u hu)
  have hLdG : ∀ z s, Gd z s ≠ 0 → (f z).dualLFactor s = heckeL χ⁻¹ z s ^ d *
      ∏ i, ((∏ u ∈ placesAbove (K i) z, heckeL (lam i)⁻¹ u s) *
        (∏ u ∈ placesAbove (K i) z, heckeL (lam' i)⁻¹ u s)⁻¹) ^ r i := by
    intro z s hs
    obtain ⟨h1, h2⟩ := mul_ne_zero_iff.mp hs
    refine hLd z s h1 fun i u hu => ?_
    exact mul_ne_zero_iff.mp (Finset.prod_ne_zero_iff.mp
      (Finset.prod_ne_zero_iff.mp h2 i (Finset.mem_univ i)) u hu)
  -- Nonzero meromorphy of the package factors.
  have hl : ∀ z, NonzeroMeromorphic (fun s => heckeL χ z s ^ d *
      ∏ i, ((∏ u ∈ placesAbove (K i) z, heckeL (lam i) u s) *
        (∏ u ∈ placesAbove (K i) z, heckeL (lam' i) u s)⁻¹) ^ r i) := fun z =>
    NonzeroMeromorphic.mul (NonzeroMeromorphic.zpow (nonzeroMeromorphic_heckeL χ z) d)
      (NonzeroMeromorphic.finsetProd _ fun i _ => NonzeroMeromorphic.zpow
        (NonzeroMeromorphic.mul
          (NonzeroMeromorphic.finsetProd _ fun u _ => nonzeroMeromorphic_heckeL (lam i) u)
          (NonzeroMeromorphic.inv (NonzeroMeromorphic.finsetProd _ fun u _ =>
            nonzeroMeromorphic_heckeL (lam' i) u))) (r i))
  have hld : ∀ z, NonzeroMeromorphic (fun s => heckeL χ⁻¹ z s ^ d *
      ∏ i, ((∏ u ∈ placesAbove (K i) z, heckeL (lam i)⁻¹ u s) *
        (∏ u ∈ placesAbove (K i) z, heckeL (lam' i)⁻¹ u s)⁻¹) ^ r i) := fun z =>
    NonzeroMeromorphic.mul (NonzeroMeromorphic.zpow (nonzeroMeromorphic_heckeL χ⁻¹ z) d)
      (NonzeroMeromorphic.finsetProd _ fun i _ => NonzeroMeromorphic.zpow
        (NonzeroMeromorphic.mul
          (NonzeroMeromorphic.finsetProd _ fun u _ => nonzeroMeromorphic_heckeL (lam i)⁻¹ u)
          (NonzeroMeromorphic.inv (NonzeroMeromorphic.finsetProd _ fun u _ =>
            nonzeroMeromorphic_heckeL (lam' i)⁻¹ u))) (r i))
  -- The archimedean functions.
  have hA : NonzeroMeromorphic
      (fun s => DF.A s ^ d * ∏ i, ((DK i).A s * ((DK' i).A s)⁻¹) ^ r i) :=
    NonzeroMeromorphic.mul (NonzeroMeromorphic.zpow DF.nonzeroMeromorphic_A d)
      (NonzeroMeromorphic.finsetProd _ fun i _ => NonzeroMeromorphic.zpow
        (NonzeroMeromorphic.mul (DK i).nonzeroMeromorphic_A
          (NonzeroMeromorphic.inv (DK' i).nonzeroMeromorphic_A)) (r i))
  have hAd : NonzeroMeromorphic
      (fun s => DF.Ad s ^ d * ∏ i, ((DK i).Ad s * ((DK' i).Ad s)⁻¹) ^ r i) :=
    NonzeroMeromorphic.mul (NonzeroMeromorphic.zpow DF.nonzeroMeromorphic_Ad d)
      (NonzeroMeromorphic.finsetProd _ fun i _ => NonzeroMeromorphic.zpow
        (NonzeroMeromorphic.mul (DK i).nonzeroMeromorphic_Ad
          (NonzeroMeromorphic.inv (DK' i).nonzeroMeromorphic_Ad)) (r i))
  have hAe : NonzeroMeromorphic
      (fun s => DF.Ae s ^ d * ∏ i, ((DK i).Ae s * ((DK' i).Ae s)⁻¹) ^ r i) :=
    NonzeroMeromorphic.mul (NonzeroMeromorphic.zpow DF.nonzeroMeromorphic_Ae d)
      (NonzeroMeromorphic.finsetProd _ fun i _ => NonzeroMeromorphic.zpow
        (NonzeroMeromorphic.mul (DK i).nonzeroMeromorphic_Ae
          (NonzeroMeromorphic.inv (DK' i).nonzeroMeromorphic_Ae)) (r i))
  have hin : ∀ z ∈ B, MeromorphicEq (f z).lFactor (fun s => heckeL χ z s ^ d *
        ∏ i, ((∏ u ∈ placesAbove (K i) z, heckeL (lam i) u s) *
          (∏ u ∈ placesAbove (K i) z, heckeL (lam' i) u s)⁻¹) ^ r i) ∧
      MeromorphicEq (f z).dualLFactor (fun s => heckeL χ⁻¹ z s ^ d *
        ∏ i, ((∏ u ∈ placesAbove (K i) z, heckeL (lam i)⁻¹ u s) *
          (∏ u ∈ placesAbove (K i) z, heckeL (lam' i)⁻¹ u s)⁻¹) ^ r i) ∧
      MeromorphicEq (f z).epsilonFactor (fun s => finiteEpsilon χ ψf μ z s ^ d *
        ∏ i, ((∏ u ∈ placesAbove (K i) z,
            finiteEpsilon (lam i) (traceComponents ψf) (μK i) u s) *
          (∏ u ∈ placesAbove (K i) z,
            finiteEpsilon (lam' i) (traceComponents ψf) (μK i) u s)⁻¹) ^ r i) :=
    fun z _ => ⟨meromorphicEq_of_eq_of_ne_zero (hG z) (hLG z),
      meromorphicEq_of_eq_of_ne_zero (hGd z) (hLdG z), meromorphicEq_of_eq (hε z)⟩
  refine P.toFunctionalEquation _ f
    (lumpedArch_nonzeroMeromorphic w₀ hA hAd hAe)
    (meromorphicEq_of_eq (lumpedArch_prod_lFactor w₀ _ _ _))
    (meromorphicEq_of_eq (lumpedArch_prod_dualLFactor w₀ _ _ _))
    (meromorphicEq_of_eq (lumpedArch_prod_epsilonFactor w₀ _ _ _))
    (max (max σ₁ σ₂) M) ?_ hin ?_
  · intro z _ s hs
    have h12 : max σ₁ σ₂ < s.re := lt_of_le_of_lt (le_max_left _ _) hs
    have hMs : M < s.re := lt_of_le_of_lt (le_max_right _ _) hs
    have hi : ∀ i, max (max (σl i) (σl' i)) (max (σli i) (σli' i)) < s.re :=
      fun i => lt_of_le_of_lt (hMi i) hMs
    refine ⟨hL z s (hσ₁ z s (lt_of_le_of_lt (le_max_left _ _) h12)) fun i u _ => ⟨?_, ?_⟩,
      hLd z s (hσ₂ z s (lt_of_le_of_lt (le_max_right _ _) h12)) fun i u _ => ⟨?_, ?_⟩⟩
    · exact hσl i u s (lt_of_le_of_lt (le_max_left _ _) (lt_of_le_of_lt (le_max_left _ _) (hi i)))
    · exact hσl' i u s
        (lt_of_le_of_lt (le_max_right _ _) (lt_of_le_of_lt (le_max_left _ _) (hi i)))
    · exact hσli i u s
        (lt_of_le_of_lt (le_max_left _ _) (lt_of_le_of_lt (le_max_right _ _) (hi i)))
    · exact hσli' i u s
        (lt_of_le_of_lt (le_max_right _ _) (lt_of_le_of_lt (le_max_right _ _) (hi i)))
  · intro z hz
    exact ⟨NonzeroMeromorphic.congr (hl z) (hin z hz).1.symm,
      NonzeroMeromorphic.congr (hld z) (hin z hz).2.1.symm, hεnm z hz⟩

end Langlands.Global.FunctionalEquationComparison.RelativeWeilEngine

namespace Langlands.ClassField.Global.RelativeWeilGroup

/-- A representation of `W_{E/F}` continuous for the Krull topology on `Gal(E/F)` is
continuous for the discrete topology `relativeGaloisTopology`. -/
theorem FiniteRepresentation.isContinuous_discrete {c : FundamentalClass.ClassFamily.{u}}
    {F E : Type u} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    [IsGalois F E] (S : FiniteRepresentation.{0, u, uV} ℂ (RelativeWeilGroup c F E))
    (hS : S.IsContinuous) :
    letI := relativeGaloisTopology F E
    S.IsContinuous := by
  have key : ∀ t : TopologicalSpace (E ≃ₐ[F] E), krullTopology F E = t →
      letI := t
      S.IsContinuous := by
    rintro t rfl
    exact hS
  exact key _ (krullTopology_eq_relativeGaloisTopology F E)

end Langlands.ClassField.Global.RelativeWeilGroup

namespace Langlands.Global.FunctionalEquationComparison

open NumberField IsDedekindDomain
open scoped NumberField
open Langlands.Global Langlands.Global.HeckeFunctionalEquation Langlands.Global.AdelicFunctoriality
open Langlands.Global.CompletionPadic Langlands.VirtualRepresentation
open Langlands.ClassField.Global Langlands.ClassField.Global.RelativeWeilGroup
open Langlands.Global.FunctionalEquationComparison.RelativeWeilEngine

section Discrete

attribute [local instance] relativeGaloisTopology

/-- The global functional equation for twisted relative Weil pairs, assuming the transfer
reciprocity of local relative Weil maps. -/
theorem relativeWeilTwistFunctionalEquation_of_localTransferReciprocity
    (hN3 : LocalTransferReciprocityStatement.{u}) :
    RelativeWeilTwistFunctionalEquationStatement.{u, uV, uE} := by
  classical
  intro c hc F E _ _ _ _ _ _ ψ hψ1 hψ S S' hS hS'
  have h : FundamentalClass.Restriction c := hc.choose_spec.2.2.1
  have hgeo := LocalClassField.commonClosureGeometricProof.{u, u}
  have hN2 : LocalInducedRestrictionStatement.{max u uV, u} :=
    localInducedRestriction.{max u uV, u}
  have hN4 := transferNormCompatibilityStatement.{u}
  have hH := heckeGlobalFunctionalEquation_proof.{u}
  -- Components of `ψ` at the finite places and self-dual Haar measures.
  choose ψf hψf hμ using (hH F 1 ψ hψ1 hψ).1.1
  let μ := fun v => Classical.choice (hμ v)
  let μK : ∀ (K : IntermediateField F E) (u : FinitePlace K),
      LocalFactor.PadicAbelian.SelfDualHaar (topologicalData u) (traceComponents ψf u) :=
    fun K u => Classical.choice (nonempty_selfDualHaar u _)
  -- The class of `S ⊗ S'` and its Brauer decomposition.
  have hSd := FiniteRepresentation.isContinuous_discrete S hS
  have hS'd := FiniteRepresentation.isContinuous_discrete S' hS'
  let X : FiniteRepresentation.{0, u, max u uV} ℂ (RelativeWeilGroup c F E) :=
    FiniteRepresentation.tensor (FiniteRepresentation.tensor S S')
      (FiniteRepresentation.characterLine.{u, max u uV}
        (1 : RelativeWeilGroup c F E →ₜ* ℂˣ).toMonoidHom)
  have hX : X.IsContinuous := FiniteRepresentation.isContinuous_tensor
    (FiniteRepresentation.isContinuous_tensor hSd hS'd)
    (FiniteRepresentation.characterLine_isContinuous _)
  let eX : FiniteRepresentation.Equiv X (FiniteRepresentation.tensor S S') :=
    FiniteRepresentation.tensorTrivialLineEquiv _
  let x : ContinuousVirtual.{u, uV} c F E := ExactGrothendieckGroup.ofRepresentation _ ⟨X, hX⟩
  obtain ⟨n, r, K, θ, θ', hdec⟩ :=
    exists_twist_decomposition c F E h (inducedCharacterGeneration c F E) x
  choose θh hθh using fun i => exists_eq_continuousReciprocityCharacter
    (transferCharacterFactorization c hc (K i) E) (θ i)
  choose θh' hθh' using fun i => exists_eq_continuousReciprocityCharacter
    (transferCharacterFactorization c hc (K i) E) (θ' i)
  let d := ExactGrothendieckGroup.degree _ x
  -- Archimedean data, independent of the twist.
  let DF₀ : HeckeArchData (1 : HeckeCharacter F) ψ :=
    Classical.choice (nonempty_heckeArchData hH 1 ψ hψ1 hψ)
  let DK₀ : ∀ i, HeckeArchData (θh i) (traceAdditiveCharacter (L := K i) ψ hψ) := fun i =>
    Classical.choice (nonempty_heckeArchData hH _ _ (exists_traceAdditiveCharacter_ne_one ψ hψ)
      (traceAdditiveCharacter_diagonal ψ hψ))
  let DK₀' : ∀ i, HeckeArchData (θh' i) (traceAdditiveCharacter (L := K i) ψ hψ) := fun i =>
    Classical.choice (nonempty_heckeArchData hH _ _ (exists_traceAdditiveCharacter_ne_one ψ hψ)
      (traceAdditiveCharacter_diagonal ψ hψ))
  obtain ⟨w₀⟩ : Nonempty (InfinitePlace F) := inferInstance
  -- The finite exceptional set.
  obtain ⟨S₀, hS₀⟩ := exists_finset_additiveConductor_eq_zero hH ψ hψ1 hψ ψf hψf
  choose Sc hSc using fun i => exists_finset_additiveConductor_eq_zero hH
    (traceAdditiveCharacter (L := K i) ψ hψ) (exists_traceAdditiveCharacter_ne_one ψ hψ)
    (traceAdditiveCharacter_diagonal ψ hψ) (traceComponents ψf)
    (isFiniteAdditiveComponent_traceComponents ψ hψ ψf hψf)
  choose Sθ hSθ using fun i => HeckeFunctionalEquation.exists_finset_isUnramifiedAt _ (θh i)
  choose Sθ' hSθ' using fun i => HeckeFunctionalEquation.exists_finset_isUnramifiedAt _ (θh' i)
  refine ⟨S₀ ∪ Finset.univ.biUnion
      (fun i => (Sθ i ∪ Sθ' i ∪ Sc i).image (fun u => u.under (𝓞 F))),
    lumpedArch w₀ (fun s => DF₀.A s ^ d * ∏ i, ((DK₀ i).A s * ((DK₀' i).A s)⁻¹) ^ r i)
      (fun s => DF₀.Ad s ^ d * ∏ i, ((DK₀ i).Ad s * ((DK₀' i).Ad s)⁻¹) ^ r i)
      (fun s => DF₀.Ae s ^ d * ∏ i, ((DK₀ i).Ae s * ((DK₀' i).Ae s)⁻¹) ^ r i), ?_⟩
  intro χ _ hχ1 B hT₀B hχB f hf
  -- Transport of the archimedean data to the twisted characters.
  have hinf : ∀ v, χ.infiniteComponent v = (1 : HeckeCharacter F).infiniteComponent v := by
    intro v
    rw [HeckeCharacter.infiniteComponent_eq_one_of_hasPrescribedInfinityComponent_one χ hχ1 v]
    rfl
  have hinfK : ∀ i v, (HeckeCharacter.normComp χ * θh i).infiniteComponent v =
      (θh i).infiniteComponent v := fun i v => by
    rw [HeckeCharacter.infiniteComponent_mul,
      HeckeCharacter.normComp_infiniteComponent_eq_one χ hχ1 v]
    exact DFunLike.ext _ _ fun y => one_mul ((θh i).infiniteComponent v y)
  have hinfK' : ∀ i v, (HeckeCharacter.normComp χ * θh' i).infiniteComponent v =
      (θh' i).infiniteComponent v := fun i v => by
    rw [HeckeCharacter.infiniteComponent_mul,
      HeckeCharacter.normComp_infiniteComponent_eq_one χ hχ1 v]
    exact DFunLike.ext _ _ fun y => one_mul ((θh' i).infiniteComponent v y)
  -- Epsilon factors are `1` outside `B`.
  have hzB : ∀ z ∉ B, ∀ i, ∀ u ∈ placesAbove (K i) z,
      u ∉ Sθ i ∧ u ∉ Sθ' i ∧ u ∉ Sc i := by
    intro z hz i u hu
    have hzu : u.under (𝓞 F) = z := (mem_placesAbove u z).mp hu
    have hmem : ∀ T : Finset (FinitePlace (K i)), T ⊆ Sθ i ∪ Sθ' i ∪ Sc i → u ∈ T → False :=
      fun T hT huT => hz (hT₀B (Finset.mem_union_right _ (Finset.mem_biUnion.mpr
        ⟨i, Finset.mem_univ i, Finset.mem_image.mpr ⟨u, hT huT, hzu⟩⟩)))
    refine ⟨fun h1 => hmem _ ?_ h1, fun h1 => hmem _ ?_ h1, fun h1 => hmem _ ?_ h1⟩
    · exact fun _ h => Finset.mem_union_left _ (Finset.mem_union_left _ h)
    · exact fun _ h => Finset.mem_union_left _ (Finset.mem_union_right _ h)
    · exact fun _ h => Finset.mem_union_right _ h
  have hBF : ∀ z ∉ B, ∀ s : ℂ, finiteEpsilon χ ψf μ z s = 1 := fun z hz s =>
    finiteEpsilon_eq_one χ ψf μ z (hχB z hz)
      (hS₀ z fun h0 => hz (hT₀B (Finset.mem_union_left _ h0))) s
  have hunr : ∀ i, ∀ z ∉ B, ∀ u ∈ placesAbove (K i) z,
      (HeckeCharacter.normComp (L := K i) χ).IsUnramifiedAt u := by
    intro i z hz u hu
    obtain ⟨q, -, rfl⟩ := Finset.mem_map.mp hu
    exact HeckeCharacter.normComp_isUnramifiedAt χ z (hχB z hz) q
  have hBK : ∀ i, ∀ z ∉ B, ∀ u ∈ placesAbove (K i) z, ∀ s : ℂ,
      finiteEpsilon (HeckeCharacter.normComp χ * θh i) (traceComponents ψf) (μK (K i)) u s =
        1 := fun i z hz u hu s =>
    finiteEpsilon_eq_one _ _ _ u
      (isUnramifiedAt_mul (hunr i z hz u hu) (hSθ i u (hzB z hz i u hu).1))
      (hSc i u (hzB z hz i u hu).2.2) s
  have hBK' : ∀ i, ∀ z ∉ B, ∀ u ∈ placesAbove (K i) z, ∀ s : ℂ,
      finiteEpsilon (HeckeCharacter.normComp χ * θh' i) (traceComponents ψf) (μK (K i)) u s =
        1 := fun i z hz u hu s =>
    finiteEpsilon_eq_one _ _ _ u
      (isUnramifiedAt_mul (hunr i z hz u hu) (hSθ' i u (hzB z hz i u hu).2.1))
      (hSc i u (hzB z hz i u hu).2.2) s
  -- The finite factors as Hecke factors.
  have hloc : ∀ z, (∀ s, heckeL χ z s ≠ 0 → (∀ i, ∀ u ∈ placesAbove (K i) z,
        heckeL (HeckeCharacter.normComp χ * θh i) u s ≠ 0 ∧
          heckeL (HeckeCharacter.normComp χ * θh' i) u s ≠ 0) →
      (f z).lFactor s = heckeL χ z s ^ d *
        ∏ i, ((∏ u ∈ placesAbove (K i) z, heckeL (HeckeCharacter.normComp χ * θh i) u s) *
          (∏ u ∈ placesAbove (K i) z, heckeL (HeckeCharacter.normComp χ * θh' i) u s)⁻¹) ^
            r i) ∧
      (∀ s, heckeL χ⁻¹ z s ≠ 0 → (∀ i, ∀ u ∈ placesAbove (K i) z,
        heckeL (HeckeCharacter.normComp χ * θh i)⁻¹ u s ≠ 0 ∧
          heckeL (HeckeCharacter.normComp χ * θh' i)⁻¹ u s ≠ 0) →
      (f z).dualLFactor s = heckeL χ⁻¹ z s ^ d *
        ∏ i, ((∏ u ∈ placesAbove (K i) z, heckeL (HeckeCharacter.normComp χ * θh i)⁻¹ u s) *
          (∏ u ∈ placesAbove (K i) z, heckeL (HeckeCharacter.normComp χ * θh' i)⁻¹ u s)⁻¹) ^
            r i) ∧
      (∀ s, (f z).epsilonFactor s = finiteEpsilon χ ψf μ z s ^ d *
        ∏ i, ((∏ u ∈ placesAbove (K i) z, finiteEpsilon
              (HeckeCharacter.normComp χ * θh i) (traceComponents ψf) (μK (K i)) u s) *
          (∏ u ∈ placesAbove (K i) z, finiteEpsilon
              (HeckeCharacter.normComp χ * θh' i) (traceComponents ψf) (μK (K i)) u s)⁻¹) ^
            r i) := by
    intro z
    obtain ⟨w, e, ι, hι, ψz, eCz, εz, hεz, hcan, hfz⟩ := hf z
    exact localFactors_eq_heckeFactors h hN2 hN3 hN4 hgeo χ S S' X hX eX x rfl r K θ θ' hdec
      θh θh' hθh hθh' ψf μ (fun i => μK (K i)) w e ι hι ψz eCz εz hεz
      (eq_of_isFiniteAdditiveComponent (hψf z) fun y => hcan y) (f z) hfz
  have hεnm : ∀ z ∈ B, NonzeroMeromorphic (f z).epsilonFactor := by
    intro z _
    obtain ⟨w, e, ι, hι, ψz, eCz, εz, hεz, hcan, -, -, cε, m, -, hεf⟩ := hf z
    rw [show (f z).epsilonFactor = _ from funext hεf]
    exact nonzeroMeromorphic_epsilonMonomial _
      (Nat.zero_lt_of_lt (padicField z).canonicalTopologicalData.residueCardinality_gt_one) cε m
  exact exists_functionalEquation_of_heckeFactors hH ψ hψ1 hψ ψf hψf μ d χ
    (DF₀.ofInfiniteComponent_eq hinf) r K (fun i => HeckeCharacter.normComp χ * θh i)
    (fun i => HeckeCharacter.normComp χ * θh' i) (fun i => μK (K i))
    (fun i => (DK₀ i).ofInfiniteComponent_eq (hinfK i))
    (fun i => (DK₀' i).ofInfiniteComponent_eq (hinfK' i)) B hBF hBK hBK' w₀ f
    (fun z => (hloc z).1) (fun z => (hloc z).2.1) (fun z => (hloc z).2.2) hεnm

end Discrete

end Langlands.Global.FunctionalEquationComparison
