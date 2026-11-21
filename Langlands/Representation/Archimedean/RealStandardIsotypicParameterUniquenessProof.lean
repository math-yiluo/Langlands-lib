import Langlands.Automorphic.GKIsotypicIrreducibility
import Langlands.Automorphic.LocalComponentEmbeddingReduction
import Langlands.Global.RankinSelberg.RealStandardIntertwinerPairLReduction
import Langlands.Representation.Archimedean.RealInjectiveIntertwinerStages
import Langlands.Representation.Archimedean.RealStandardCompactMultiplicityOne
import Langlands.Representation.Archimedean.RealStandardEllipticCartanComparisonProof
import Langlands.Representation.Archimedean.RealStandardEllipticCartanReduction
import Langlands.Representation.Archimedean.RealStandardIsotypicParameterUniquenessStatement

/-! # Real standard-module parameters in a common isotypic module -/

noncomputable section

universe uV uW

open scoped TensorProduct

set_option autoImplicit false

namespace Langlands.Archimedean

open Langlands.LocalFactor.Archimedean
open RealStandardCompactMultiplicityOne (realStandardExistsCompactScalarVector)

attribute [local instance 100] LieRing.ofAssociativeRing

local notation "K" n:max => Matrix.unitaryGroup (Fin n) ℝ
local notation "L" n:max => ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℝ
local notation "KF" n:max ds:max => kFiniteFunctions (realStandardModule n ds) (unitaryCompact ℝ n)
local notation "NF" ds:max => List.flatMap realBlockNormalize ds

private theorem realMoeglinData_normalize (ds : List RealBlock) :
    realMoeglinData (NF ds) = realMoeglinData ds := by
  have h (b : RealBlock) : realBlockMoeglinData b.positiveWeight = realBlockMoeglinData b := by
    cases b with
    | character d => rfl
    | induced d =>
      by_cases hd : d.weight < 0
      · simp [RealBlock.positiveWeight, realBlockMoeglinData, ComplexCharacterData.conj,
          hd, ne_of_lt hd]
      · simp [RealBlock.positiveWeight, hd]
  have hn : NF ds = (ds.flatMap realBlockExpand).map RealBlock.positiveWeight := by
    rw [List.map_flatMap]
    rfl
  rw [hn, realMoeglinData, List.flatMap_map]
  simp only [h]
  exact realMoeglinData_flatMap_expand ds

private theorem normalized_embedding {n : ℕ} {W : Type uW} [AddCommGroup W] [Module ℂ W]
    {σ : Representation ℂ (K n) W} {ξ : L n →ₗ⁅ℂ⁆ Module.End ℂ W} {ds : List RealBlock}
    {A : KF n ds →ₗ[ℂ] W} (hA : A ∈ gkHoms (realStandardRep n ds) (realStandardLie n ds) σ ξ)
    (hi : Function.Injective A) :
    ∃ S : KF n (NF ds) →ₗ[ℂ] W, Function.Injective S ∧
      S ∈ gkHoms (realStandardRep n (NF ds)) (realStandardLie n (NF ds)) σ ξ := by
  obtain ⟨T, hTi, hT⟩ := RealInjectiveIntertwinerExists.of_eq
    (realStandardModule_flatMap_normalize n ds).symm rfl (RealInjectiveIntertwinerExists.refl n ds)
  refine ⟨A.comp T, hi.comp hTi, ?_⟩
  obtain ⟨hK, hL⟩ := (mem_gkHoms _ _ _ _ _).mp hA
  exact ⟨fun k f => by simp only [LinearMap.comp_apply, hT.map_realStandardRep, hK],
    fun X f => by simp only [LinearMap.comp_apply, hT.map_realStandardLie, hL]⟩

private theorem standard_equiv_of_isotypic {n : ℕ}
    {V : Type uV} [AddCommGroup V] [Module ℂ V] {W : Type uW} [AddCommGroup W] [Module ℂ W]
    {ρ : Representation ℂ (K n) V} {π : L n →ₗ⁅ℂ⁆ Module.End ℂ V}
    {σ : Representation ℂ (K n) W} {ξ : L n →ₗ⁅ℂ⁆ Module.End ℂ W}
    (hirr : IsIrreducibleGKModule ρ π) (hiso : IsGKIsotypic ρ π σ ξ)
    {ds : List RealBlock} (hr : realRank ds = n) {A : KF n ds →ₗ[ℂ] W}
    (hA : A ∈ gkHoms (realStandardRep n ds) (realStandardLie n ds) σ ξ)
    (hi : Function.Injective A) :
    IsIrreducibleGKModule (realStandardRep n ds) (realStandardLie n ds) ∧
      Nonempty ((gkFreeRepresentation (realStandardRep n ds) (realStandardLie n ds)).Equiv
        (gkFreeRepresentation ρ π)) := by
  obtain ⟨x, hx, hline⟩ := realStandardExistsCompactScalarVector n ds hr
  have hI := isIrreducibleGKModule_of_injective_of_isotypic _ _ _ _ _ _ hirr hiso A hA hi x hx hline
  have := isIrreducible_gkFreeRepresentation _ _ hI
  have := isIrreducible_gkFreeRepresentation _ _ hirr
  have := hI.1
  let f := gkHomsIntertwiningMap _ _ _ _ ⟨A, hA⟩
  have hf : f ≠ 0 := fun h0 => LinearMap.ne_zero_of_injective hi
    (congrArg Representation.IntertwiningMap.toLinearMap h0)
  obtain ⟨g, hg⟩ := IsotypicEmbedding.exists_intertwiningMap_ne_zero_of_isotypic
    (gkFreeRepresentation ρ π) (gkFreeRepresentation (realStandardRep n ds) (realStandardLie n ds))
    (gkFreeRepresentation σ ξ) ((isGKIsotypic_iff _ _ _ _).mp hiso) f hf
  exact ⟨hI, ⟨g.ofBijective ((Representation.IsIrreducible.bijective_or_eq_zero g).resolve_right hg)⟩⟩

private theorem isRealStandardIntertwiner_of_mem_gkHoms {n : ℕ} {ds es : List RealBlock}
    {T : KF n ds →ₗ[ℂ] KF n es}
    (hT : T ∈ gkHoms (realStandardRep n ds) (realStandardLie n ds)
      (realStandardRep n es) (realStandardLie n es)) :
    IsRealStandardIntertwiner n (realStandardRep n es) (realStandardLie n es) ds T := by
  obtain ⟨hK, hL⟩ := (mem_gkHoms _ _ _ _ _).mp hT
  exact InductionStages.isRealStandardIntertwiner_iff.mpr
    ⟨fun k f => hK (InductionStages.toUnitary n k) f, fun X f => hL (1 ⊗ₜ X) f⟩

private theorem uniqueness_of_positiveWeightUnique (hunique : RealPositiveWeightStandardUniqueStatement) :
    RealStandardIsotypicParameterUniquenessStatement.{uV,uW} := by
  intro n V W _ _ _ _ ρ π σ ξ ds es A B _ hirr _ hiso hd he hA hiA hB hiB
  have hd' := (realRank_flatMap_normalize ds).trans hd
  have he' := (realRank_flatMap_normalize es).trans he
  obtain ⟨A', hiA', hA'⟩ := normalized_embedding hA hiA
  obtain ⟨B', hiB', hB'⟩ := normalized_embedding hB hiB
  obtain ⟨hId, ⟨ed⟩⟩ := standard_equiv_of_isotypic hirr hiso hd' hA' hiA'
  obtain ⟨hIe, ⟨ee⟩⟩ := standard_equiv_of_isotypic hirr hiso he' hB' hiB'
  let T := ed.trans ee.symm
  have hgk := toLinearMap_mem_gkHoms _ _ _ _ T.toIntertwiningMap
  have hp := hunique n (NF ds) (NF es) hd' he'
    (fun _ => weight_pos_of_mem_flatMap_normalize) (fun _ => weight_pos_of_mem_flatMap_normalize)
    hId hIe T.toLinearMap (isRealStandardIntertwiner_of_mem_gkHoms hgk) T.toLinearEquiv.bijective
  rw [← realMoeglinData_normalize ds, ← realMoeglinData_normalize es]
  exact hp.flatMap_right realBlockMoeglinData

/-- If two real standard modules of rank `n` embed by injective
`(𝔤, K)`-intertwiners into one module that is isotypic of the type of an
irreducible `(𝔤, K)`-module, then their lists of Mœglin data are permutations
of each other. -/
theorem realStandardIsotypicParameterUniqueness :
    RealStandardIsotypicParameterUniquenessStatement.{uV, uW} :=
  uniqueness_of_positiveWeightUnique
    (realStandardEllipticCartanReduction
      RealStandardEllipticCartan.realStandardEllipticCartanComparison)

end Langlands.Archimedean
