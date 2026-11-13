import Langlands.Representation.Unitary.CharacterPositivity
import Langlands.Representation.Character.SeparationProof
import Langlands.Representation.Smooth.Admissibility.CoefficientQuotient
import Langlands.Representation.Smooth.FixedVectors.LawsProof

/-!
# Level-wise input for unitarity of character-limit constituents

For a compact open subgroup `K`, the Hecke corner `H_K` acts on the `K`-fixed vectors of a
smooth representation. This module records two facts used at each level:

* if the distribution character of an admissible representation `ρ` is of positive type,
  then the trace of `star a * a` acting on `ρ^K` is nonnegative for every `a ∈ H_K`;
* an intertwiner restricts to an `H_K`-linear map of fixed vectors, injective or surjective
  when the intertwiner is.
-/

noncomputable section

namespace Langlands.CharacterLimitLevel

open MeasureTheory HarmonicAnalysis Hecke
open scoped ComplexOrder

universe uG uV uW

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure]
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {W : Type uW} [AddCommGroup W] [Module ℂ W]

/-- If the distribution character of an admissible representation is of positive type,
every Hecke-corner square `star a * a` acts on the fixed vectors with nonnegative trace. -/
theorem trace_cornerAction_star_mul_self_nonneg
    [T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G]
    (ρ : Representation ℂ G V) (hρ : IsAdmissible ρ)
    (hpos : Character.IsPositiveType μ (Character.distribution μ ρ hρ))
    (K : OpenSubgroup G) (hK : IsCompact (K : Set G)) (a : HeckeAlgebra.Corner μ K hK) :
    0 ≤ LinearMap.trace ℂ (fixedVectors ρ K.toSubgroup)
      (cornerAction μ ρ hρ.1 K hK (star a * a)) := by
  rw [← CharacterSeparation.distribution_corner μ ρ hρ K hK]
  exact hpos (HeckeAlgebra.toTestFunction μ (HeckeAlgebra.Corner.toHeckeAlgebra μ K hK a))

variable (K : OpenSubgroup G) (hK : IsCompact (K : Set G))

/-- An intertwiner of smooth representations restricted to `K`-fixed vectors, as a linear
map for the corner module structures. -/
def cornerLinearMap {ρ : Representation ℂ G V} (hρ : IsSmooth ρ)
    {σ : Representation ℂ G W} (hσ : IsSmooth σ) (T : ρ.IntertwiningMap σ) :
    letI := cornerModule μ ρ hρ K hK
    letI := cornerModule μ σ hσ K hK
    fixedVectors ρ K.toSubgroup →ₗ[HeckeAlgebra.Corner μ K hK] fixedVectors σ K.toSubgroup :=
  letI := cornerModule μ ρ hρ K hK
  letI := cornerModule μ σ hσ K hK
  { toFun := fixedVectorsMap T K.toSubgroup
    map_add' := (fixedVectorsMap T K.toSubgroup).map_add
    map_smul' := fun f v => cornerAction_intertwiner μ ρ hρ K hK hσ T f v }

@[simp]
theorem cornerLinearMap_apply {ρ : Representation ℂ G V} (hρ : IsSmooth ρ)
    {σ : Representation ℂ G W} (hσ : IsSmooth σ) (T : ρ.IntertwiningMap σ)
    (v : fixedVectors ρ K.toSubgroup) :
    cornerLinearMap μ K hK hρ hσ T v = fixedVectorsMap T K.toSubgroup v := rfl

theorem cornerLinearMap_injective {ρ : Representation ℂ G V} (hρ : IsSmooth ρ)
    {σ : Representation ℂ G W} (hσ : IsSmooth σ) (T : ρ.IntertwiningMap σ)
    (hT : Function.Injective T) :
    Function.Injective (cornerLinearMap μ K hK hρ hσ T) :=
  fixedVectorsMap_injective T hT K.toSubgroup

theorem cornerLinearMap_surjective {ρ : Representation ℂ G V} (hρ : IsSmooth ρ)
    {σ : Representation ℂ G W} (hσ : IsSmooth σ) (T : ρ.IntertwiningMap σ)
    (hT : Function.Surjective T) :
    Function.Surjective (cornerLinearMap μ K hK hρ hσ T) :=
  fixedVectorsMap_surjective_of_complexAlgebra T hT hρ K hK

end Langlands.CharacterLimitLevel
