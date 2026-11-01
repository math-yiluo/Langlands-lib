import Langlands.Representation.Parabolic.RefinedFiniteLengthFunctorStatement
import Langlands.Representation.Parabolic.FiniteLengthFunctorProof
import Langlands.Representation.CuspidalSupport.RefinedCuspidalInductionReduction
import Langlands.Representation.CuspidalSupport.RefinedJacquetLengthProof
import Langlands.Representation.Parabolic.FlattenedJacquetQuotientProof
import Langlands.Representation.Parabolic.InductionExactnessProof

/-!
# Finite length and exactness of the actual product-Levi refinement functors

Both actual refinement functors preserve finite group-algebra length and short
exact sequences of finite-length smooth representations, in every rank, for
every outer block shape and refinement, without any admissibility premise.
Finite length is reduced to the published all-rank standard theorem through
the actual flattened Levi equivalence, induction in stages and the flattened
Jacquet quotient; exactness is proved directly on the actual maps.
-/

noncomputable section

namespace Langlands.Parabolic.RefinedFiniteLengthFunctorAssembly

open GeneralLinear Geometric CategoryTheory
open scoped MonoidAlgebra

universe uF uV uW

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)

/-- Standard normalized parabolic induction of the actual normalized refined
induction of a finite-length smooth representation has finite length. -/
theorem normalizedParabolicInduced_refinedInduced_finiteLength {n : ℕ}
    (B : BlockShape n) (S : BlockRefinement B) :
    letI := T.topology
    ∀ A : SmoothRep.{0, uF, uV} ℂ (refinedLevi F.Carrier B S), A.HasFiniteLength →
      letI := T.generalLinearTopologicalGroup n
      letI := T.leviTopologicalGroup B
      IsFiniteLength ℂ[GeneralLinear n F.Carrier]
        (T.normalizedParabolicInduced B
          (T.normalizedRefinedInduced B S A.representation)).asModule := by
  let := T.topology
  intro A hA
  let := T.generalLinearTopologicalGroup n
  let := T.leviTopologicalGroup B
  let := T.valuativeRel
  let := T.localField
  let e := flattenedLeviEquiv F.Carrier B S
  let σ := A.representation
  have hσe : IsSmooth (σ.comp e.toMonoidHom) :=
    isSmooth_comp _ (flattenedLeviEquivContinuous F.Carrier B S).continuous A.isSmooth
  have hAe : IsFiniteLength ℂ[(B.flatten S).Levi F.Carrier]
      (Representation.asModule (σ.comp e.toMonoidHom)) :=
    (FiniteLengthAssembly.finiteLength_comp_surjective_iff σ e.toMonoidHom
      e.surjective).mp hA
  have hflat : IsFiniteLength ℂ[GeneralLinear n F.Carrier]
      (T.normalizedParabolicInduced (B.flatten S) (σ.comp e.toMonoidHom)).asModule :=
    (normalizedParabolicFiniteLength.{uF, uV} F T).1 n (B.flatten S)
      (SmoothRep.of (σ.comp e.toMonoidHom) hσe) hAe
  have hst := normalizedRefinementInductionTransitivity.{uF, uV} F T B S
  let E := hst.choose
  let E₁ : Representation.Equiv
      (T.normalizedParabolicInduced B (T.normalizedRefinedInduced B S σ))
      (T.normalizedComposedInduced B S σ) := by
    have E' := SmoothRep.equivOfIso (E.app A)
    dsimp only [CategoryTheory.Functor.comp_obj,
      PadicField.TopologicalData.normalizedRefinedInductionFunctor,
      normalizedRefinedInductionFunctorOf,
      PadicField.TopologicalData.normalizedParabolicInductionFunctor,
      BlockShape.normalizedInductionFunctorOf,
      PadicField.TopologicalData.normalizedComposedInductionFunctor,
      PadicField.TopologicalData.normalizedRefinedInduced,
      PadicField.TopologicalData.normalizedParabolicInduced,
      SmoothRep.representation, SmoothRep.of, Rep.of] at E' ⊢
    exact E'
  have hcf := composedFlattenedInduction.{uF, uV} p F T n B S _ σ
  let E₂ := hcf.choose
  exact FiniteLengthAssembly.finiteLength_of_injective
    (E₂.toIntertwiningMap.comp E₁.toIntertwiningMap) (E₂.injective.comp E₁.injective) hflat

/-- Normalized refined induction preserves finite length. -/
theorem inductionFiniteLength :
    NormalizedRefinedInductionFiniteLengthStatement.{uF, uV} F T := by
  let := T.topology
  intro n B S A hA
  let := T.generalLinearTopologicalGroup n
  let := T.leviTopologicalGroup B
  let ρI := T.normalizedRefinedInduced B S A.representation
  have hI : IsSmooth ρI := T.isSmooth_normalizedRefinedInduced B S A.representation
  let J := T.normalizedParabolicInduced B ρI
  have hJ : IsFiniteLength ℂ[GeneralLinear n F.Carrier] J.asModule :=
    normalizedParabolicInduced_refinedInduced_finiteLength F T B S A hA
  have hJsmooth : IsSmooth J := T.isSmooth_normalizedParabolicInduced B ρI
  have hJac : IsFiniteLength ℂ[B.Levi F.Carrier] (T.normalizedJacquet B J).asModule :=
    (normalizedParabolicFiniteLength.{uF, max uF uV} F T).2 n B (SmoothRep.of J hJsmooth) hJ
  exact FiniteLengthAssembly.finiteLength_of_surjective _
    (CuspidalSupport.jacquetEvaluation_id_surjective T B ρI hI) hJac

/-- The actual refined Jacquet map of a surjective intertwiner is surjective. -/
theorem normalizedRefinedJacquetMap_surjective {n : ℕ} (B : BlockShape n)
    (S : BlockRefinement B) {V : Type uV} {W : Type uW}
    [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    {ρ : Representation ℂ (B.Levi F.Carrier) V}
    {τ : Representation ℂ (B.Levi F.Carrier) W} (q : ρ.IntertwiningMap τ)
    (hq : Function.Surjective q) :
    Function.Surjective (T.normalizedRefinedJacquetMap B S q) := by
  change Function.Surjective (T.normalizedRefinedJacquetMap B S q).toLinearMap
  rw [CuspidalSupport.RefinedJacquetLengthProof.map_toLinearMap]
  exact Langlands.coinvariants_map_surjective _ hq

/-- The normalized refined Jacquet functor preserves finite length. -/
theorem jacquetFiniteLength :
    NormalizedRefinedJacquetFiniteLengthStatement.{uF, uV} F T := by
  let := T.topology
  intro n B S A hA
  let := T.generalLinearTopologicalGroup n
  let := T.leviTopologicalGroup B
  let e := flattenedLeviEquiv F.Carrier B S
  let X := T.normalizedParabolicInduced B A.representation
  have hXsmooth : IsSmooth X := T.isSmooth_normalizedParabolicInduced B A.representation
  have hX : IsFiniteLength ℂ[GeneralLinear n F.Carrier] X.asModule :=
    (normalizedParabolicFiniteLength.{uF, uV} F T).1 n B A hA
  have hflat : IsFiniteLength ℂ[(B.flatten S).Levi F.Carrier]
      (T.normalizedJacquet (B.flatten S) X).asModule :=
    (normalizedParabolicFiniteLength.{uF, max uF uV} F T).2 n (B.flatten S)
      (SmoothRep.of X hXsmooth) hX
  obtain ⟨f, -, hf⟩ := flattenedJacquetQuotient p F T n B S _ X
  have hiter : IsFiniteLength ℂ[refinedLevi F.Carrier B S]
      (T.normalizedRefinedJacquet B S (T.normalizedJacquet B X)).asModule :=
    (FiniteLengthAssembly.finiteLength_comp_surjective_iff _ e.toMonoidHom e.surjective).mpr
      (FiniteLengthAssembly.finiteLength_of_surjective f hf hflat)
  let ev := CuspidalSupport.jacquetEvaluation T B
    (Representation.IntertwiningMap.id X)
  have hev : Function.Surjective ev :=
    CuspidalSupport.jacquetEvaluation_id_surjective T B A.representation A.isSmooth
  exact FiniteLengthAssembly.finiteLength_of_surjective
    (T.normalizedRefinedJacquetMap B S ev)
    (normalizedRefinedJacquetMap_surjective F T B S ev hev) hiter

/-- A refined parabolic is closed in the actual product Levi. -/
theorem isClosed_refinedParabolic {n : ℕ} (B : BlockShape n) (S : BlockRefinement B) :
    letI := T.topology
    IsClosed (refinedParabolic F.Carrier B S : Set (B.Levi F.Carrier)) := by
  let := T.topology
  let := T.fieldT2
  rw [refinedParabolic, Subgroup.coe_pi]
  exact isClosed_set_pi fun i _ => (S i).isClosed_parabolic F.Carrier

/-- Normalized refined induction carries surjections of smooth representations
to surjections. -/
theorem normalizedRefinedInducedMap_surjective {n : ℕ} (B : BlockShape n)
    (S : BlockRefinement B) {V : Type uV} {W : Type uW}
    [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    {σ : Representation ℂ (refinedLevi F.Carrier B S) V}
    {τ : Representation ℂ (refinedLevi F.Carrier B S) W} (f : σ.IntertwiningMap τ)
    (hσ : letI := T.topology; IsSmooth σ) (hτ : letI := T.topology; IsSmooth τ)
    (hf : Function.Surjective f) :
    Function.Surjective (T.normalizedRefinedInducedMap B S f) := by
  let := T.topology
  let := T.moduleTopology
  let : IsTopologicalRing F.Carrier := IsModuleTopology.isTopologicalRing (Padic p) F.Carrier
  let := T.fieldT2
  let := T.leviTopologicalGroup B
  let := T.leviT2Space B
  refine Induction.smoothInductionSurjectivity.{uF, uV, uW} (B.Levi F.Carrier) ?_
    (refinedParabolic F.Carrier B S) (isClosed_refinedParabolic F T B S) V W _ _ ?_ ?_
    (refinedInducingMap B S (T.refinedLeviHalfModulus B S) f) hf
  · intro K
    let L := T.leviCompactOpen B K (K.isOpen.mem_nhds K.one_mem)
    exact ⟨L.1, L.2.1, L.2.2⟩
  · exact (isSmooth_twist_iff _ _ (T.isOpen_ker_refinedParabolicHalfModulus B S)).2
      (isSmooth_comp _ (refinedLeviProjectionContinuous F.Carrier B S).continuous hσ)
  · exact (isSmooth_twist_iff _ _ (T.isOpen_ker_refinedParabolicHalfModulus B S)).2
      (isSmooth_comp _ (refinedLeviProjectionContinuous F.Carrier B S).continuous hτ)

/-- Normalized refined induction preserves short exact sequences. -/
theorem inductionShortExact :
    NormalizedRefinedInductionShortExactStatement.{uF, uV} F T := by
  let := T.topology
  intro n B S A D E f g _ _ _ h
  let := T.valuativeRel
  let := T.localField
  let := T.leviTopologicalGroup B
  obtain ⟨hf, hg, hex⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · exact Induction.smoothInducedMap_injective _ _ hf
  · exact normalizedRefinedInducedMap_surjective F T B S (SmoothRep.hom g)
      D.isSmooth E.isSmooth hg
  · exact Induction.smoothInducedMap_range_eq_ker _ _ _ hf hex

/-- The normalized refined Jacquet functor preserves short exact sequences. -/
theorem jacquetShortExact :
    NormalizedRefinedJacquetShortExactStatement.{uF, uV} F T := by
  let := T.topology
  intro n B S A D E f g _ _ _ h
  obtain ⟨hf, hg, hex⟩ := h
  obtain ⟨hi, hex', hq⟩ := CuspidalSupport.RefinedJacquetLengthProof.map_exact T B S
    (SmoothRep.hom f) (SmoothRep.hom g) D.isSmooth hf hg hex
  exact ⟨hi, hq, hex'⟩

end Langlands.Parabolic.RefinedFiniteLengthFunctorAssembly

namespace Langlands.Parabolic

universe uF uV

/-- Both actual refinement functors preserve finite group-algebra length and
short exact sequences of finite-length smooth representations, in every rank,
for every outer block shape and refinement. -/
theorem normalizedRefinedFiniteLengthExactness
    {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData) :
    NormalizedRefinedFiniteLengthExactnessStatement.{uF, uV} F T :=
  ⟨RefinedFiniteLengthFunctorAssembly.inductionFiniteLength F T,
    RefinedFiniteLengthFunctorAssembly.jacquetFiniteLength F T,
    RefinedFiniteLengthFunctorAssembly.inductionShortExact F T,
    RefinedFiniteLengthFunctorAssembly.jacquetShortExact F T⟩

end Langlands.Parabolic
