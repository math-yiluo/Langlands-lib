import Langlands.Representation.Aubert.General.LocalFieldRefinedParabolicPreservationStatement
import Langlands.Representation.Aubert.General.LocalFieldMatrixParabolicPreservationProof
import Langlands.AllField.Representation.Parabolic.RefinementInductionTransitivityProof
import Langlands.AllField.Representation.Parabolic.RefinementCoordinatesNormalizationProof
import Langlands.AllField.Representation.Parabolic.FlattenedJacquetQuotientProof
import Langlands.AllField.Representation.CuspidalSupport.RefinedJacquetLengthProof
import Langlands.AllFieldBZ.Representation.CuspidalSupport.InducedJacquetEvaluation
import Langlands.Representation.Parabolic.ComposedFlattenedInductionProof
import Langlands.Representation.Induction.CompactLocalSection

/-! Normalized refined induction and Jacquet restriction preserve length and exactness. -/

noncomputable section

set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency.types false

open scoped MonoidAlgebra

namespace Langlands.Aubert.General.RationalPointFamily.GL

open GeneralLinear Geometric SmoothRep
open FiniteLengthAssembly

universe uF uV uW

variable {F : Type uF} [Field F] (T : LocalFieldData F)

/-- The actual composed induction agrees with induction in flattened block coordinates. -/
theorem composedInductionEquivFlattened {n : ℕ} (B : BlockShape n) (S : BlockRefinement B)
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (σ : Representation ℂ (refinedLevi F B S) V) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup n
    Nonempty ((T.normalizedComposedInduced B S σ).Equiv
      (T.normalizedParabolicInduced (B.flatten S)
        (σ.comp (flattenedLeviEquiv F B S).toMonoidHom))) := by
  let := T.topology
  let := T.generalLinearTopologicalGroup n
  let e := B.flattenBlockEquiv S
  let hs := fun a => (B.flatten_size_flattenBlockEquiv S a).symm
  have hc : ∀ i k x, B.index i ((S i).index k x) =
      (B.flatten S).index (e ⟨i, k⟩) (Fin.cast (hs ⟨i, k⟩) x) :=
    fun i k x => B.index_index_eq_flatten S ⟨i, k⟩ x
  have hσ :
      (σ.comp (flattenedLeviEquiv F B S).toMonoidHom).comp
        ((B.flatten S).leviRefinementEquiv B S e hs F).symm.toMonoidHom = σ := by
    apply MonoidHom.ext
    intro m
    change σ (flattenedLeviEquiv F B S
      (((B.flatten S).leviRefinementEquiv B S e hs F).symm m)) = σ m
    rw [B.leviRefinementEquiv_flatten F S, MulEquiv.apply_symm_apply]
  have h := (AllField.Parabolic.refinementCoordinatesNormalization F T n (B.flatten S) B S
    e hs hc).2.2 V (σ.comp (flattenedLeviEquiv F B S).toMonoidHom)
  dsimp only at h
  rw [hσ] at h
  exact ⟨h.choose⟩

private theorem jacquet_evaluation_surjective {n : ℕ} (B : BlockShape n)
    {V : Type uV} [AddCommGroup V] [Module ℂ V] (σ : Representation ℂ (B.Levi F) V) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup n
    IsSmooth σ → Function.Surjective
      (AllFieldBZ.CuspidalSupport.jacquetEvaluation (F := AllFieldBZ.LocalFieldPackage.ofField F)
        T B (Representation.IntertwiningMap.id (T.normalizedParabolicInduced B σ))) := by
  let := T.topology
  let := T.generalLinearTopologicalGroup n
  let := T.generalLinearNonarchimedean n
  let := T.generalLinearLocallyCompactSpace n
  intro hσ v
  have hσP : IsSmooth (twist (T.parabolicHalfModulus B) (σ.comp (B.leviProjection F))) :=
    (isSmooth_twist_iff _ _ (T.isOpen_ker_parabolicHalfModulus B)).mpr
      (isSmooth_comp _ (T.blockLeviProjection B).continuous hσ)
  let f := Induction.compactLocalSection _ _ hσP 1 v Set.univ isOpen_univ (Set.mem_univ _)
  refine ⟨B.jacquetMk (T.normalizedParabolicInduced B σ) f.val, ?_⟩
  exact Induction.compactLocalSection_apply _ _ hσP 1 v Set.univ isOpen_univ (Set.mem_univ _)

/-- The actual iterated induction agrees with the direct composed induction. -/
noncomputable def iteratedInductionEquivComposed {n : ℕ} (B : BlockShape n)
    (S : BlockRefinement B) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup n
    letI := T.leviTopologicalGroup B
    ∀ A : SmoothRep.{0, uF, uV} ℂ (refinedLevi F B S),
      (T.normalizedParabolicInduced B (T.normalizedRefinedInduced B S A.representation)).Equiv
        (T.normalizedComposedInduced B S A.representation) := by
  let := T.topology
  let := T.generalLinearTopologicalGroup n
  let := T.leviTopologicalGroup B
  intro A
  let E := (AllField.Parabolic.normalizedRefinementInductionTransitivity.{uF, uV} F T B S).choose
  have E' := SmoothRep.equivOfIso (E.app A)
  dsimp only [CategoryTheory.Functor.comp_obj, LocalFieldData.normalizedRefinedInductionFunctor,
    normalizedRefinedInductionFunctorOf, LocalFieldData.normalizedParabolicInductionFunctor,
    BlockShape.normalizedInductionFunctorOf, LocalFieldData.normalizedComposedInductionFunctor,
    LocalFieldData.normalizedRefinedInduced, LocalFieldData.normalizedParabolicInduced,
    SmoothRep.representation, SmoothRep.of, Rep.of] at E' ⊢
  exact E'

set_option maxHeartbeats 5000000 in
/-- Standard normalized parabolic induction of the actual normalized refined
induction of a finite-length smooth representation has finite length. -/
private theorem normalizedParabolicInduced_refinedInduced_finiteLength {n : ℕ}
    (B : BlockShape n) (S : BlockRefinement B) :
    letI := T.topology
    ∀ A : SmoothRep.{0, uF, max (uF + 1) uV} ℂ (refinedLevi F B S), A.HasFiniteLength →
      letI := T.generalLinearTopologicalGroup n
      letI := T.leviTopologicalGroup B
      IsFiniteLength ℂ[GeneralLinear n F]
        (T.normalizedParabolicInduced B
          (T.normalizedRefinedInduced B S A.representation)).asModule := by
  let := T.topology
  intro A hA
  let := T.generalLinearTopologicalGroup n
  let := T.leviTopologicalGroup B
  let := T.valuativeRel
  let := T.localField
  let e := flattenedLeviEquiv F B S
  let σ := A.representation
  have hσe : IsSmooth (σ.comp e.toMonoidHom) :=
    isSmooth_comp _ (flattenedLeviEquivContinuous F B S).continuous A.isSmooth
  have hAe : IsFiniteLength ℂ[(B.flatten S).Levi F]
      (Representation.asModule (σ.comp e.toMonoidHom)) :=
    (FiniteLengthAssembly.finiteLength_comp_surjective_iff σ e.toMonoidHom
      e.surjective).mp hA
  have hflat : IsFiniteLength ℂ[GeneralLinear n F]
      (T.normalizedParabolicInduced (B.flatten S) (σ.comp e.toMonoidHom)).asModule :=
    (localFieldMatrixParabolicPreservation.{uF, uV} F T n (B.flatten S)).1
      (SmoothRep.of (σ.comp e.toMonoidHom) hσe) hAe
  let E₂ := Classical.choice (composedInductionEquivFlattened.{uF, max (uF + 1) uV} T B S σ)
  have hmid : IsFiniteLength ℂ[GeneralLinear n F] (T.normalizedComposedInduced B S σ).asModule :=
    finiteLength_of_injective E₂.toIntertwiningMap E₂.injective hflat
  let E₁ := iteratedInductionEquivComposed.{uF, max (uF + 1) uV} T B S A
  exact finiteLength_of_injective E₁.toIntertwiningMap E₁.injective hmid

/-- Normalized refined induction preserves finite length. -/
private theorem inductionFiniteLength (n : ℕ) (B : BlockShape n) (S : BlockRefinement B) :
    letI := T.topology
    PreservesFiniteLength (T.normalizedRefinedInductionFunctor.{uF, max (uF + 1) uV} B S) := by
  let := T.topology
  intro A hA
  let := T.generalLinearTopologicalGroup n
  let := T.leviTopologicalGroup B
  let ρI := T.normalizedRefinedInduced B S A.representation
  have hI : IsSmooth ρI :=
    ((T.normalizedRefinedInductionFunctor B S).obj A).isSmooth
  let J := T.normalizedParabolicInduced B ρI
  have hJ : IsFiniteLength ℂ[GeneralLinear n F] J.asModule :=
    normalizedParabolicInduced_refinedInduced_finiteLength.{uF, uV} T B S A hA
  have hJsmooth : IsSmooth J := T.isSmooth_normalizedParabolicInduced B ρI
  have hJac : IsFiniteLength ℂ[B.Levi F] (T.normalizedJacquet B J).asModule :=
    (localFieldMatrixParabolicPreservation.{uF, uV} F T n B).2.2.1 (SmoothRep.of J hJsmooth) hJ
  exact FiniteLengthAssembly.finiteLength_of_surjective _
    (jacquet_evaluation_surjective T B ρI hI) hJac

/-- The actual refined Jacquet map of a surjective intertwiner is surjective. -/
private theorem normalizedRefinedJacquetMap_surjective {n : ℕ} (B : BlockShape n)
    (S : BlockRefinement B) {V : Type uV} {W : Type uW}
    [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    {ρ : Representation ℂ (B.Levi F) V}
    {τ : Representation ℂ (B.Levi F) W} (q : ρ.IntertwiningMap τ)
    (hq : Function.Surjective q) :
    Function.Surjective (T.normalizedRefinedJacquetMap B S q) := by
  change Function.Surjective (T.normalizedRefinedJacquetMap B S q).toLinearMap
  rw [AllField.CuspidalSupport.RefinedJacquetLengthProof.map_toLinearMap]
  exact Langlands.coinvariants_map_surjective _ hq

/-- The normalized refined Jacquet functor preserves finite length. -/
private theorem jacquetFiniteLength (n : ℕ) (B : BlockShape n) (S : BlockRefinement B) :
    letI := T.topology
    PreservesFiniteLength (T.normalizedRefinedJacquetFunctor.{uF, max (uF + 1) uV} B S) := by
  let := T.topology
  intro A hA
  let := T.generalLinearTopologicalGroup n
  let := T.leviTopologicalGroup B
  let e := flattenedLeviEquiv F B S
  let X := T.normalizedParabolicInduced B A.representation
  have hXsmooth : IsSmooth X := T.isSmooth_normalizedParabolicInduced B A.representation
  have hX : IsFiniteLength ℂ[GeneralLinear n F] X.asModule :=
    (localFieldMatrixParabolicPreservation.{uF, uV} F T n B).1 A hA
  have hflat : IsFiniteLength ℂ[(B.flatten S).Levi F]
      (T.normalizedJacquet (B.flatten S) X).asModule :=
    (localFieldMatrixParabolicPreservation.{uF, uV} F T n (B.flatten S)).2.2.1
      (SmoothRep.of X hXsmooth) hX
  obtain ⟨f, -, hf⟩ := AllField.Parabolic.flattenedJacquetQuotient F T n B S _ X
  have hiter : IsFiniteLength ℂ[refinedLevi F B S]
      (T.normalizedRefinedJacquet B S (T.normalizedJacquet B X)).asModule :=
    (FiniteLengthAssembly.finiteLength_comp_surjective_iff _ e.toMonoidHom e.surjective).mpr
      (FiniteLengthAssembly.finiteLength_of_surjective f hf hflat)
  let ev := AllFieldBZ.CuspidalSupport.jacquetEvaluation
    (F := AllFieldBZ.LocalFieldPackage.ofField F) T B
    (Representation.IntertwiningMap.id X)
  have hev : Function.Surjective ev :=
    jacquet_evaluation_surjective T B A.representation A.isSmooth
  exact FiniteLengthAssembly.finiteLength_of_surjective
    (T.normalizedRefinedJacquetMap B S ev)
    (normalizedRefinedJacquetMap_surjective T B S ev hev) hiter

/-- A refined parabolic is closed in the actual product Levi. -/
private theorem isClosed_refinedParabolic {n : ℕ} (B : BlockShape n) (S : BlockRefinement B) :
    letI := T.topology
    IsClosed (refinedParabolic F B S : Set (B.Levi F)) := by
  let := T.topology
  let := T.fieldT2
  rw [refinedParabolic, Subgroup.coe_pi]
  exact isClosed_set_pi fun i _ => (S i).isClosed_parabolic F

/-- Normalized refined induction carries surjections of smooth representations
to surjections. -/
private theorem normalizedRefinedInducedMap_surjective {n : ℕ} (B : BlockShape n)
    (S : BlockRefinement B) {V : Type uV} {W : Type uW}
    [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    {σ : Representation ℂ (refinedLevi F B S) V}
    {τ : Representation ℂ (refinedLevi F B S) W} (f : σ.IntertwiningMap τ)
    (hσ : letI := T.topology; IsSmooth σ) (hτ : letI := T.topology; IsSmooth τ)
    (hf : Function.Surjective f) :
    Function.Surjective (T.normalizedRefinedInducedMap B S f) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := T.fieldT2
  let := T.leviTopologicalGroup B
  let := T.leviT2Space B
  refine Induction.smoothInductionSurjectivity.{uF, uV, uW} (B.Levi F) ?_
    (refinedParabolic F B S) (isClosed_refinedParabolic T B S) V W _ _ ?_ ?_
    (refinedInducingMap B S (T.refinedLeviHalfModulus B S) f) hf
  · intro K
    obtain ⟨L, hLc, hLK⟩ := AllField.CuspidalSupport.levi_exists_compact_openSubgroup_subset
      T B K (K.isOpen.mem_nhds K.one_mem)
    exact ⟨L, hLc, hLK⟩
  · exact (isSmooth_twist_iff _ _ (AllField.CuspidalSupport.isOpen_ker_refinedParabolicHalfModulus T B S)).2
      (isSmooth_comp _ (refinedLeviProjectionContinuous F B S).continuous hσ)
  · exact (isSmooth_twist_iff _ _ (AllField.CuspidalSupport.isOpen_ker_refinedParabolicHalfModulus T B S)).2
      (isSmooth_comp _ (refinedLeviProjectionContinuous F B S).continuous hτ)

/-- Normalized refined induction preserves short exact sequences. -/
private theorem inductionShortExact (n : ℕ) (B : BlockShape n) (S : BlockRefinement B) :
    letI := T.topology
    PreservesFiniteLengthShortExact (T.normalizedRefinedInductionFunctor.{uF, max (uF + 1) uV} B S) := by
  let := T.topology
  intro A D E f g _ _ _ h
  let := T.valuativeRel
  let := T.localField
  let := T.leviTopologicalGroup B
  obtain ⟨hf, hg, hex⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · exact Induction.smoothInducedMap_injective _ _ hf
  · exact normalizedRefinedInducedMap_surjective T B S (SmoothRep.hom g)
      D.isSmooth E.isSmooth hg
  · exact Induction.smoothInducedMap_range_eq_ker _ _ _ hf hex

/-- The normalized refined Jacquet functor preserves short exact sequences. -/
private theorem jacquetShortExact (n : ℕ) (B : BlockShape n) (S : BlockRefinement B) :
    letI := T.topology
    PreservesFiniteLengthShortExact (T.normalizedRefinedJacquetFunctor.{uF, max (uF + 1) uV} B S) := by
  let := T.topology
  intro A D E f g _ _ _ h
  obtain ⟨hf, hg, hex⟩ := h
  obtain ⟨hi, hex', hq⟩ := AllField.CuspidalSupport.RefinedJacquetLengthProof.map_exact T B S
    (SmoothRep.hom f) (SmoothRep.hom g) D.isSmooth hf hg hex
  exact ⟨hi, hq, hex'⟩

/-- Exact preservation for all actual normalized refinement functors. -/
theorem localFieldRefinedParabolicPreservation : LocalFieldRefinedParabolicPreservationStatement.{uF, uV} := by
  intro F _ T n B S
  exact ⟨inductionFiniteLength T n B S, inductionShortExact T n B S,
    jacquetFiniteLength T n B S, jacquetShortExact T n B S⟩

end Langlands.Aubert.General.RationalPointFamily.GL
