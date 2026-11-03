import Langlands.Representation.Aubert.General.Parabolic
import Langlands.Representation.Category.Subquotients
import Langlands.Representation.Induction.CompactQuotientProof
import Langlands.Representation.Jacquet.LocalizationExactnessProof

/-! Actual normalized induction and Jacquet on directed unions. -/

noncomputable section

open CategoryTheory

namespace Langlands.Induction

universe uR uG uV uW

variable {R : Type uR} {G : Type uG} {V : Type uV} {W : Type uW}
  [CommRing R] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W]

/-- An induced function whose values lie in an injective coefficient map lifts
with its original open right stabilizer. -/
theorem smoothInducedMap_exists_preimage_of_eval_mem_range
    (P : Subgroup G) {σ : Representation R P V} {τ : Representation R P W}
    (T : σ.IntertwiningMap τ) (hT : Function.Injective T)
    (f : SmoothFunctions P τ)
    (hf : ∀ x : G, eval P τ f x ∈ LinearMap.range T.toLinearMap) :
    ∃ g : SmoothFunctions P σ, smoothInducedMap P T g = f := by
  classical
  choose g hg using hf
  change ∀ x, T (g x) = eval P τ f x at hg
  obtain ⟨K, hK⟩ := smoothInduced_smooth P τ f
  let g' : SmoothFunctions P σ := smoothFunctionOf P σ g
    (by
      intro p x
      apply hT
      rw [T.isIntertwining, hg, hg, eval_covariant]) K
    (by
      intro k x
      apply hT
      rw [hg, hg]
      exact eval_mul_of_mem_fixedVectors P τ K.toSubgroup hK k x)
  refine ⟨g', ?_⟩
  apply Subtype.ext
  apply Subtype.ext
  funext x
  exact hg x

/-- A chosen actual lift of a smooth induced function through an injective
coefficient map, when every evaluation lies in its image. -/
def smoothInducedLiftOfEvalMemRange
    (P : Subgroup G) {σ : Representation R P V} {τ : Representation R P W}
    (T : σ.IntertwiningMap τ) (hT : Function.Injective T)
    (f : SmoothFunctions P τ)
    (hf : ∀ x : G, eval P τ f x ∈ LinearMap.range T.toLinearMap) :
    SmoothFunctions P σ :=
  (smoothInducedMap_exists_preimage_of_eval_mem_range P T hT f hf).choose

/-- Postcomposition of the chosen lift is the original induced function. -/
theorem smoothInducedMap_liftOfEvalMemRange
    (P : Subgroup G) {σ : Representation R P V} {τ : Representation R P W}
    (T : σ.IntertwiningMap τ) (hT : Function.Injective T)
    (f : SmoothFunctions P τ)
    (hf : ∀ x : G, eval P τ f x ∈ LinearMap.range T.toLinearMap) :
    smoothInducedMap P T (smoothInducedLiftOfEvalMemRange P T hT f hf) = f :=
  (smoothInducedMap_exists_preimage_of_eval_mem_range P T hT f hf).choose_spec

end Langlands.Induction

namespace Langlands.Aubert.General

universe uG uV uI

variable {G : Type uG} [Group G] [TopologicalSpace G] [LocallyCompactSpace G]
  [NonarchimedeanGroup G] {P M U : Subgroup G}

/-- An actual normalized induced function lifts through an injective smooth
coefficient map when all its evaluations are in the range. -/
theorem normalizedInductionFunctor_exists_preimage_of_eval_mem_range
    (h : IsSemidirectDecomposition P M U) (hU : IsClosed (U : Set G))
    {A B : SmoothRep.{0, uG, uV} ℂ M} (φ : A ⟶ B)
    (hφ : Function.Injective (SmoothRep.hom φ))
    (f : (normalizedInductionFunctor h hU).obj B)
    (hf : ∀ x : G, Induction.eval P (inducingRepresentation h hU B) f x ∈
      LinearMap.range (SmoothRep.hom φ).toLinearMap) :
    ∃ g : (normalizedInductionFunctor h hU).obj A,
      SmoothRep.hom ((normalizedInductionFunctor h hU).map φ) g = f := by
  let T : (inducingRepresentation h hU A).IntertwiningMap
      (inducingRepresentation h hU B) :=
    ((Induction.SmoothCharacter.twistFunctor
      (inductionCharacter U P hU h.le_normalizer)).map ((inflationFunctor h).map φ)).hom
  exact Induction.smoothInducedMap_exists_preimage_of_eval_mem_range P T hφ f hf

/-- Compactness of `P \ G` makes every normalized induced function come from one
member of a directed covering family of injective coefficient maps. -/
theorem normalizedInductionFunctor_exists_preimage_of_directed_cover
    (h : IsSemidirectDecomposition P M U) (hU : IsClosed (U : Set G))
    [CompactSpace (Induction.LeftQuotient P)] {ι : Type uI}
    (A : ι → SmoothRep.{0, uG, uV} ℂ M) (B : SmoothRep.{0, uG, uV} ℂ M)
    (φ : ∀ i, A i ⟶ B) (hinj : ∀ i, Function.Injective (SmoothRep.hom (φ i)))
    (hdir : Directed (· ≤ ·) (fun i => (SmoothRep.hom (φ i)).range))
    (hcover : ∀ b : B, ∃ i, b ∈ (SmoothRep.hom (φ i)).range)
    (f : (normalizedInductionFunctor h hU).obj B) :
    ∃ i, ∃ g : (normalizedInductionFunctor h hU).obj (A i),
      SmoothRep.hom ((normalizedInductionFunctor h hU).map (φ i)) g = f := by
  classical
  obtain ⟨K, hK⟩ := ((normalizedInductionFunctor h hU).obj B).isSmooth f
  obtain ⟨t, ht⟩ := Induction.exists_finset_doubleCoset_cover P K
  have hfinite : ∀ s : Finset G, ∃ i, ∀ x ∈ s,
      Induction.eval P (inducingRepresentation h hU B) f x ∈
        (SmoothRep.hom (φ i)).range := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
        obtain ⟨i, _⟩ := hcover 0
        exact ⟨i, by simp⟩
    | @insert x s hxs ih =>
        obtain ⟨i, hi⟩ := ih
        obtain ⟨j, hj⟩ := hcover (Induction.eval P (inducingRepresentation h hU B) f x)
        obtain ⟨k, hik, hjk⟩ := hdir i j
        refine ⟨k, ?_⟩
        intro y hy
        rcases Finset.mem_insert.mp hy with rfl | hy
        · exact hjk hj
        · exact hik (hi y hy)
  obtain ⟨i, hi⟩ := hfinite t
  refine ⟨i, normalizedInductionFunctor_exists_preimage_of_eval_mem_range h hU (φ i)
    (hinj i) f ?_⟩
  intro x
  obtain ⟨y, hy, p, hp, k, hk, rfl⟩ := ht x
  rw [Induction.eval_mul_of_mem_fixedVectors P (inducingRepresentation h hU B)
    K.toSubgroup hK ⟨k, hk⟩, normalizedInductionFunctor_covariant h hU B f ⟨p, hp⟩ y]
  exact (SmoothRep.hom (φ i)).range.toSubmodule.smul_mem _
    ((SmoothRep.hom (φ i)).range.apply_mem_toSubmodule (h.projection ⟨p, hp⟩) (hi y hy))

/-- The actual normalized Jacquet functor preserves injectivity when `U` is a
limit of compact subgroups. -/
theorem normalizedJacquetFunctor_map_injective
    (U M : Subgroup G) (hU : IsClosed (U : Set G))
    (hMU : M ≤ Subgroup.normalizer (U : Set G))
    (hUc : Jacquet.Localization.IsLimitOfCompactSubgroups U)
    {A B : SmoothRep.{0, uG, uV} ℂ G} (φ : A ⟶ B)
    (hφ : Function.Injective (SmoothRep.hom φ)) :
    Function.Injective (SmoothRep.hom ((normalizedJacquetFunctor U M hU hMU).map φ)) := by
  exact Jacquet.Localization.map_injective_of_smooth U hUc 1 (IsLocallyConstant.const 1)
    M hMU (Jacquet.Localization.isInvariant_one U M hMU) (SmoothRep.hom φ) hφ B.isSmooth

/-- Containment of actual coefficient images gives containment of the images of
the normalized Jacquet maps, by choosing representatives in the actual quotient. -/
theorem normalizedJacquetFunctor_range_le_of_range_le
    (U M : Subgroup G) (hU : IsClosed (U : Set G))
    (hMU : M ≤ Subgroup.normalizer (U : Set G))
    {A B C : SmoothRep.{0, uG, uV} ℂ G} (φ : A ⟶ C) (ψ : B ⟶ C)
    (hφψ : (SmoothRep.hom φ).range ≤ (SmoothRep.hom ψ).range) :
    (SmoothRep.hom ((normalizedJacquetFunctor U M hU hMU).map φ)).range ≤
      (SmoothRep.hom ((normalizedJacquetFunctor U M hU hMU).map ψ)).range := by
  rintro _ ⟨a, rfl⟩
  obtain ⟨v, rfl⟩ := Jacquet.Localization.mk_surjective A.representation U 1 a
  obtain ⟨w, hw⟩ := hφψ (show SmoothRep.hom φ v ∈ (SmoothRep.hom φ).range from ⟨v, rfl⟩)
  refine ⟨Jacquet.Localization.mk B.representation U 1 w, ?_⟩
  change Jacquet.Localization.mk C.representation U 1 (SmoothRep.hom ψ w) =
    Jacquet.Localization.mk C.representation U 1 (SmoothRep.hom φ v)
  exact congrArg (Jacquet.Localization.mk C.representation U 1) hw

/-- Every actual normalized Jacquet class is in one stage whenever the original
coefficient images cover the original representation. No compactness is needed. -/
theorem normalizedJacquetFunctor_cover_of_cover
    (U M : Subgroup G) (hU : IsClosed (U : Set G))
    (hMU : M ≤ Subgroup.normalizer (U : Set G)) {ι : Type uI}
    (A : ι → SmoothRep.{0, uG, uV} ℂ G) (B : SmoothRep.{0, uG, uV} ℂ G)
    (φ : ∀ i, A i ⟶ B) (hcover : ∀ b : B, ∃ i, b ∈ (SmoothRep.hom (φ i)).range) :
    ∀ b : (normalizedJacquetFunctor U M hU hMU).obj B, ∃ i,
      b ∈ (SmoothRep.hom ((normalizedJacquetFunctor U M hU hMU).map (φ i))).range := by
  intro b
  obtain ⟨v, rfl⟩ := Jacquet.Localization.mk_surjective B.representation U 1 b
  obtain ⟨i, a, ha⟩ := hcover v
  refine ⟨i, Jacquet.Localization.mk (A i).representation U 1 a, ?_⟩
  change Jacquet.Localization.mk B.representation U 1 (SmoothRep.hom (φ i) a) =
    Jacquet.Localization.mk B.representation U 1 v
  exact congrArg (Jacquet.Localization.mk B.representation U 1) ha

set_option maxHeartbeats 800000 in
/-- Every vector of the actual composite `i r B` comes from `i r (A i)` for one
stage of a directed covering family of injective maps into `B`. -/
theorem inductionJacquetFunctor_exists_preimage_of_directed_cover
    (h : IsSemidirectDecomposition P M U) (hU : IsClosed (U : Set G))
    [CompactSpace (Induction.LeftQuotient P)]
    (hUc : Jacquet.Localization.IsLimitOfCompactSubgroups U) {ι : Type uI}
    (A : ι → SmoothRep.{0, uG, max uG uV} ℂ G)
    (B : SmoothRep.{0, uG, max uG uV} ℂ G)
    (φ : ∀ i, A i ⟶ B) (hinj : ∀ i, Function.Injective (SmoothRep.hom (φ i)))
    (hdir : Directed (· ≤ ·) (fun i => (SmoothRep.hom (φ i)).range))
    (hcover : ∀ b : B, ∃ i, b ∈ (SmoothRep.hom (φ i)).range)
    (f : (inductionJacquetFunctor.{uG, uV} h hU).obj B) :
    ∃ i, ∃ g : (inductionJacquetFunctor.{uG, uV} h hU).obj (A i),
      SmoothRep.hom ((inductionJacquetFunctor.{uG, uV} h hU).map (φ i)) g = f := by
  apply normalizedInductionFunctor_exists_preimage_of_directed_cover.{uG, max uG uV, uI} h hU
    (fun i => (jacquetFunctor.{uG, max uG uV} h hU).obj (A i))
    ((jacquetFunctor.{uG, max uG uV} h hU).obj B)
    (fun i => (jacquetFunctor.{uG, max uG uV} h hU).map (φ i))
  · intro i
    exact normalizedJacquetFunctor_map_injective U M hU h.levi_le_normalizer hUc (φ i) (hinj i)
  · intro i j
    obtain ⟨k, hik, hjk⟩ := hdir i j
    exact ⟨k,
      normalizedJacquetFunctor_range_le_of_range_le U M hU h.levi_le_normalizer
        (φ i) (φ k) hik,
      normalizedJacquetFunctor_range_le_of_range_le U M hU h.levi_le_normalizer
        (φ j) (φ k) hjk⟩
  · exact normalizedJacquetFunctor_cover_of_cover U M hU h.levi_le_normalizer A B φ hcover

end Langlands.Aubert.General
