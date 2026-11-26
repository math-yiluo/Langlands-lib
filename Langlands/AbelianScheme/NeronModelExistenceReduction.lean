import Langlands.GroupScheme.RelativeIdentityComponent.BaseChange
import Langlands.AbelianScheme.NeronModelExistenceStatement
import Langlands.AbelianScheme.NeronModelFromScheme
import Langlands.AbelianScheme.NeronModelOfWeakNeronModelStatement
import Langlands.AlgebraicGeometry.BirationalGroupLawSolutionStatement
import Langlands.AlgebraicGeometry.Picard.DiscreteValuationRingSelfProductLineBundleExtensionProof

/-! # Néron models from weak Néron models and solutions of birational group laws -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false

namespace Langlands.AbelianScheme

open NeronModelInfra Langlands.AlgebraicGeometry

variable {V K : Type u} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
  [Field K] [Algebra V K] [IsFractionRing V K]

/-- A solution of a birational group law containing the whole model has generic fibre
isomorphic to the abelian variety: the embedding is an open immersion on generic fibres,
proper because the abelian variety is proper, and surjective because its image is dense in
the generic fibre. -/
theorem solution_genericIso {B : AbelianScheme (Spec (CommRingCat.of K))}
    {X : Over (Spec (CommRingCat.of V))}
    (eX : B.X ≅ (Over.pullback (specGenericFibreInclusion V K)).obj X)
    {m : BirationalGroupLaw X.hom} (σ : m.Solution) (hσ : σ.domain = ⊤) :
    Nonempty (B.X ≅ (Over.pullback (specGenericFibreInclusion V K)).obj σ.group.X) := by
  let η := specGenericFibreInclusion V K
  let G := σ.group.X
  have hι : IsIso σ.domain.ι := by
    rw [isIso_iff_isOpenImmersion_and_surjective]
    refine ⟨inferInstance, ⟨fun x => ?_⟩⟩
    have hx : x ∈ σ.domain := by rw [hσ]; trivial
    exact ⟨⟨x, hx⟩, rfl⟩
  let j : X.left ⟶ G.left := inv σ.domain.ι ≫ σ.embedding
  have hj : j ≫ G.hom = X.hom := by
    simp only [j, G, Category.assoc, σ.embedding_comp, IsIso.inv_hom_id_assoc]
  have : IsOpenImmersion σ.embedding := σ.isOpenImmersion_embedding
  have hjo : IsOpenImmersion j := inferInstance
  let jO : X ⟶ G := Over.homMk j hj
  let jK := (Over.pullback η).map jO
  have hsq := Langlands.GroupScheme.RelativeIdentityComponent.overPullback_isPullback η jO
  have hKo : IsOpenImmersion jK.left :=
    MorphismProperty.of_isPullback (P := @IsOpenImmersion) hsq.flip hjo
  -- Properness of the generic fibre map.
  have hηo : IsOpenImmersion η := isOpenImmersion_spec_fractionRing_of_dvr V K
  have : IsProper B.X.hom := B.proper
  have hXKp : IsProper (pullback.snd X.hom η) := by
    have h := Over.w eX.inv
    change eX.inv.left ≫ B.X.hom = pullback.snd X.hom η at h
    rw [← h]
    infer_instance
  have : IsSeparated G.hom := σ.isSeparated
  have hGKs : IsSeparated (pullback.snd G.hom η) := inferInstance
  have hcomp : jK.left ≫ pullback.snd G.hom η = pullback.snd X.hom η := Over.w jK
  have hKp : IsProper jK.left := by
    have : IsProper (jK.left ≫ pullback.snd G.hom η) := by rw [hcomp]; exact hXKp
    exact IsProper.of_comp jK.left (pullback.snd G.hom η)
  -- Surjectivity: the image is closed and contains a generization of every point.
  have hfstG : IsOpenImmersion (pullback.fst G.hom η) := inferInstance
  have hfstX : IsOpenImmersion (pullback.fst X.hom η) := inferInstance
  have hfst : pullback.fst X.hom η ≫ j = jK.left ≫ pullback.fst G.hom η := hsq.w.symm
  have hrange : ∀ q : ↑(pullback G.hom η), ∃ q' ∈ Set.range jK.left, q' ⤳ q := by
    intro q
    let p := (pullback.fst G.hom η).base q
    obtain ⟨y, ⟨x0, rfl⟩, hyp, hyspec⟩ := σ.embedding_dense p
    have hpη : G.hom.base p ∈ Set.range η.base := by
      refine ⟨(pullback.snd G.hom η).base q, ?_⟩
      simp only [p, ← Scheme.Hom.comp_apply, pullback.condition]
    have hyG : σ.embedding.base x0 ∈ Set.range (pullback.fst G.hom η).base := by
      rw [IsOpenImmersion.range_pullbackFst]
      change G.hom.base (σ.embedding.base x0) ∈ η.opensRange
      rw [hyp]
      exact hpη
    obtain ⟨q', hq'⟩ := hyG
    refine ⟨q', ?_, ?_⟩
    · let x1 := σ.domain.ι.base x0
      have hx1 : X.hom.base x1 ∈ Set.range η.base := by
        have : X.hom.base x1 = G.hom.base (σ.embedding.base x0) := by
          show (σ.domain.ι ≫ X.hom).base x0 = (σ.embedding ≫ G.hom).base x0
          rw [σ.embedding_comp]
        rw [this, hyp]
        exact hpη
      have hx1' : x1 ∈ Set.range (pullback.fst X.hom η).base := by
        rw [IsOpenImmersion.range_pullbackFst]
        exact hx1
      obtain ⟨x'', hx''⟩ := hx1'
      refine ⟨x'', (pullback.fst G.hom η).isOpenEmbedding.injective ?_⟩
      rw [hq']
      have key : (jK.left ≫ pullback.fst G.hom η).base x'' = σ.embedding.base x0 := by
        rw [← hfst, Scheme.Hom.comp_apply]
        refine (congrArg j.base hx'').trans ?_
        show (σ.domain.ι ≫ j).base x0 = σ.embedding.base x0
        simp only [j, IsIso.hom_inv_id_assoc]
        rfl
      exact key
    · rw [← (pullback.fst G.hom η).isOpenEmbedding.toIsInducing.specializes_iff, hq']
      exact hyspec
  have hsurj : Function.Surjective jK.left.base := by
    intro q
    obtain ⟨q', hq'r, hq'q⟩ := hrange q
    have hcl : IsClosed (Set.range jK.left.base) := jK.left.isClosedMap.isClosed_range
    exact hcl.closure_subset_iff.mpr (Set.singleton_subset_iff.mpr hq'r)
      (specializes_iff_mem_closure.mp hq'q)
  have hiso : IsIso jK.left := by
    rw [isIso_iff_isOpenImmersion_and_surjective]
    exact ⟨hKo, ⟨hsurj⟩⟩
  exact ⟨eX ≪≫ Over.isoMk (asIso jK.left) hcomp⟩

/-- Weak Néron models, solutions of birational group laws and the construction of the
birational group law on ω-minimal models give Néron models of abelian varieties over
discrete valuation rings. -/
def NeronModelExistenceReductionStatement : Prop :=
  WeakNeronModelExistenceStatement.{u} → BirationalGroupLawSolutionStatement.{u} →
    NeronModelOfWeakNeronModelStatement.{u} → NeronModelExistenceStatement.{u}

/-- The Néron model is the solution of the birational group law on the model supplied by
`NeronModelOfWeakNeronModelStatement`, built from a weak Néron model. -/
theorem neronModelExistenceReduction : NeronModelExistenceReductionStatement.{u} := by
  intro hW hB hN V K _ _ _ _ _ _ B
  obtain ⟨W, hWs, hWsep, hWlft, hWqc, hWe, hWN⟩ := hW V K B
  obtain ⟨X, eX, m, hXs, hXsep, hXlft, hXqc, hXsurj, hgen, hneron⟩ :=
    hN V K B W hWs hWsep hWlft hWqc hWe hWN
  obtain ⟨σ, hσ⟩ := (hB V X.left X.hom hXs hXsep hXlft hXqc hXsurj m).2 hgen
  obtain ⟨e⟩ := solution_genericIso eX σ hσ
  exact ⟨NeronModel.ofScheme σ.group.X (hneron σ hσ) e⟩

end Langlands.AbelianScheme
