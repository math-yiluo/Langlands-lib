import Langlands.Sheaf.Equivariant.AnalyticGSheaves
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Topology.Compactness.Compact

/-!
# Conditional finite subcovers in the analytic étale site

Compactness turns open, jointly surjective point images into finite covering
families. The geometric openness and point-surjectivity inputs remain explicit.
-/

noncomputable section

namespace Langlands.Analytic.SaturatedAtlasPresentation

open CategoryTheory
open Langlands.Sheaf.Equivariant Langlands.Sheaf.Equivariant.TwistedOver

universe u v z

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable {X : LocalizedCategory.{u, v, v} (K := K)}

/-- An open jointly surjective sieve over a compact object contains a finite
family which is still an étale cover. -/
theorem exists_finite_etale_subcover {U : EtaleSite X}
    (hcompact : CompactSpace (localizedSpaceFunctor.obj U.left))
    (S : Sieve U)
    (hopen : ∀ (V : EtaleSite X) (f : V ⟶ U),
      IsOpenMap (localizedSpaceFunctor.map f.left))
    (hpoints : ∀ x : (EtaleSite.points X).obj U,
      ∃ (V : EtaleSite X) (f : V ⟶ U), S f ∧
        x ∈ Set.range ((EtaleSite.points X).map f)) :
    ∃ (n : ℕ) (V : Fin n → EtaleSite X) (f : ∀ i, V i ⟶ U),
      (∀ i, S (f i)) ∧ Sieve.ofArrows V f ∈ etaleTopology X U := by
  classical
  let _ := hcompact
  choose V f hf hx using hpoints
  let W : localizedSpaceFunctor.obj U.left → Set (localizedSpaceFunctor.obj U.left) :=
    fun x => Set.range (localizedSpaceFunctor.map (f x).left)
  have hW : ∀ x, IsOpen (W x) := fun x => (hopen (V x) (f x)).isOpen_range
  have hcover : Set.univ ⊆ ⋃ x, W x := by
    intro x _
    exact Set.mem_iUnion.mpr ⟨x, hx x⟩
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover W hW hcover
  let e := t.equivFin
  let V' : Fin t.card → EtaleSite X := fun i => V (e.symm i).val
  let f' : ∀ i, V' i ⟶ U := fun i => f (e.symm i).val
  refine ⟨t.card, V', f', fun i => hf _, ?_⟩
  apply generate_mem_etaleTopology
  apply ofArrows_mem_etalePrecoverage_iff.mpr
  intro x
  obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.mp (ht (Set.mem_univ x))
  refine ⟨e ⟨y, hy⟩, ?_⟩
  change x ∈ Set.range (localizedSpaceFunctor.map (f (e.symm (e ⟨y, hy⟩)).val).left)
  rw [e.symm_apply_apply]
  exact hxy

/-- The finite-base-cover premise for the twisted étale site follows from
compactness, openness of étale structure maps, and point-surjectivity of covering
sieves in the ordinary étale site. -/
theorem exists_finite_twistedEtale_base_subcover
    {G : Type z} [Group G] (ρ : G →* Aut X)
    (hcompact : IsCompactSpace X)
    (hopen : ∀ U : EtaleSite X, IsOpenMap (localizedSpaceFunctor.map U.hom))
    (hpoints : ∀ ⦃U : EtaleSite X⦄ (S : Sieve U), S ∈ etaleTopology X U →
      ∀ x : (EtaleSite.points X).obj U,
        ∃ (V : EtaleSite X) (f : V ⟶ U), S f ∧
          x ∈ Set.range ((EtaleSite.points X).map f))
    (S : Sieve (base etale ρ))
    (hS : S ∈ Langlands.Sheaf.Equivariant.Analytic.twistedEtaleTopology ρ
      (base etale ρ)) :
    ∃ (n : ℕ) (V : Fin n → TwistedOver etale ρ)
      (f : ∀ i, V i ⟶ base etale ρ),
      (∀ i, S (f i)) ∧ Sieve.ofArrows V f ∈
        Langlands.Sheaf.Equivariant.Analytic.twistedEtaleTopology ρ (base etale ρ) := by
  let S' := Sieve.functorPullback (ι etale ρ) S
  have hS' : S' ∈ etaleTopology X (base etale ρ).obj := hS
  have hopen' : ∀ (V : EtaleSite X) (f : V ⟶ (base etale ρ).obj),
      IsOpenMap (localizedSpaceFunctor.map f.left) := by
    intro V f
    have hf : f.left = V.hom := by
      have hw := MorphismProperty.Over.w f
      change f.left ≫ 𝟙 X = V.hom at hw
      exact (Category.comp_id f.left).symm.trans hw
    change IsOpenMap (localizedSpaceFunctor.map f.left)
    rw [hf]
    exact hopen V
  obtain ⟨n, V, f, hf, hcov⟩ :=
    exists_finite_etale_subcover hcompact.1 S' hopen' (hpoints S' hS')
  refine ⟨n, fun i => (ι etale ρ).obj (V i),
    fun i => (ι etale ρ).map (f i), hf, ?_⟩
  have h := (ι_coverPreserving (ρ := ρ) (etaleTopology X)).cover_preserve hcov
  rw [Sieve.functorPushforward_ofArrows] at h
  exact h

/-- A selected finite covering family contained in the given twisted covering
sieve. Its components include the family and proofs of membership and covering. -/
def finiteTwistedEtaleBaseSubcover
    {G : Type z} [Group G] (ρ : G →* Aut X)
    (hcompact : IsCompactSpace X)
    (hopen : ∀ U : EtaleSite X, IsOpenMap (localizedSpaceFunctor.map U.hom))
    (hpoints : ∀ ⦃U : EtaleSite X⦄ (S : Sieve U), S ∈ etaleTopology X U →
      ∀ x : (EtaleSite.points X).obj U,
        ∃ (V : EtaleSite X) (f : V ⟶ U), S f ∧
          x ∈ Set.range ((EtaleSite.points X).map f))
    (S : Sieve (base etale ρ))
    (hS : S ∈ Langlands.Sheaf.Equivariant.Analytic.twistedEtaleTopology ρ
      (base etale ρ)) :
    Σ (n : ℕ) (V : Fin n → TwistedOver etale ρ),
      {f : ∀ i, V i ⟶ base etale ρ //
        (∀ i, S (f i)) ∧ Sieve.ofArrows V f ∈
          Langlands.Sheaf.Equivariant.Analytic.twistedEtaleTopology ρ (base etale ρ)} :=
  Classical.choice <| by
    obtain ⟨n, V, f, hf, hcov⟩ :=
      exists_finite_twistedEtale_base_subcover ρ hcompact hopen hpoints S hS
    exact ⟨⟨n, V, f, hf, hcov⟩⟩

end Langlands.Analytic.SaturatedAtlasPresentation
