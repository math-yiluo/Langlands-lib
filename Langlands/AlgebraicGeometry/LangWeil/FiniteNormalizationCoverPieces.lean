import Langlands.AlgebraicGeometry.LangWeil.FiniteNormalizationCoverStatement
import Langlands.AlgebraicGeometry.LangWeil.FiniteNormalizationCoverAlgebra

/-! # Single pieces of finite normalization covers

A piece records the data of one index of `FiniteNormalizationCover`, with the fibre
dimension bound replaced by a chain of specializations in its own fibre. Finitely many
pieces that cover all field-valued points give a `FiniteNormalizationCover`. -/

universe u

open CategoryTheory CategoryTheory.Limits
open _root_.AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.LangWeil.NormalizationCoverConstruction

/-- A chain of `n + 1` distinct points, each specializing to the next, bounds the
topological Krull dimension of a `T₀` space from below by `n`. -/
theorem le_topologicalKrullDim_of_chain {T : Type*} [TopologicalSpace T] [T0Space T] {n : ℕ}
    (x : Fin (n + 1) → T)
    (hx : ∀ i : Fin n, x i.castSucc ⤳ x i.succ ∧ x i.castSucc ≠ x i.succ) :
    (n : WithBot ℕ∞) ≤ topologicalKrullDim T := by
  let c : Fin (n + 1) → TopologicalSpace.IrreducibleCloseds T := fun i =>
    ⟨closure {x i.rev}, isIrreducible_singleton.closure, isClosed_closure⟩
  have hc : StrictMono c := by
    refine Fin.strictMono_iff_lt_succ.mpr fun i => ?_
    obtain ⟨h₁, h₂⟩ := hx i.rev
    have hle : closure {x i.rev.succ} ⊆ closure {x i.rev.castSucc} :=
      specializes_iff_closure_subset.mp h₁
    refine lt_of_le_of_ne ?_ ?_
    · change closure {x i.castSucc.rev} ⊆ closure {x i.succ.rev}
      rw [Fin.rev_castSucc, Fin.rev_succ]
      exact hle
    · intro h
      have h' : closure {x i.castSucc.rev} = closure {x i.succ.rev} := congrArg (fun Z => Z.1) h
      rw [Fin.rev_castSucc, Fin.rev_succ] at h'
      refine h₂ (h₁.antisymm ?_).eq
      rw [specializes_iff_closure_subset, h']
  exact Order.LTSeries.length_le_krullDim (LTSeries.mk n c hc)

/-- One piece of a finite normalization cover of `f`. Instead of the fibre dimension of `f`,
it records a chain of `dimension + 1` points specializing in its own fibre over each base
point. -/
structure Piece {S X : Scheme.{u}} (f : X ⟶ S) where
  /-- The affine base stratum. -/
  base : Scheme.{u}
  /-- The source stratum. -/
  source : Scheme.{u}
  baseAffine : IsAffine base
  /-- The immersion of the base stratum. -/
  baseMap : base ⟶ S
  baseImmersion : IsImmersion baseMap
  /-- The immersion of the source stratum. -/
  sourceMap : source ⟶ X
  sourceImmersion : IsImmersion sourceMap
  /-- The relative dimension of the normalization. -/
  dimension : ℕ
  /-- The finite surjective normalization map. -/
  normalization : source ⟶ AffineSpace (ULift.{u} (Fin dimension)) base
  normalizationFinite : IsFinite normalization
  normalizationSurjective : Function.Surjective normalization
  comm : normalization ≫ (AffineSpace (ULift.{u} (Fin dimension)) base ↘ base) ≫ baseMap =
    sourceMap ≫ f
  fibreChain : ∀ t : base, ∃ x : Fin (dimension + 1) → source,
    (∀ i, (normalization ≫ (AffineSpace (ULift.{u} (Fin dimension)) base ↘ base)) (x i) = t) ∧
    ∀ i : Fin dimension, x i.castSucc ⤳ x i.succ ∧ x i.castSucc ≠ x i.succ

namespace Piece

variable {S X : Scheme.{u}} {f : X ⟶ S}

/-- The fibre chain of a piece gives the dimension bound on the fibre of `f`. -/
theorem dimension_le (p : Piece f) (t : p.base) :
    (p.dimension : WithBot ℕ∞) ≤ topologicalKrullDim (f.fiber (p.baseMap t)) := by
  obtain ⟨x, hx, hchain⟩ := p.fibreChain t
  have := p.sourceImmersion
  have hmem : ∀ i, p.sourceMap (x i) ∈ f ⁻¹' {p.baseMap t} := by
    intro i
    rw [Set.mem_preimage, Set.mem_singleton_iff, ← Scheme.Hom.comp_apply, ← p.comm, ← hx i]
    simp only [Scheme.Hom.comp_apply]
  let e := (f.fiberHomeo (p.baseMap t)).symm
  refine le_topologicalKrullDim_of_chain (fun i => e ⟨p.sourceMap (x i), hmem i⟩) fun i => ?_
  obtain ⟨h₁, h₂⟩ := hchain i
  refine ⟨Specializes.map ?_ e.continuous, ?_⟩
  · rw [subtype_specializes_iff]
    exact h₁.map p.sourceMap.continuous
  · intro h
    exact h₂ (p.sourceMap.isEmbedding.injective (congrArg Subtype.val (e.injective h)))

/-- Transport a piece along immersions of source and base. -/
def comp {S' X' : Scheme.{u}} {f' : X' ⟶ S'} (p : Piece f') (a : X' ⟶ X) [IsImmersion a]
    (b : S' ⟶ S) [IsImmersion b] (h : f' ≫ b = a ≫ f) : Piece f where
  base := p.base
  source := p.source
  baseAffine := p.baseAffine
  baseMap := p.baseMap ≫ b
  baseImmersion := by have := p.baseImmersion; infer_instance
  sourceMap := p.sourceMap ≫ a
  sourceImmersion := by have := p.sourceImmersion; infer_instance
  dimension := p.dimension
  normalization := p.normalization
  normalizationFinite := p.normalizationFinite
  normalizationSurjective := p.normalizationSurjective
  comm := by
    have := p.comm
    simp only [← Category.assoc] at this ⊢
    rw [this, Category.assoc, h, Category.assoc]
  fibreChain := p.fibreChain

@[simp] lemma comp_sourceMap {S' X' : Scheme.{u}} {f' : X' ⟶ S'} (p : Piece f') (a : X' ⟶ X)
    [IsImmersion a] (b : S' ⟶ S) [IsImmersion b] (h : f' ≫ b = a ≫ f) :
    (p.comp a b h).sourceMap = p.sourceMap ≫ a := rfl

@[simp] lemma comp_source {S' X' : Scheme.{u}} {f' : X' ⟶ S'} (p : Piece f') (a : X' ⟶ X)
    [IsImmersion a] (b : S' ⟶ S) [IsImmersion b] (h : f' ≫ b = a ≫ f) :
    (p.comp a b h).source = p.source := rfl

end Piece

/-- Finitely many pieces through which every field-valued point factors form a finite
normalization cover. -/
theorem nonempty_cover_of_pieces {S X : Scheme.{u}} {f : X ⟶ S} (s : Set (Piece f))
    (hs : s.Finite)
    (hcov : ∀ (K : Type u) [Field K] (x : Spec (.of K) ⟶ X),
      ∃ p ∈ s, ∃ z : Spec (.of K) ⟶ p.source, z ≫ p.sourceMap = x) :
    Nonempty (FiniteNormalizationCover f) := by
  have := hs.fintype
  let e := Fintype.equivFin s
  let P : Fin (Fintype.card s) → Piece f := fun i => (e.symm i).1
  exact ⟨{
    count := Fintype.card s
    base := fun i => (P i).base
    source := fun i => (P i).source
    baseAffine := fun i => (P i).baseAffine
    baseMap := fun i => (P i).baseMap
    baseImmersion := fun i => (P i).baseImmersion
    sourceMap := fun i => (P i).sourceMap
    sourceImmersion := fun i => (P i).sourceImmersion
    dimension := fun i => (P i).dimension
    normalization := fun i => (P i).normalization
    normalizationFinite := fun i => (P i).normalizationFinite
    normalizationSurjective := fun i => (P i).normalizationSurjective
    «over» := fun i => (P i).comm
    covers := by
      intro K _ x
      obtain ⟨p, hp, z, hz⟩ := hcov K x
      obtain ⟨i, hi⟩ : ∃ i, P i = p := ⟨e ⟨p, hp⟩, by simp [P]⟩
      subst hi
      exact ⟨i, z, hz⟩
    dimension_le := fun i t => (P i).dimension_le t }⟩

/-- Noetherian induction over primes: if each prime `Q` has an element `g ∉ Q` and an index
covering every prime above `Q` avoiding `g`, finitely many indices cover every prime. -/
theorem exists_finite_cover_of_prime {A : Type*} [CommRing A] [IsNoetherianRing A]
    {ι : Type*} (cov : ι → Ideal A → Prop)
    (H : ∀ Q : Ideal A, Q.IsPrime → ∃ g ∉ Q, ∃ i, ∀ P : Ideal A, P.IsPrime → Q ≤ P → g ∉ P →
      cov i P) :
    ∃ s : Set ι, s.Finite ∧ ∀ P : Ideal A, P.IsPrime → ∃ i ∈ s, cov i P := by
  suffices h : ∀ I : Ideal A, ∃ s : Set ι, s.Finite ∧
      ∀ P : Ideal A, P.IsPrime → I ≤ P → ∃ i ∈ s, cov i P by
    obtain ⟨s, hs, h⟩ := h ⊥
    exact ⟨s, hs, fun P hP => h P hP bot_le⟩
  have hlt : ∀ (I : Ideal A) (a : A), a ∉ I → I < I ⊔ Ideal.span {a} := fun I a ha =>
    left_lt_sup.mpr fun h => ha (h (Ideal.mem_span_singleton_self a))
  have hle : ∀ (I P : Ideal A) (a : A), I ≤ P → a ∈ P → I ⊔ Ideal.span {a} ≤ P :=
    fun I P a hI ha => sup_le hI ((Ideal.span_singleton_le_iff_mem P).mpr ha)
  intro I
  induction I using WellFoundedGT.induction with
  | _ I ih =>
  by_cases htop : I = ⊤
  · refine ⟨∅, Set.finite_empty, fun P hP hIP => ?_⟩
    exact absurd (top_le_iff.mp (htop ▸ hIP)) hP.ne_top
  by_cases hprime : I.IsPrime
  · obtain ⟨g, hg, i, hi⟩ := H I hprime
    obtain ⟨s, hs, hcov⟩ := ih (I ⊔ Ideal.span {g}) (hlt I g hg)
    refine ⟨insert i s, hs.insert i, fun P hP hIP => ?_⟩
    by_cases hgP : g ∈ P
    · obtain ⟨j, hj, hc⟩ := hcov P hP (hle I P g hIP hgP)
      exact ⟨j, Set.mem_insert_of_mem _ hj, hc⟩
    · exact ⟨i, Set.mem_insert _ _, hi P hP hIP hgP⟩
  · obtain ⟨a, b, hab, ha, hb⟩ : ∃ a b, a * b ∈ I ∧ a ∉ I ∧ b ∉ I := by
      by_contra hc
      push Not at hc
      exact hprime ⟨htop, fun {a b} hab => by
        by_contra h
        push Not at h
        exact h.2 (hc a b hab h.1)⟩
    obtain ⟨s, hs, hcs⟩ := ih (I ⊔ Ideal.span {a}) (hlt I a ha)
    obtain ⟨t, ht, hct⟩ := ih (I ⊔ Ideal.span {b}) (hlt I b hb)
    refine ⟨s ∪ t, hs.union ht, fun P hP hIP => ?_⟩
    rcases hP.mem_or_mem (hIP hab) with h | h
    · obtain ⟨j, hj, hc⟩ := hcs P hP (hle I P a hIP h)
      exact ⟨j, Or.inl hj, hc⟩
    · obtain ⟨j, hj, hc⟩ := hct P hP (hle I P b hIP h)
      exact ⟨j, Or.inr hj, hc⟩

end Langlands.AlgebraicGeometry.LangWeil.NormalizationCoverConstruction
