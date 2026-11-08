import Langlands.Automorphic.OperatorCompactCompatibility
import Langlands.Global.AdelesSecondCountable
import Langlands.Global.ArchimedeanEnvelopingFiltration

/-! # Countable dimension of irreducible operator realizations -/

noncomputable section
universe u
set_option autoImplicit false

namespace Langlands.Automorphic

open Langlands.Global Cardinal Module Langlands.FiniteVectors

variable {F : Type u} [Field F] [NumberField F] {n : ℕ}

local instance countableDimGroup1 : AddCommGroup (RationalInvariantFunctions F n) :=
  Submodule.addCommGroup _
local instance countableDimGroup2 : AddCommGroup (ContinuousRationalFunctions F n) :=
  Submodule.addCommGroup _
local instance countableDimGroup3 : AddCommGroup (FiniteSmoothRationalFunctions F n) :=
  Submodule.addCommGroup _
local instance countableDimGroup4 : AddCommGroup (AutomorphicForms F n) := Submodule.addCommGroup _
local instance countableDimGroup5 : AddCommGroup (StableAutomorphicFunctions F n) :=
  Submodule.addCommGroup _

variable (F n) in
/-- The finite adelic matrix group is second countable. -/
theorem finiteAdelicGL_secondCountableTopology :
    SecondCountableTopology (FiniteAdelicGL F n) := by
  have := finiteAdeles_secondCountableTopology F
  have : SecondCountableTopology (Matrix (Fin n) (Fin n) (FiniteAdeles F)) :=
    inferInstanceAs (SecondCountableTopology (Fin n → Fin n → FiniteAdeles F))
  have : SecondCountableTopology (Matrix (Fin n) (Fin n) (FiniteAdeles F))ᵐᵒᵖ :=
    (MulOpposite.opHomeomorph (M := Matrix (Fin n) (Fin n) (FiniteAdeles F))).symm.isEmbedding
      |>.secondCountableTopology
  exact Units.isEmbedding_embedProduct.secondCountableTopology

variable (F n) in
/-- An open subgroup of the finite adelic matrix group has countably many cosets. -/
theorem finiteAdelicGL_countable_quotient (U : OpenSubgroup (FiniteAdelicGL F n)) :
    Countable (FiniteAdelicGL F n ⧸ U.toSubgroup) := by
  have := finiteAdelicGL_secondCountableTopology F n
  obtain ⟨D, hDc, hDd⟩ := TopologicalSpace.exists_countable_dense (FiniteAdelicGL F n)
  have : Countable D := hDc.to_subtype
  refine Function.Surjective.countable
    (f := fun d : D => ((d : FiniteAdelicGL F n) : FiniteAdelicGL F n ⧸ U.toSubgroup))
    fun q => ?_
  have hU : IsOpen ((fun x => q.out⁻¹ * x) ⁻¹' (U : Set (FiniteAdelicGL F n))) :=
    U.isOpen.preimage (continuous_const_mul _)
  obtain ⟨d, hd, hdU⟩ := hDd.exists_mem_open hU ⟨q.out, by simp⟩
  refine ⟨⟨d, hd⟩, ?_⟩
  have e : ((q.out : FiniteAdelicGL F n) : FiniteAdelicGL F n ⧸ U.toSubgroup) = d :=
    QuotientGroup.eq.mpr hdU
  rw [QuotientGroup.out_eq'] at e
  exact e.symm

namespace OperatorRealization

variable (S : OperatorRealization F n)
local instance countableDimGroup6 : AddCommGroup S.Space := Submodule.addCommGroup _

set_option maxHeartbeats 1000000 in
/-- The finite adelic orbit of a realized vector is countable. -/
theorem countable_finiteOrbit (v : S.Space) :
    (Set.range fun d : FiniteAdelicGL F n => S.finiteRepresentation d v).Countable := by
  obtain ⟨U, hU⟩ := S.finiteRepresentation_isSmooth v
  have := finiteAdelicGL_countable_quotient F n U
  let f : FiniteAdelicGL F n ⧸ U.toSubgroup → S.Space :=
    Quotient.lift (fun d => S.finiteRepresentation d v) (by
      intro a b hab
      have hab' : a⁻¹ * b ∈ U.toSubgroup := QuotientGroup.leftRel_apply.mp hab
      have h := hU ⟨a⁻¹ * b, hab'⟩
      change S.finiteRepresentation (a⁻¹ * b) v = v at h
      have e1 : S.finiteRepresentation (a * (a⁻¹ * b)) =
          S.finiteRepresentation a * S.finiteRepresentation (a⁻¹ * b) := map_mul _ _ _
      calc S.finiteRepresentation a v
          = S.finiteRepresentation a (S.finiteRepresentation (a⁻¹ * b) v) :=
            (congrArg (S.finiteRepresentation a) h).symm
        _ = S.finiteRepresentation (a * (a⁻¹ * b)) v := (LinearMap.congr_fun e1 v).symm
        _ = S.finiteRepresentation b v :=
            congrArg (fun g => S.finiteRepresentation g v) (mul_inv_cancel_left a b))
  refine (Set.countable_range f).mono ?_
  rintro _ ⟨d, rfl⟩
  exact ⟨QuotientGroup.mk d, rfl⟩

/-- A subspace stable under the three operator families is stable under the generated
operator algebra. -/
theorem representation_mem_of_stable (P : Submodule ℂ S.Space)
    (hd : ∀ d, ∀ v ∈ P, S.finiteRepresentation d v ∈ P)
    (hk : ∀ k, ∀ v ∈ P, S.compactRepresentation k v ∈ P)
    (he : ∀ a, ∀ v ∈ P, S.envelopingAction a v ∈ P)
    (a : automorphicOperatorAlgebra F n) : ∀ v ∈ P, S.representation a v ∈ P := by
  obtain ⟨a, ha⟩ := a
  induction ha using Algebra.adjoin_induction with
  | mem b hb =>
    rcases hb with (⟨d, rfl⟩ | ⟨k, rfl⟩) | ⟨e, rfl⟩
    · exact hd d
    · exact hk k
    · exact he e
  | algebraMap c =>
    intro v hv
    have h : S.representation ⟨algebraMap ℂ _ c, Subalgebra.algebraMap_mem _ c⟩ v = c • v :=
      rfl
    rw [h]
    exact P.smul_mem c hv
  | add b₁ b₂ h₁ h₂ ih₁ ih₂ =>
    intro v hv
    have h : S.representation ⟨b₁ + b₂, Subalgebra.add_mem _ h₁ h₂⟩ v =
        S.representation ⟨b₁, h₁⟩ v + S.representation ⟨b₂, h₂⟩ v := rfl
    rw [h]
    exact P.add_mem (ih₁ v hv) (ih₂ v hv)
  | mul b₁ b₂ h₁ h₂ ih₁ ih₂ =>
    intro v hv
    have h : S.representation ⟨b₁ * b₂, Subalgebra.mul_mem _ h₁ h₂⟩ v =
        S.representation ⟨b₁, h₁⟩ (S.representation ⟨b₂, h₂⟩ v) := rfl
    rw [h]
    exact ih₁ _ (ih₂ v hv)

set_option maxHeartbeats 2000000 in
/-- An irreducible actual operator realization has countable complex dimension. -/
theorem rank_le_aleph0 (hS : S.IsIrreducible) : Module.rank ℂ S.Space ≤ ℵ₀ := by
  classical
  have hnt : Nontrivial (Subrepresentation S.representation) := hS.toNontrivial
  obtain ⟨x₀, hx₀⟩ : ∃ x : S.Space, x ≠ 0 := by
    by_contra! h
    apply (bot_ne_top : (⊥ : Subrepresentation S.representation) ≠ ⊤)
    apply Subrepresentation.ext
    change (⊥ : Submodule ℂ S.Space) = ⊤
    rw [eq_comm, eq_bot_iff]
    intro x _
    exact (Submodule.mem_bot ℂ).mpr (h x)
  have hκ : ∀ v : S.Space, ∃ t : Set S.Space, t.Finite ∧
      Submodule.span ℂ t = orbitSpan S.compactRepresentation v := by
    intro v
    have : Module.Finite ℂ (orbitSpan S.compactRepresentation v) :=
      S.compactRepresentation_isFiniteVector v
    obtain ⟨t, ht⟩ := (Module.Finite.iff_fg.mp this)
    exact ⟨t, t.finite_toSet, ht⟩
  let ev : S.Space → ArchimedeanGL.EnvelopingAlgebra F n →ₗ[ℂ] S.Space := fun v =>
    LinearMap.applyₗ v ∘ₗ S.envelopingAction.toLinearMap
  have hE : ∀ (v : S.Space) (d : ℕ), ∃ t : Set S.Space, t.Finite ∧
      Submodule.span ℂ t = (ArchimedeanGL.envelopingDegreeFiltration F n d).map (ev v) := by
    intro v d
    have hfg : (ArchimedeanGL.envelopingDegreeFiltration F n d).FG :=
      Module.Finite.iff_fg.mp inferInstance
    obtain ⟨t, ht⟩ := hfg.map (ev v)
    exact ⟨t, t.finite_toSet, ht⟩
  choose tκ htκ htκspan using hκ
  choose tE htE htEspan using hE
  let step : Set S.Space → Set S.Space := fun s =>
    s ∪ (⋃ v ∈ s, Set.range fun d : FiniteAdelicGL F n => S.finiteRepresentation d v) ∪
      (⋃ v ∈ s, tκ v) ∪ (⋃ v ∈ s, ⋃ d : ℕ, tE v d)
  have hstep_count : ∀ s : Set S.Space, s.Countable → (step s).Countable := by
    intro s hs
    refine ((hs.union (hs.biUnion fun v _ => S.countable_finiteOrbit v)).union
      (hs.biUnion fun v _ => (htκ v).countable)).union
      (hs.biUnion fun v _ => Set.countable_iUnion fun d => (htE v d).countable)
  have hstep_sub : ∀ s : Set S.Space, s ⊆ step s := fun s x hx =>
    Or.inl (Or.inl (Or.inl hx))
  let seq : ℕ → Set S.Space := fun m => Nat.rec {x₀} (fun _ t => step t) m
  have hseq_succ : ∀ m, seq (m + 1) = step (seq m) := fun _ => rfl
  have hseq_count : ∀ m, (seq m).Countable := by
    intro m
    induction m with
    | zero => exact Set.countable_singleton x₀
    | succ m ih => rw [hseq_succ]; exact hstep_count _ ih
  let sAll : Set S.Space := ⋃ m, seq m
  have hsAll : sAll.Countable := Set.countable_iUnion hseq_count
  let P : Submodule ℂ S.Space := Submodule.span ℂ sAll
  have hseqP : ∀ m, Submodule.span ℂ (seq m) ≤ P := fun m =>
    Submodule.span_mono (Set.subset_iUnion seq m)
  have hstable : ∀ (f : S.Space →ₗ[ℂ] S.Space),
      (∀ m, ∀ v ∈ seq m, f v ∈ Submodule.span ℂ (seq (m + 1))) → ∀ v ∈ P, f v ∈ P := by
    intro f hf v hv
    induction hv using Submodule.span_induction with
    | mem w hw =>
      obtain ⟨m, hm⟩ := Set.mem_iUnion.mp hw
      exact hseqP (m + 1) (hf m w hm)
    | zero => rw [map_zero]; exact P.zero_mem
    | add x y _ _ hx hy => rw [map_add]; exact P.add_mem hx hy
    | smul c x _ hx => rw [map_smul]; exact P.smul_mem c hx
  have hPd : ∀ d, ∀ v ∈ P, S.finiteRepresentation d v ∈ P := by
    intro d
    apply hstable
    intro m v hv
    apply Submodule.subset_span
    rw [hseq_succ]
    exact Or.inl (Or.inl (Or.inr (Set.mem_biUnion hv ⟨d, rfl⟩)))
  have hPk : ∀ k, ∀ v ∈ P, S.compactRepresentation k v ∈ P := by
    intro k
    apply hstable
    intro m v hv
    have h1 : S.compactRepresentation k v ∈ Submodule.span ℂ (tκ v) := by
      rw [htκspan]
      exact action_mem_orbitSpan _ k v
    refine Submodule.span_mono ?_ h1
    rw [hseq_succ]
    intro w hw
    exact Or.inl (Or.inr (Set.mem_biUnion hv hw))
  have hPe : ∀ a, ∀ v ∈ P, S.envelopingAction a v ∈ P := by
    intro a
    apply hstable
    intro m v hv
    obtain ⟨d, hd⟩ := ArchimedeanGL.exists_mem_envelopingDegreeFiltration F n a
    have h1 : S.envelopingAction a v ∈ Submodule.span ℂ (tE v d) := by
      rw [htEspan]
      exact ⟨a, hd, rfl⟩
    refine Submodule.span_mono ?_ h1
    rw [hseq_succ]
    intro w hw
    exact Or.inr (Set.mem_biUnion hv (Set.mem_iUnion.mpr ⟨d, hw⟩))
  let Prep : Subrepresentation S.representation :=
    ⟨P, fun a v hv => S.representation_mem_of_stable P hPd hPk hPe a v hv⟩
  have hPtop : Prep = ⊤ := by
    rcases hS.eq_bot_or_eq_top Prep with h | h
    · exfalso
      have hx : x₀ ∈ Prep.toSubmodule :=
        hseqP 0 (Submodule.subset_span (Set.mem_singleton x₀))
      rw [h] at hx
      exact hx₀ ((Submodule.mem_bot ℂ).mp hx)
    · exact h
  have hPeq : P = ⊤ := congrArg Subrepresentation.toSubmodule hPtop
  calc Module.rank ℂ S.Space = Module.rank ℂ (⊤ : Submodule ℂ S.Space) := (rank_top ℂ S.Space).symm
    _ = Module.rank ℂ P := by rw [hPeq]
    _ ≤ #sAll := rank_span_le sAll
    _ ≤ ℵ₀ := hsAll.le_aleph0

end OperatorRealization

end Langlands.Automorphic
