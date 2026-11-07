import Langlands.Representation.Jacquet.Localization
import Langlands.Representation.Jacquet.IwahoriStablePairingData
import Langlands.Representation.Compact.ProjectionProof
import Langlands.Representation.Smooth.Contragredient.LawsProof

/-! # Evaluating a stable-lift pairing at translates

Let `P ℓ w` pair smooth functionals with vectors through the `U`-coinvariants of the
contragredient and the `O`-coinvariants of the representation. A vector `x` has
*stable lifts* (`HasStableLifts`) when, for every small compact open `K` with opposite
Iwahori contractions, its `O`-class has a `K`-fixed lift on which `P` is evaluation
against `K`-fixed functionals. For such `x` and each functional `ℓ` there is
a compact subset `C ⊆ O` such that `P ℓ (ρ t x) = ℓ(ρ t x)` for every `t` that
normalizes `O`, commutes with `M`, satisfies the translation invariance of `P`, and
conjugates `C` into the stabilizer of `ℓ`. This is the core of Renard VI.9.6.4 and
VI.9.6.5.
-/

noncomputable section

namespace Langlands.Aubert.General

universe uG uV

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]

open Jacquet

/-- The translate `ρ̃(t⁻¹) ℓ` is fixed by `c` when `t c t⁻¹` fixes `ℓ`. -/
theorem smoothContragredient_conj_fixed (ρ : Representation ℂ G V) (t c : G)
    (ℓ : SmoothDual ρ) (h : smoothContragredient ρ (t * c * t⁻¹) ℓ = ℓ) :
    smoothContragredient ρ c (smoothContragredient ρ t⁻¹ ℓ) =
      smoothContragredient ρ t⁻¹ ℓ := by
  have e : c * t⁻¹ = t⁻¹ * (t * c * t⁻¹) := by group
  rw [← Module.End.mul_apply, ← map_mul, e, map_mul, Module.End.mul_apply, h]

/-- A functional fixed by `o` vanishes on the generator `ρ o w - w`. -/
theorem smoothDualPairing_sub_eq_zero_of_fixed (ρ : Representation ℂ G V) (o : G)
    (ℓ : SmoothDual ρ) (h : smoothContragredient ρ o ℓ = ℓ) (w : V) :
    smoothDualPairing ρ ℓ (ρ o w - w) = 0 := by
  have hinv := smoothDualPairing_invariant (ρ := ρ) o ℓ w
  rw [h] at hinv
  rw [map_sub, hinv, sub_self]

/-- The vector `x` has stable lifts for the pairing `P`: there is an open subgroup `W`
such that every compact open `K ≤ W` with Iwahori contractions for `g` in the order
`(U, M, O)` and for `g⁻¹` in the order `(O, M, U)` has a `K`-fixed vector `v` with the
same `O`-class as `x` and with `P Λ v = Λ(v)` for every `K`-fixed smooth functional `Λ`. -/
def HasStableLifts (ρ : Representation ℂ G V) (U M O : Subgroup G) (g : G)
    (P : SmoothDual ρ → V → ℂ) (x : V) : Prop :=
  ∃ W : OpenSubgroup G, ∀ K : OpenSubgroup G, IsCompact (K : Set G) →
    IsIwahoriContraction K U M O g → IsIwahoriContraction K O M U g⁻¹ → K ≤ W →
      ∃ v ∈ fixedVectors ρ K.toSubgroup,
        Jacquet.Localization.mk ρ O 1 v = Jacquet.Localization.mk ρ O 1 x ∧
        ∀ Λ ∈ fixedVectors (smoothContragredient ρ) K.toSubgroup,
          P Λ v = smoothDualPairing ρ Λ v

/-- The asymptotic evaluation of a stable-lift pairing.

`P ℓ w` depends only on the `O`-class of `w` and the `U`-class of `ℓ`. Suppose that
compact open subgroups with both Iwahori contractions are cofinal and that `x` has
stable lifts (`HasStableLifts`). Then for every `ℓ` there is a compact `C ⊆ O` such that
every `t`
normalizing `O`, commuting with `M`, conjugating `C` into the stabilizer of `ℓ` and
satisfying `P (ρ̃(t⁻¹) ℓ') w = P ℓ' (ρ t w)` has `P ℓ (ρ t x) = ℓ(ρ t x)`. -/
theorem exists_compact_forall_stableLiftPairing_translate_eq
    (ρ : Representation ℂ G V) (U M O : Subgroup G) (hO : IsClosed (O : Set G)) (g : G)
    (hBasis : HasOppositeIwahoriContractionBasis U M O g)
    (P : SmoothDual ρ → V → ℂ)
    (hPO : ∀ (ℓ : SmoothDual ρ) (w w' : V),
      Jacquet.Localization.mk ρ O 1 w = Jacquet.Localization.mk ρ O 1 w' → P ℓ w = P ℓ w')
    (hPU : ∀ (ℓ ℓ' : SmoothDual ρ) (w : V),
      Jacquet.Localization.mk (smoothContragredient ρ) U 1 ℓ =
        Jacquet.Localization.mk (smoothContragredient ρ) U 1 ℓ' → P ℓ w = P ℓ' w)
    (x : V) (hx : HasStableLifts ρ U M O g P x) (ℓ : SmoothDual ρ) :
    ∃ C : Set G, IsCompact C ∧ C ⊆ O ∧
      ∀ t : G, t ∈ Subgroup.normalizer O → (∀ m ∈ M, t * m = m * t) →
        (∀ c ∈ C, smoothContragredient ρ (t * c * t⁻¹) ℓ = ℓ) →
        (∀ (ℓ' : SmoothDual ρ) (w : V), P (smoothContragredient ρ t⁻¹ ℓ') w = P ℓ' (ρ t w)) →
          P ℓ (ρ t x) = smoothDualPairing ρ ℓ (ρ t x) := by
  classical
  obtain ⟨L, hL⟩ := isSmooth_smoothContragredient ρ ℓ
  obtain ⟨W, hW⟩ := hx
  obtain ⟨K, hKc, hKsub, hUp, hLow⟩ := hBasis ((W ⊓ L : OpenSubgroup G) : Set G)
    (W ⊓ L).isOpen (W ⊓ L).one_mem
  have hKW : K ≤ W := fun k hk => (hKsub hk).1
  have hKL : K ≤ L := fun k hk => (hKsub hk).2
  obtain ⟨v, hv, hvx, hvP⟩ := hW K hKc hUp hLow hKW
  have hrel : x - v ∈ Jacquet.Localization.relations ρ O 1 :=
    (Jacquet.Localization.mk_eq_iff ρ O 1 x v).1 hvx.symm
  obtain ⟨n, f, e, he⟩ := Submodule.mem_span_set'.1 hrel
  choose uv huv using fun i => (e i).property
  let C : Set G := ((K : Set G) ∩ (O : Set G)) ∪ Set.range (fun i => ((uv i).1 : G))
  have hKclosed : IsClosed (K : Set G) := K.isClosed
  refine ⟨C, (hKc.inter_right hO).union (Set.finite_range _).isCompact, ?_, ?_⟩
  · rintro c (hc | ⟨i, rfl⟩)
    · exact hc.2
    · exact (uv i).1.property
  intro t htO htM hfix hinv
  set ℓt : SmoothDual ρ := smoothContragredient ρ t⁻¹ ℓ with hℓt
  have hfixC : ∀ c ∈ C, smoothContragredient ρ c ℓt = ℓt := fun c hc =>
    smoothContragredient_conj_fixed ρ t c ℓ (hfix c hc)
  have hfixM : ∀ m ∈ K.toSubgroup ⊓ M, smoothContragredient ρ m ℓt = ℓt := by
    intro m hm
    have hmt : t * m = m * t := htM m hm.2
    have e' : m * t⁻¹ = t⁻¹ * m := by
      rw [mul_inv_eq_iff_eq_mul, mul_assoc, ← hmt, inv_mul_cancel_left]
    rw [hℓt, ← Module.End.mul_apply, ← map_mul, e', map_mul, Module.End.mul_apply,
      apply_eq_of_mem_fixedVectors (smoothContragredient ρ) hL (hKL hm.1)]
  -- `ℓ(ρ t x) = ℓt(x)` and `ℓt(x) = ℓt(v)`.
  have hpair : smoothDualPairing ρ ℓ (ρ t x) = smoothDualPairing ρ ℓt x := by
    rw [hℓt]
    change _ = smoothDualPairing ρ ℓ (ρ t⁻¹⁻¹ x)
    rw [inv_inv]
  have hker : smoothDualPairing ρ ℓt (x - v) = 0 := by
    rw [← he, map_sum]
    apply Finset.sum_eq_zero
    intro i _
    rw [map_smul, ← huv i]
    have h0 := smoothDualPairing_sub_eq_zero_of_fixed ρ ((uv i).1 : G) ℓt
      (hfixC _ (Or.inr ⟨i, rfl⟩)) (uv i).2
    simp only [MonoidHom.one_apply, Units.val_one, one_smul]
    rw [h0, smul_zero]
  have hxv : smoothDualPairing ρ ℓt x = smoothDualPairing ρ ℓt v := by
    rw [map_sub] at hker
    exact sub_eq_zero.mp hker
  -- `P ℓ (ρ t x) = P ℓ (ρ t v) = P ℓt v`.
  have hinvθ : Jacquet.Localization.IsInvariant O (Subgroup.normalizer O) le_rfl
      (1 : O →* ℂˣ) := fun _ _ => rfl
  have htv : Jacquet.Localization.mk ρ O 1 (ρ t x) = Jacquet.Localization.mk ρ O 1 (ρ t v) := by
    rw [Jacquet.Localization.mk_eq_iff, ← map_sub]
    exact Jacquet.Localization.relations_stable ρ O 1 (Subgroup.normalizer O) le_rfl hinvθ
      ⟨t, htO⟩ hrel
  rw [hPO ℓ _ _ htv, ← hinv ℓ v, hpair, hxv]
  -- Average `ℓt` over `K`.
  let Λ : SmoothDual ρ :=
    Compact.averageMap (smoothContragredient ρ) (isSmooth_smoothContragredient ρ) K hKc ℓt
  have hΛ : Λ ∈ fixedVectors (smoothContragredient ρ) K.toSubgroup :=
    Compact.averageMap_mem_fixedVectors _ _ K hKc ℓt
  have hmk : Jacquet.Localization.mk (smoothContragredient ρ) U 1 Λ =
      Jacquet.Localization.mk (smoothContragredient ρ) U 1 ℓt := by
    apply map_averageMap_of_forall_eq
    intro k
    obtain ⟨l, hl, m, hm, o, ho, hk⟩ := hLow.factor k.val k.property
    rw [hk, map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply,
      hfixC o (Or.inl ⟨ho.1, ho.2⟩), hfixM m hm]
    have h1 := Jacquet.Localization.mk_apply_subgroup (smoothContragredient ρ) U 1 ⟨l, hl.2⟩ ℓt
    simpa using h1
  have heval : smoothDualPairing ρ Λ v = smoothDualPairing ρ ℓt v := by
    apply map_averageMap_of_forall_eq (smoothContragredient ρ)
      (isSmooth_smoothContragredient ρ) K hKc ((smoothDualPairing ρ).flip v)
    intro k
    change smoothDualPairing ρ ℓt (ρ (k : G)⁻¹ v) = smoothDualPairing ρ ℓt v
    rw [apply_eq_of_mem_fixedVectors ρ hv (K.toSubgroup.inv_mem k.property)]
  rw [hPU ℓt Λ v hmk.symm, hvP Λ hΛ, heval]

end Langlands.Aubert.General
