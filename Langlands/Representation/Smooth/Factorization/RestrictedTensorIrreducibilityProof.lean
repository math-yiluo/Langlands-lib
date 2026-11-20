import Langlands.Representation.Smooth.Factorization.RestrictedTensorStatement
import Langlands.Representation.RestrictedTensor.Irreducibility
import Langlands.Representation.Smooth.Schur.Proof

/-!
# Irreducibility of restricted tensor representations

Proof of `Langlands.RestrictedTensorIrreducibilityStatement` (Flath 1979, §2, Example 2).
The quotient at a single index detects proper nonzero local subrepresentations.
For the other implication, admissible Schur supplies the scalar self-intertwiners
required by `RestrictedTensor.representation_isIrreducible`.
-/

noncomputable section

open scoped Classical

universe uK uI uG uV

namespace Langlands.RestrictedTensor

variable {K : Type uK} [Field K] {ι : Type uI} {G : ι → Type uG} [∀ i, Group (G i)]
  {V : ι → Type uV} [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]

/-- A restricted tensor product whose carrier is nonzero has nonzero factors at the
exceptional indices. -/
private theorem nontrivial_of_mem_exceptional (E : Finset ι) (e : ∀ i, V i)
    [Nontrivial (Space K V E e)] {i : ι} (hi : i ∈ E) : Nontrivial (V i) := by
  by_contra h
  rw [not_nontrivial_iff_subsingleton] at h
  obtain ⟨x, hx⟩ := exists_ne (0 : Space K V E e)
  obtain ⟨S, t, rfl⟩ := exists_of E e x
  have hall : ∀ t' : Stage K V S.1, t' = 0 := by
    intro t'
    induction t' using PiTensorProduct.induction_on with
    | smul_tprod c v =>
      have hv : v ⟨i, S.2 hi⟩ = 0 := Subsingleton.elim _ _
      rw [(PiTensorProduct.tprod K).map_coord_zero ⟨i, S.2 hi⟩ hv, smul_zero]
    | add a b ha hb => rw [ha, hb, add_zero]
  exact hx (by rw [hall t, map_zero])

/-- An irreducible restricted tensor representation has irreducible local factors when its
reference vectors are nonzero outside `E`. A proper nonzero subrepresentation `W` of `ρ j`
would give a proper nonzero kernel for the map obtained by replacing `V j` with `V j ⧸ W`. -/
theorem isIrreducible_of_isIrreducible_representation (H : ∀ i, Subgroup (G i))
    (ρ : ∀ i, Representation K (G i) (V i)) (E : Finset ι) (e : ∀ i, V i)
    (he : ∀ i ∉ E, ∀ g ∈ H i, ρ i g (e i) = e i) (hne : ∀ i ∉ E, e i ≠ 0)
    (hirr : (representation H ρ E e he).IsIrreducible) (j : ι) : (ρ j).IsIrreducible := by
  have hsp : Nontrivial (Space K V E e) := by
    by_contra h
    rw [not_nontrivial_iff_subsingleton] at h
    exact (bot_ne_top : (⊥ : Subrepresentation (representation H ρ E e he)) ≠ ⊤)
      (Subrepresentation.ext (Subsingleton.elim _ _))
  have hV : ∀ i, Nontrivial (V i) := fun i => by
    by_cases hi : i ∈ E
    · exact nontrivial_of_mem_exceptional (K := K) E e hi
    · exact ⟨⟨e i, 0, hne i hi⟩⟩
  have hz : ∀ i, ∃ z : V i, z ≠ 0 := fun i => exists_ne 0
  choose z hz using hz
  refine { exists_pair_ne := ⟨⊥, ⊤, fun h => ?_⟩, eq_bot_or_eq_top := fun W => ?_ }
  · obtain ⟨x, hx⟩ := exists_ne (0 : V j)
    have h' : (⊥ : Submodule K (V j)) = ⊤ := congrArg Subrepresentation.toSubmodule h
    have hx' : x ∈ (⊥ : Submodule K (V j)) := h' ▸ Submodule.mem_top
    exact hx ((Submodule.mem_bot K).mp hx')
  by_contra hW
  push Not at hW
  obtain ⟨hWb, hWt⟩ := hW
  -- the quotient data
  let N : ∀ i, Submodule K (V i) := Function.update (fun _ => ⊥) j W.toSubmodule
  have hNj : N j = W.toSubmodule := Function.update_self j _ _
  have hNi : ∀ i, i ≠ j → N i = ⊥ := fun i hi => Function.update_of_ne hi _ _
  have hN : ∀ i (g : G i), N i ≤ (N i).comap (ρ i g) := by
    intro i g
    by_cases hi : i = j
    · subst hi
      rw [hNj]
      exact fun x hx => W.apply_mem_toSubmodule g hx
    · rw [hNi i hi]
      exact bot_le
  let σ : ∀ i, Representation K (G i) (V i ⧸ N i) := fun i => (ρ i).quotient (N i) (hN i)
  let f : ∀ i, V i →ₗ[K] V i ⧸ N i := fun i => (N i).mkQ
  let e' : ∀ i, V i ⧸ N i := fun i => f i (e i)
  let E' : Finset ι := insert j E
  have hσf : ∀ i (g : G i) (x : V i), σ i g (f i x) = f i (ρ i g x) := fun i g x => rfl
  have he' : ∀ i ∉ E', ∀ g ∈ H i, σ i g (e' i) = e' i := by
    intro i hi g hg
    rw [hσf, he i (fun hiE => hi (Finset.mem_insert_of_mem hiE)) g hg]
  have hmk : ∀ i, i ≠ j → ∀ x : V i, x ≠ 0 → f i x ≠ 0 := by
    intro i hi x hx h0
    apply hx
    have h1 : x ∈ N i := (Submodule.Quotient.mk_eq_zero (N i)).mp h0
    rw [hNi i hi] at h1
    exact (Submodule.mem_bot K).mp h1
  have hne' : ∀ i ∉ E', e' i ≠ 0 := fun i hi =>
    hmk i (fun h => hi (h ▸ Finset.mem_insert_self j E)) (e i)
      (hne i (fun hiE => hi (Finset.mem_insert_of_mem hiE)))
  have hf : ∀ᶠ i in Filter.cofinite, f i (e i) = e' i := Filter.Eventually.of_forall fun _ => rfl
  have hint : ∀ i (g : G i), (f i).comp (ρ i g) = (σ i g).comp (f i) :=
    fun i g => LinearMap.ext fun x => (hσf i g x).symm
  let Φ := map E E' e e' f hf
  let U : Subrepresentation (representation H ρ E e he) :=
    { toSubmodule := LinearMap.ker Φ
      apply_mem_toSubmodule := fun g x hx => by
        rw [LinearMap.mem_ker] at hx ⊢
        have h := LinearMap.congr_fun
          (map_intertwines H ρ σ E E' e e' he he' f hf hint g) x
        rw [LinearMap.comp_apply, LinearMap.comp_apply, hx, map_zero] at h
        exact h }
  -- the stage containing `j`
  let S : Index E := ⟨E', Finset.subset_insert j E⟩
  have hjS : j ∈ S.1 := Finset.mem_insert_self j E
  have hpres : ∀ i ∉ S.1, f i (e i) = e' i := fun _ _ => rfl
  have hΦpure : ∀ v : ∀ i : S.1, V i,
      Φ (pure E e S v) = pure E' e' ⟨S.1, le_rfl⟩ (fun i => f i (v i)) :=
    fun v => map_pure_of_preserves E E' e e' f hf S le_rfl hpres v
  have hpure_ne : ∀ v : ∀ i : S.1, V i, (∀ i, v i ≠ 0) → pure (K := K) E e S v ≠ 0 := by
    intro v hv h0
    apply stage_tprod_ne_zero (K := K) S.1 v hv
    apply of_injective E e hne S
    rw [map_zero]
    exact h0
  rcases hirr.eq_bot_or_eq_top U with hU | hU
  · -- `U = ⊥` is impossible: a pure tensor with a nonzero coordinate in `W` lies in the kernel
    obtain ⟨w, hwW, hw0⟩ := (Submodule.ne_bot_iff _).mp
      (fun h => hWb (Subrepresentation.ext h))
    let v : ∀ i : S.1, V i := Function.update (fun i => z i) ⟨j, hjS⟩ w
    have hv : ∀ i, v i ≠ 0 := by
      intro i
      by_cases hi : i = ⟨j, hjS⟩
      · subst hi
        simpa only [v, Function.update_self] using hw0
      · simpa only [v, Function.update_of_ne hi] using hz i
    have hker : pure E e S v ∈ U.toSubmodule := by
      change Φ (pure E e S v) = 0
      rw [hΦpure]
      have hcoord : f j (v ⟨j, hjS⟩) = 0 := by
        simp only [v, Function.update_self]
        exact (Submodule.Quotient.mk_eq_zero (N j)).mpr (hNj ▸ hwW)
      exact congrArg (of K _ E' e' ⟨S.1, le_rfl⟩)
        ((PiTensorProduct.tprod K).map_coord_zero ⟨j, hjS⟩ hcoord) |>.trans (map_zero _)
    rw [congrArg Subrepresentation.toSubmodule hU] at hker
    exact hpure_ne v hv ((Submodule.mem_bot K).mp hker)
  · -- `U = ⊤` is impossible: a pure tensor with coordinate outside `W` is not in the kernel
    obtain ⟨w, hwW⟩ : ∃ w : V j, w ∉ W.toSubmodule := by
      by_contra h
      push Not at h
      exact hWt (Subrepresentation.ext (eq_top_iff.mpr fun x _ => h x))
    let v : ∀ i : S.1, V i := Function.update (fun i => z i) ⟨j, hjS⟩ w
    have hfv : ∀ i : S.1, f i (v i) ≠ 0 := by
      intro i
      by_cases hi : i = ⟨j, hjS⟩
      · subst hi
        simp only [v, Function.update_self]
        intro h0
        exact hwW (hNj ▸ (Submodule.Quotient.mk_eq_zero (N j)).mp h0)
      · simp only [v, Function.update_of_ne hi]
        exact hmk i (fun h => hi (Subtype.ext h)) _ (hz i)
    have hmem : pure E e S v ∈ U.toSubmodule := by
      rw [congrArg Subrepresentation.toSubmodule hU]
      exact Submodule.mem_top
    change Φ (pure E e S v) = 0 at hmem
    rw [hΦpure] at hmem
    apply stage_tprod_ne_zero (K := K) (V := fun i => V i ⧸ N i) S.1 (fun i => f i (v i)) hfv
    apply of_injective (K := K) E' e' hne' ⟨S.1, le_rfl⟩
    rw [map_zero]
    exact hmem

end Langlands.RestrictedTensor

namespace Langlands

open RestrictedTensor

/-- The restricted tensor representation of admissible local representations is irreducible
exactly when every local representation is irreducible (Flath 1979, §2, Example 2). -/
theorem restrictedTensorIrreducibility :
    Langlands.RestrictedTensorIrreducibilityStatement.{uI, uG, uV} := by
  intro ι G _ _ _ _ _ _ H V _ _ ρ E r hr _ hadm _
  constructor
  · intro h i
    exact isIrreducible_of_isIrreducible_representation H ρ E r.family _ r.family_nonzero h i
  · intro h
    let := h
    exact representation_isIrreducible H ρ E r.family _ r.family_nonzero
      (fun i φ => (admissibleSchur_scalarEndomorphism (ρ i) (hadm i) (h i) φ).exists)

end Langlands
