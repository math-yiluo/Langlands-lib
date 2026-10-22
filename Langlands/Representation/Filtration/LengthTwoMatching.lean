import Langlands.Representation.Filtration.ObjectDefinitions
import Langlands.Representation.Filtration.LengthCriterionProof
import Langlands.Representation.Filtration.LengthTwoMatchingStatement

/-! Matching composition factors of two representations whose subrepresentation
lattices carry strictly monotone counts bounded by two. -/

namespace Langlands

namespace LengthTwo

universe uK uG uV uW

open Representation
open LengthCriterionProof (quotientRep)

variable {k : Type*} [Field k] {G : Type uG} [Monoid G]
  {V : Type uV} {W : Type uW} [AddCommGroup V] [Module k V]
  [AddCommGroup W] [Module k W]
  {ρ : Representation k G V} {σ : Representation k G W}

/-- The preimage of a subrepresentation under an intertwining map. -/
def comap (f : ρ.IntertwiningMap σ) (S : Subrepresentation σ) : Subrepresentation ρ where
  toSubmodule := S.toSubmodule.comap f.toLinearMap
  apply_mem_toSubmodule g v hv := by
    change f (ρ g v) ∈ S.toSubmodule
    rw [f.isIntertwining]
    exact S.apply_mem_toSubmodule g hv

theorem mem_comap (f : ρ.IntertwiningMap σ) (S : Subrepresentation σ) (v : V) :
    v ∈ comap f S ↔ f v ∈ S := Iff.rfl

/-- An intertwining map carrying the upper step onto the upper step, with exactly
the lower step as the preimage of the lower step, identifies the two successive
quotients. -/
theorem nonempty_gradedEquiv (f : ρ.IntertwiningMap σ)
    {S T : Subrepresentation ρ} {S' T' : Subrepresentation σ}
    (hT : ∀ v ∈ T.toSubmodule, f v ∈ T'.toSubmodule)
    (hsurj : ∀ w ∈ T'.toSubmodule, ∃ v ∈ T.toSubmodule, f v = w)
    (hker : ∀ v ∈ T.toSubmodule, f v ∈ S'.toSubmodule ↔ v ∈ S.toSubmodule) :
    Nonempty ((quotientRep S T).Equiv (quotientRep S' T')) := by
  let L : T.toSubmodule →ₗ[k]
      (T'.toSubmodule ⧸ S'.toSubmodule.comap T'.toSubmodule.subtype) :=
    (S'.toSubmodule.comap T'.toSubmodule.subtype).mkQ ∘ₗ f.toLinearMap.restrict hT
  have hL : S.toSubmodule.comap T.toSubmodule.subtype ≤ LinearMap.ker L := by
    intro v hv
    rw [LinearMap.mem_ker]
    change Submodule.Quotient.mk _ = 0
    rw [Submodule.Quotient.mk_eq_zero]
    exact (hker v v.2).2 hv
  let Φ := (S.toSubmodule.comap T.toSubmodule.subtype).liftQ L hL
  have hΦ (v : T.toSubmodule) :
      Φ (Submodule.Quotient.mk v) =
        Submodule.Quotient.mk ⟨f v, hT v v.2⟩ := rfl
  let Ψ : (quotientRep S T).IntertwiningMap (quotientRep S' T') :=
    { toLinearMap := Φ
      isIntertwining' := by
        intro g
        apply LinearMap.ext
        intro x
        obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ x
        change Φ (Submodule.Quotient.mk (T.toRepresentation g v)) =
          (quotientRep S' T') g (Φ (Submodule.Quotient.mk v))
        rw [hΦ, hΦ]
        change Submodule.Quotient.mk _ = Submodule.Quotient.mk _
        congr 1
        apply Subtype.ext
        exact IntertwiningMap.isIntertwining _ _ f g v }
  refine ⟨Ψ.ofBijective ⟨?_, ?_⟩⟩
  · intro x y hxy
    obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    obtain ⟨w, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    change Φ (Submodule.Quotient.mk v) = Φ (Submodule.Quotient.mk w) at hxy
    rw [hΦ, hΦ, Submodule.Quotient.eq] at hxy
    rw [Submodule.Quotient.eq]
    change ((v - w : T.toSubmodule) : V) ∈ S.toSubmodule
    apply (hker _ (v - w).2).1
    have hxy' : f v - f w ∈ S'.toSubmodule := hxy
    simpa [map_sub] using hxy'
  · intro y
    obtain ⟨w, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    obtain ⟨v, hv, hvw⟩ := hsurj w w.2
    refine ⟨Submodule.Quotient.mk ⟨v, hv⟩, ?_⟩
    change Φ (Submodule.Quotient.mk _) = _
    rw [hΦ]
    congr 1
    exact Subtype.ext hvw

/-- An actual representation equivalence preserves irreducibility. -/
theorem isIrreducible_of_equiv (e : ρ.Equiv σ) (h : ρ.IsIrreducible) :
    σ.IsIrreducible := by
  rw [Representation.irreducible_iff_isSimpleModule_asModule] at h ⊢
  exact (LinearMap.isSimpleModule_iff_of_bijective
    (Representation.IntertwiningMap.equivLinearMapAsModule ρ σ e.toIntertwiningMap)
    e.bijective).1 h

/-- A covering pair of subrepresentations has an irreducible successive quotient. -/
theorem isIrreducible_gradedRep_of_covBy {S T : Subrepresentation ρ} (h : S ⋖ T) :
    (quotientRep S T).IsIrreducible := by
  have hle : S ≤ T := h.le
  obtain ⟨v, hvT, hvS⟩ : ∃ v ∈ T.toSubmodule, v ∉ S.toSubmodule := by
    by_contra hcon
    push Not at hcon
    exact h.lt.ne (le_antisymm hle (fun v hv => hcon v hv))
  let p := S.toSubmodule.comap T.toSubmodule.subtype
  have hnt : (⊥ : Subrepresentation (quotientRep S T)) ≠ ⊤ := by
    intro hbt
    have hmem : (Submodule.Quotient.mk ⟨v, hvT⟩ : T.toSubmodule ⧸ p) ∈
        (⊤ : Subrepresentation (quotientRep S T)).toSubmodule := Submodule.mem_top
    rw [← hbt] at hmem
    change (Submodule.Quotient.mk ⟨v, hvT⟩ : T.toSubmodule ⧸ p) ∈
      (⊥ : Submodule k (T.toSubmodule ⧸ p)) at hmem
    rw [Submodule.mem_bot, Submodule.Quotient.mk_eq_zero] at hmem
    exact hvS hmem
  have : Nontrivial (Subrepresentation (quotientRep S T)) := ⟨⟨⊥, ⊤, hnt⟩⟩
  refine ⟨fun U => ?_⟩
  -- The preimage of `U` in the ambient representation.
  let U' : Subrepresentation ρ :=
    { toSubmodule := (U.toSubmodule.comap p.mkQ).map T.toSubmodule.subtype
      apply_mem_toSubmodule := by
        intro g x hx
        obtain ⟨y, hy, rfl⟩ := hx
        refine ⟨T.toRepresentation g y, ?_, rfl⟩
        exact U.apply_mem_toSubmodule g hy }
  have hSU : S ≤ U' := by
    intro x hx
    refine ⟨⟨x, hle hx⟩, ?_, rfl⟩
    change Submodule.Quotient.mk _ ∈ U.toSubmodule
    rw [(Submodule.Quotient.mk_eq_zero p).2 hx]
    exact U.toSubmodule.zero_mem
  have hUT : U' ≤ T := by
    intro x hx
    obtain ⟨y, -, rfl⟩ := hx
    exact y.2
  rcases h.eq_or_eq hSU hUT with hU | hU
  · left
    apply Subrepresentation.toSubmodule_injective
    apply le_antisymm _ bot_le
    intro x hx
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    rw [Submodule.mem_bot, Submodule.Quotient.mk_eq_zero]
    have : (y : V) ∈ U' := ⟨y, hx, rfl⟩
    rw [hU] at this
    exact this
  · right
    apply Subrepresentation.toSubmodule_injective
    apply le_antisymm le_top
    intro x _
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    have : (y : V) ∈ U' := by rw [hU]; exact y.2
    obtain ⟨z, hz, hzy⟩ := this
    have hzy' : z = y := Subtype.ext hzy
    subst hzy'
    exact hz

/-- The graded pieces of a filtration of `Rep.of ρ` are the successive quotients
of its consecutive steps. -/
theorem gradedRepresentation_ρ {n : ℕ} (s : ObjectRepFiltration (Rep.of ρ) n) (i : Fin n) :
    (s.gradedRepresentation i).ρ =
      quotientRep (s.subrepresentation i.castSucc) (s.subrepresentation i.succ) := rfl

/-- A filtration whose consecutive steps are covering pairs has simple factors. -/
theorem hasSimpleFactors_of_covBy {n : ℕ} (s : ObjectRepFiltration (Rep.of ρ) n)
    (h : ∀ i : Fin n, s.subrepresentation i.castSucc ⋖ s.subrepresentation i.succ) :
    s.HasSimpleFactors :=
  fun i => isIrreducible_gradedRep_of_covBy (h i)

/-- The filtration `0 ⊆ ρ` with the whole representation as its only factor. -/
def oneStep (ρ : Representation k G V) : ObjectRepFiltration (Rep.of ρ) 1 :=
  ObjectRepFiltration.ofSubrepresentations ![⊥, ⊤]
    (by
      intro i j hij
      fin_cases i <;> fin_cases j <;> simp_all)
    rfl rfl

/-- The filtration `0 ⊆ K ⊆ ρ`. -/
def twoStep (K : Subrepresentation ρ) : ObjectRepFiltration (Rep.of ρ) 2 :=
  ObjectRepFiltration.ofSubrepresentations ![⊥, K, ⊤]
    (by
      intro i j hij
      fin_cases i <;> fin_cases j <;> simp_all [Fin.le_def])
    rfl rfl

theorem oneStep_hasSimpleFactors (h : (⊥ : Subrepresentation ρ) ⋖ ⊤) :
    (oneStep ρ).HasSimpleFactors := by
  intro i
  fin_cases i
  exact isIrreducible_gradedRep_of_covBy h

theorem twoStep_hasSimpleFactors {K : Subrepresentation ρ} (h₁ : ⊥ ⋖ K) (h₂ : K ⋖ ⊤) :
    (twoStep K).HasSimpleFactors := by
  intro i
  fin_cases i
  · exact isIrreducible_gradedRep_of_covBy h₁
  · exact isIrreducible_gradedRep_of_covBy h₂

theorem equiv_symm_apply_apply (φ : ρ.Equiv σ) (v : V) : φ.symm (φ v) = v :=
  φ.toLinearEquiv.symm_apply_apply v

theorem equiv_apply_symm_apply (φ : ρ.Equiv σ) (w : W) : φ (φ.symm w) = w :=
  φ.toLinearEquiv.apply_symm_apply w

/-- Transport a filtration along an equivalence of representations. -/
def transport {n : ℕ} (φ : ρ.Equiv σ) (s : ObjectRepFiltration (Rep.of ρ) n) :
    ObjectRepFiltration (Rep.of σ) n :=
  ObjectRepFiltration.ofSubrepresentations
    (fun i => comap φ.symm.toIntertwiningMap (s.subrepresentation i))
    (fun _ _ hij _ hw => s.monotone_subrepresentation hij hw)
    (by
      apply Subrepresentation.toSubmodule_injective
      apply le_antisymm _ bot_le
      intro w hw
      have hw' : φ.symm w ∈ s.subrepresentation 0 := hw
      rw [ObjectRepFiltration.subrepresentation_zero] at hw'
      have h0 : φ.symm w = 0 := (Submodule.mem_bot k).1 hw'
      rw [Submodule.mem_bot, ← equiv_apply_symm_apply φ w, h0, map_zero])
    (by
      apply Subrepresentation.toSubmodule_injective
      apply le_antisymm le_top
      intro w _
      change φ.symm w ∈ s.subrepresentation (Fin.last n)
      rw [ObjectRepFiltration.subrepresentation_last]
      exact Submodule.mem_top)

/-- Equivalent representations have the same factors, given a composition series
of one of them. -/
theorem haveSameJordanHolderFactors_of_equiv {n : ℕ} (φ : ρ.Equiv σ)
    (s : ObjectRepFiltration (Rep.of ρ) n) (hs : s.HasSimpleFactors) :
    HaveSameJordanHolderFactors (Rep.of ρ) (Rep.of σ) := by
  have he : ∀ i : Fin n, Nonempty ((s.gradedRepresentation i).ρ.Equiv
      ((transport φ s).gradedRepresentation i).ρ) := by
    intro i
    rw [gradedRepresentation_ρ, gradedRepresentation_ρ]
    apply nonempty_gradedEquiv φ.toIntertwiningMap
    · intro v hv
      change φ.symm (φ v) ∈ (s.subrepresentation i.succ).toSubmodule
      rw [equiv_symm_apply_apply]
      exact hv
    · intro w hw
      exact ⟨φ.symm w, hw, equiv_apply_symm_apply φ w⟩
    · intro v _
      change φ.symm (φ v) ∈ (s.subrepresentation i.castSucc).toSubmodule ↔ _
      rw [equiv_symm_apply_apply]
  refine ⟨n, s, transport φ s, hs, fun i => ?_, 1, fun i => he i⟩
  obtain ⟨e⟩ := he i
  exact isIrreducible_of_equiv e (hs i)

theorem mem_bot_iff (v : V) : v ∈ (⊥ : Subrepresentation ρ) ↔ v = 0 :=
  Submodule.mem_bot k

theorem mem_top (v : V) : v ∈ (⊤ : Subrepresentation ρ) :=
  Submodule.mem_top

/-- A nonzero intertwining map has a nonzero source. -/
theorem bot_ne_top_of_ne_zero (A : ρ.IntertwiningMap σ) (hA : A ≠ 0) :
    (⊥ : Subrepresentation ρ) ≠ ⊤ := by
  intro h
  apply hA
  ext v
  have hv : v ∈ (⊥ : Subrepresentation ρ) := h ▸ mem_top v
  rw [mem_bot_iff] at hv
  simp [hv]

/-- A nonzero intertwining map does not have the whole source as kernel. -/
theorem ker_ne_top_of_ne_zero (A : ρ.IntertwiningMap σ) (hA : A ≠ 0) : A.ker ≠ ⊤ := by
  intro h
  apply hA
  ext v
  have hv : v ∈ A.ker := h ▸ mem_top v
  exact (IntertwiningMap.mem_ker _ _ A v).1 hv

/-- A nonzero intertwining map has nonzero range. -/
theorem range_ne_bot_of_ne_zero (A : ρ.IntertwiningMap σ) (hA : A ≠ 0) : A.range ≠ ⊥ := by
  intro h
  apply hA
  ext v
  have hv : A v ∈ A.range := (IntertwiningMap.mem_range _ _ A _).2 ⟨v, rfl⟩
  rw [h, mem_bot_iff] at hv
  exact hv

section Count

variable {μ : Subrepresentation ρ → ℕ}

theorem count_pos (hμ : StrictMono μ) (hμ0 : μ ⊥ = 0) {S : Subrepresentation ρ}
    (hS : S ≠ ⊥) : 0 < μ S := by
  have := hμ (bot_lt_iff_ne_bot.2 hS)
  omega

theorem eq_bot_of_count_eq_zero (hμ : StrictMono μ) (hμ0 : μ ⊥ = 0)
    {S : Subrepresentation ρ} (h : μ S = 0) : S = ⊥ := by
  by_contra hS
  have := count_pos hμ hμ0 hS
  omega

/-- A strict inclusion raising a strictly monotone count by at most one is a
covering pair. -/
theorem covBy_of_count (hμ : StrictMono μ) {S T : Subrepresentation ρ} (hST : S < T)
    (h : μ T ≤ μ S + 1) : S ⋖ T :=
  ⟨hST, fun _ h₁ h₂ => by
    have := hμ h₁
    have := hμ h₂
    omega⟩

/-- A nonzero representation with a strictly monotone count, vanishing at zero and
at most two on the whole representation, has a composition series. -/
theorem exists_series (hμ : StrictMono μ) (hμ0 : μ ⊥ = 0) (hμ2 : μ ⊤ ≤ 2)
    (hnt : (⊥ : Subrepresentation ρ) ≠ ⊤) :
    ∃ n, ∃ s : ObjectRepFiltration (Rep.of ρ) n, s.HasSimpleFactors := by
  by_cases h : ∃ K : Subrepresentation ρ, ⊥ < K ∧ K < ⊤
  · obtain ⟨K, h₁, h₂⟩ := h
    have := hμ h₁
    have := hμ h₂
    exact ⟨2, twoStep K, twoStep_hasSimpleFactors (covBy_of_count hμ h₁ (by omega))
      (covBy_of_count hμ h₂ (by omega))⟩
  · exact ⟨1, oneStep ρ, oneStep_hasSimpleFactors
      ⟨bot_lt_iff_ne_bot.2 hnt.symm, fun U h₁ h₂ => h ⟨U, h₁, h₂⟩⟩⟩

end Count

/-- **Length-two matching.** Let `ρ` and `σ` carry strictly monotone counts on their
subrepresentations, vanishing at zero and at most two on the whole representation,
and let `A : ρ → σ` and `A' : σ → ρ` be nonzero intertwining maps along which the
counts are additive. Suppose a count-one subrepresentation on which `A` (or `A'`)
does not vanish forces `ρ ≃ σ`. Then `ρ` and `σ` have the same composition factors
with multiplicities. -/
theorem haveSameJordanHolderFactors_of_count_le_two
    (μ : Subrepresentation ρ → ℕ) (ν : Subrepresentation σ → ℕ)
    (hμ : StrictMono μ) (hν : StrictMono ν) (hμ0 : μ ⊥ = 0) (hν0 : ν ⊥ = 0)
    (hμ2 : μ ⊤ ≤ 2) (hν2 : ν ⊤ ≤ 2)
    (A : ρ.IntertwiningMap σ) (A' : σ.IntertwiningMap ρ) (hA0 : A ≠ 0) (hA'0 : A' ≠ 0)
    (hA : μ ⊤ = μ A.ker + ν A.range) (hA' : ν ⊤ = ν A'.ker + μ A'.range)
    (hX : ∀ S : Subrepresentation ρ, μ S = 1 → (∃ v ∈ S, A v ≠ 0) → Nonempty (ρ.Equiv σ))
    (hY : ∀ S' : Subrepresentation σ, ν S' = 1 → (∃ w ∈ S', A' w ≠ 0) →
      Nonempty (ρ.Equiv σ)) :
    HaveSameJordanHolderFactors (Rep.of ρ) (Rep.of σ) := by
  have hntρ := bot_ne_top_of_ne_zero A hA0
  have hntσ := bot_ne_top_of_ne_zero A' hA'0
  by_cases hE : Nonempty (ρ.Equiv σ)
  · obtain ⟨φ⟩ := hE
    obtain ⟨n, s, hs⟩ := exists_series hμ hμ0 hμ2 hntρ
    exact haveSameJordanHolderFactors_of_equiv φ s hs
  -- Without an equivalence, `A` and `A'` kill every subrepresentation of count one.
  have hX' : ∀ S, μ S = 1 → S ≤ A.ker := by
    intro S hS v hv
    by_contra hv'
    exact hE (hX S hS ⟨v, hv, hv'⟩)
  have hY' : ∀ S', ν S' = 1 → S' ≤ A'.ker := by
    intro S' hS' w hw
    by_contra hw'
    exact hE (hY S' hS' ⟨w, hw, hw'⟩)
  have hkA := ker_ne_top_of_ne_zero A hA0
  have hkA' := ker_ne_top_of_ne_zero A' hA'0
  -- Both representations have count exactly two.
  have hμtop : μ ⊤ = 2 := by
    have := count_pos hμ hμ0 hntρ.symm
    by_contra h
    exact hkA (top_le_iff.1 (hX' ⊤ (by omega)))
  have hνtop : ν ⊤ = 2 := by
    have := count_pos hν hν0 hntσ.symm
    by_contra h
    exact hkA' (top_le_iff.1 (hY' ⊤ (by omega)))
  -- Neither map is surjective, since a surjection would be an equivalence.
  have hrA : A.range ≠ ⊤ := by
    intro h
    rw [h, hμtop, hνtop] at hA
    have hk : A.ker = ⊥ := eq_bot_of_count_eq_zero hμ hμ0 (by omega)
    apply hE
    refine ⟨A.ofBijective ⟨fun x y hxy => ?_, fun w => ?_⟩⟩
    · have hxy' : x - y ∈ A.ker := (IntertwiningMap.mem_ker _ _ A _).2 (by simp [map_sub, hxy])
      rw [hk, mem_bot_iff, sub_eq_zero] at hxy'
      exact hxy'
    · have hw : w ∈ A.range := h ▸ mem_top w
      exact (IntertwiningMap.mem_range _ _ A w).1 hw
  have hrA' : A'.range ≠ ⊤ := by
    intro h
    rw [h, hμtop, hνtop] at hA'
    have hk : A'.ker = ⊥ := eq_bot_of_count_eq_zero hν hν0 (by omega)
    apply hE
    refine ⟨(A'.ofBijective ⟨fun x y hxy => ?_, fun w => ?_⟩).symm⟩
    · have hxy' : x - y ∈ A'.ker := (IntertwiningMap.mem_ker _ _ A' _).2 (by simp [map_sub, hxy])
      rw [hk, mem_bot_iff, sub_eq_zero] at hxy'
      exact hxy'
    · have hw : w ∈ A'.range := h ▸ mem_top w
      exact (IntertwiningMap.mem_range _ _ A' w).1 hw
  -- Hence all four kernels and ranges have count one.
  have hνrA : ν A.range = 1 := by
    have := count_pos hν hν0 (range_ne_bot_of_ne_zero A hA0)
    have := hν (lt_top_iff_ne_top.2 hrA)
    omega
  have hμrA' : μ A'.range = 1 := by
    have := count_pos hμ hμ0 (range_ne_bot_of_ne_zero A' hA'0)
    have := hμ (lt_top_iff_ne_top.2 hrA')
    omega
  have hμkA : μ A.ker = 1 := by omega
  have hνkA' : ν A'.ker = 1 := by omega
  -- The range of each map is the kernel of the other.
  have h₁ : A.range = A'.ker := by
    rcases (hY' _ hνrA).lt_or_eq with h | h
    · have := hν h
      omega
    · exact h
  have h₂ : A'.range = A.ker := by
    rcases (hX' _ hμrA').lt_or_eq with h | h
    · have := hμ h
      omega
    · exact h
  have hbk : (⊥ : Subrepresentation ρ) < A.ker := by
    rw [bot_lt_iff_ne_bot]
    intro h
    rw [h, hμ0] at hμkA
    omega
  have hbk' : (⊥ : Subrepresentation σ) < A'.ker := by
    rw [bot_lt_iff_ne_bot]
    intro h
    rw [h, hν0] at hνkA'
    omega
  refine ⟨2, twoStep A.ker, twoStep A'.ker,
    twoStep_hasSimpleFactors (covBy_of_count hμ hbk (by omega))
      (covBy_of_count hμ (lt_top_iff_ne_top.2 hkA) (by omega)),
    twoStep_hasSimpleFactors (covBy_of_count hν hbk' (by omega))
      (covBy_of_count hν (lt_top_iff_ne_top.2 hkA') (by omega)),
    Equiv.swap 0 1, ?_⟩
  rw [Fin.forall_fin_two, Equiv.swap_apply_left, Equiv.swap_apply_right]
  constructor
  · -- `A'` identifies `σ / ker A'` with `ker A = range A'`.
    change Nonempty ((quotientRep ⊥ A.ker).Equiv (quotientRep A'.ker ⊤))
    obtain ⟨e⟩ := nonempty_gradedEquiv A' (S := A'.ker) (T := ⊤) (S' := ⊥) (T' := A.ker)
      (fun w _ => by
        change A' w ∈ A.ker
        rw [← h₂]
        exact (IntertwiningMap.mem_range _ _ A' _).2 ⟨w, rfl⟩)
      (fun v hv => by
        have hv' : v ∈ A'.range := h₂ ▸ hv
        obtain ⟨w, hw⟩ := (IntertwiningMap.mem_range _ _ A' v).1 hv'
        exact ⟨w, mem_top w, hw⟩)
      (fun w _ => by
        change A' w ∈ (⊥ : Subrepresentation ρ) ↔ w ∈ A'.ker
        rw [mem_bot_iff, IntertwiningMap.mem_ker])
    exact ⟨e.symm⟩
  · -- `A` identifies `ρ / ker A` with `ker A' = range A`.
    change Nonempty ((quotientRep A.ker ⊤).Equiv (quotientRep ⊥ A'.ker))
    exact nonempty_gradedEquiv A (S := A.ker) (T := ⊤) (S' := ⊥) (T' := A'.ker)
      (fun v _ => by
        change A v ∈ A'.ker
        rw [← h₁]
        exact (IntertwiningMap.mem_range _ _ A _).2 ⟨v, rfl⟩)
      (fun w hw => by
        have hw' : w ∈ A.range := h₁ ▸ hw
        obtain ⟨v, hv⟩ := (IntertwiningMap.mem_range _ _ A w).1 hw'
        exact ⟨v, mem_top v, hv⟩)
      (fun v _ => by
        change A v ∈ (⊥ : Subrepresentation σ) ↔ v ∈ A.ker
        rw [mem_bot_iff, IntertwiningMap.mem_ker])

/-- Closed proof of `LengthTwoFactorMatchingCriterion`. -/
theorem lengthTwoFactorMatchingCriterion :
    LengthTwoFactorMatchingCriterion.{uK, uG, uV, uW} := by
  intro k _ G _ V _ _ W _ _ ρ σ μ ν hμ hν hμ0 hν0 hμ2 hν2 A A' hA0 hA'0 hA hA' hX hY
  exact haveSameJordanHolderFactors_of_count_le_two μ ν hμ hν hμ0 hν0 hμ2 hν2 A A' hA0 hA'0
    hA hA' hX hY

end LengthTwo

end Langlands
