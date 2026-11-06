import Langlands.Representation.Filtration.ObjectDefinitions
import Mathlib.RingTheory.Length

/-! Length bounds for intertwining spaces along actual object filtrations. -/

noncomputable section

namespace Langlands.HomSpace

universe uK uG uV uW uX

variable {k : Type uK} [Field k] {G : Type uG} [Monoid G]
variable {V : Type uV} {W : Type uW} {X : Type uX}
variable [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]
variable [AddCommGroup X] [Module k X]

/-- Extended-natural length of the full space of intertwining maps. -/
def length (ρ : Representation k G V) (σ : Representation k G W) : ℕ∞ :=
  Module.length k (ρ.IntertwiningMap σ)

/-- Precomposition by an actual intertwiner. -/
def comap {ρ : Representation k G V} {τ : Representation k G X}
    (σ : Representation k G W) (h : ρ.IntertwiningMap τ) :
    τ.IntertwiningMap σ →ₗ[k] ρ.IntertwiningMap σ where
  toFun f := f.comp h
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem comap_injective {ρ : Representation k G V} {τ : Representation k G X}
    (σ : Representation k G W) (h : ρ.IntertwiningMap τ)
    (hh : Function.Surjective h) : Function.Injective (comap σ h) := by
  intro f g hfg
  ext x
  obtain ⟨v, rfl⟩ := hh x
  exact congrArg (fun t : ρ.IntertwiningMap σ => t v) hfg

/-- An equivalence of source representations preserves the intertwining space. -/
def equivLeft {ρ : Representation k G V} {τ : Representation k G X}
    (σ : Representation k G W) (e : ρ.Equiv τ) :
    ρ.IntertwiningMap σ ≃ₗ[k] τ.IntertwiningMap σ :=
  { comap σ e.symm.toIntertwiningMap with
    invFun := comap σ e.toIntertwiningMap
    left_inv := by
      intro f
      ext v
      exact congrArg f (e.symm_apply_apply v)
    right_inv := by
      intro f
      ext x
      exact congrArg f (e.apply_symm_apply x) }

theorem length_congr_left {ρ : Representation k G V} {τ : Representation k G X}
    (σ : Representation k G W) (e : ρ.Equiv τ) :
    length ρ σ = length τ σ :=
  (equivLeft σ e).length_eq

theorem length_top_left (ρ : Representation k G V) (σ : Representation k G W) :
    length (⊤ : Subrepresentation ρ).toRepresentation σ = length ρ σ := by
  refine length_congr_left σ
    { toLinearMap := (⊤ : Subrepresentation ρ).toSubmodule.subtype
      isIntertwining' := fun _ => rfl
      invFun := fun v => ⟨v, trivial⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

theorem length_bot_left (ρ : Representation k G V) (σ : Representation k G W) :
    length (⊥ : Subrepresentation ρ).toRepresentation σ = 0 := by
  apply Module.length_eq_zero_iff.mpr
  constructor
  intro f g
  ext ⟨v, hv⟩
  have hv' : v = 0 := hv
  subst hv'
  exact (map_zero f).trans (map_zero g).symm

/-- Restrict a map to a subrepresentation. -/
def restrict (ρ : Representation k G V) (σ : Representation k G W)
    (S : Subrepresentation ρ) :
    ρ.IntertwiningMap σ →ₗ[k] S.toRepresentation.IntertwiningMap σ :=
  comap σ
    { toLinearMap := S.toSubmodule.subtype
      isIntertwining' := fun _ => rfl }

/-- A map vanishing on a subrepresentation descends to its actual quotient. -/
def descend (ρ : Representation k G V) (σ : Representation k G W)
    (S : Subrepresentation ρ) :
    LinearMap.ker (restrict ρ σ S) →ₗ[k]
      (ρ.quotient S.toSubmodule (fun g _ hv => S.apply_mem_toSubmodule g hv)).IntertwiningMap σ := by
  have hker (f : LinearMap.ker (restrict ρ σ S)) :
      S.toSubmodule ≤ LinearMap.ker f.val.toLinearMap := by
    intro v hv
    exact congrArg (fun t : S.toRepresentation.IntertwiningMap σ => t ⟨v, hv⟩) f.property
  refine
    { toFun := fun f =>
        { toLinearMap := S.toSubmodule.liftQ f.val.toLinearMap (hker f)
          isIntertwining' := ?_ }
      map_add' := ?_
      map_smul' := ?_ }
  · intro g
    apply LinearMap.ext
    intro q
    obtain ⟨v, rfl⟩ := Submodule.mkQ_surjective S.toSubmodule q
    change f.val (ρ g v) = σ g (f.val v)
    exact Representation.IntertwiningMap.isIntertwining ρ σ f.val g v
  · intro f g
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro q
    obtain ⟨v, rfl⟩ := Submodule.mkQ_surjective S.toSubmodule q
    rfl
  · intro a f
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro q
    obtain ⟨v, rfl⟩ := Submodule.mkQ_surjective S.toSubmodule q
    rfl

theorem descend_injective (ρ : Representation k G V) (σ : Representation k G W)
    (S : Subrepresentation ρ) : Function.Injective (descend ρ σ S) := by
  intro f g h
  apply Subtype.ext
  ext v
  exact congrArg (fun t => t (S.toSubmodule.mkQ v)) h

/-- Restriction and descent bound Hom length by the subrepresentation and quotient. -/
theorem length_le_subrepresentation_add_quotient
    (ρ : Representation k G V) (σ : Representation k G W)
    (S : Subrepresentation ρ) :
    length ρ σ ≤ length S.toRepresentation σ +
      length (ρ.quotient S.toSubmodule (fun g _ hv => S.apply_mem_toSubmodule g hv)) σ := by
  let r := restrict ρ σ S
  have hex : Function.Exact (LinearMap.ker r).subtype r.rangeRestrict := by
    apply LinearMap.exact_iff.mpr
    rw [LinearMap.ker_rangeRestrict, Submodule.range_subtype]
  have heq := Module.length_eq_add_of_exact (R := k) (N := LinearMap.ker r)
    (M := ρ.IntertwiningMap σ) (P := LinearMap.range r)
    (LinearMap.ker r).subtype r.rangeRestrict
    (Submodule.injective_subtype _) r.surjective_rangeRestrict hex
  change Module.length k (ρ.IntertwiningMap σ) ≤ _
  rw [heq, add_comm]
  exact add_le_add
    (Module.length_le_of_injective (LinearMap.range r).subtype (Submodule.injective_subtype _))
    (Module.length_le_of_injective (descend ρ σ S) (descend_injective ρ σ S))

/-- Each successive actual quotient bounds the increase in Hom length. -/
theorem length_filtration_step {A : Rep.{uV} k G} {n : ℕ}
    (s : ObjectRepFiltration A n) (σ : Representation k G W) (j : Fin n) :
    length (s.subrepresentation j.succ).toRepresentation σ ≤
      length (s.subrepresentation j.castSucc).toRepresentation σ +
        length (s.gradedRepresentation j).ρ σ := by
  have hle : s.subrepresentation j.castSucc ≤ s.subrepresentation j.succ :=
    s.monotone_subrepresentation (Fin.castSucc_le_succ j)
  let S := (s.step j.castSucc).lowerInUpper (s.step j.succ)
    (CategoryTheory.Discrete.mk PUnit.unit)
  let e : S.toRepresentation.Equiv (s.subrepresentation j.castSucc).toRepresentation :=
    { toLinearMap :=
        { toFun := fun v => ⟨v.val.val, v.property⟩
          map_add' := fun _ _ => rfl
          map_smul' := fun _ _ => rfl }
      isIntertwining' := fun _ => rfl
      invFun := fun v => ⟨⟨v.val, hle v.property⟩, v.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have h := length_le_subrepresentation_add_quotient
    (s.subrepresentation j.succ).toRepresentation σ S
  exact h.trans (add_le_add (le_of_eq (length_congr_left σ e)) le_rfl)

/-- Hom length is bounded by the sum over all actual graded pieces. -/
theorem length_le_sum {A : Rep.{uV} k G} {n : ℕ}
    (s : ObjectRepFiltration A n) (σ : Representation k G W) :
    length A.ρ σ ≤ ∑ i : Fin n, length (s.gradedRepresentation i).ρ σ := by
  have key : ∀ j : ℕ, (hj : j ≤ n) →
      length (s.subrepresentation ⟨j, Nat.lt_succ_of_le hj⟩).toRepresentation σ ≤
        ∑ i : Fin j, length (s.gradedRepresentation
          ⟨i, lt_of_lt_of_le i.isLt hj⟩).ρ σ := by
    intro j
    induction j with
    | zero =>
      intro hj
      have h0 : s.subrepresentation ⟨0, Nat.lt_succ_of_le hj⟩ = ⊥ :=
        s.subrepresentation_zero
      simp only [Finset.univ_eq_empty, Finset.sum_empty]
      rw [h0, length_bot_left]
    | succ j ih =>
      intro hj
      have hjn : j < n := hj
      rw [Fin.sum_univ_castSucc]
      simp only [Fin.val_castSucc, Fin.val_last]
      exact (length_filtration_step s σ ⟨j, hjn⟩).trans
        (add_le_add (ih hjn.le) le_rfl)
  have h := key n le_rfl
  have hl : (⟨n, Nat.lt_succ_of_le le_rfl⟩ : Fin (n + 1)) = Fin.last n := rfl
  rw [hl, s.subrepresentation_last, length_top_left] at h
  exact h

/-- If only one grade can contribute, it bounds the total Hom length. -/
theorem length_le_of_single_piece {A : Rep.{uV} k G} {n : ℕ}
    (s : ObjectRepFiltration A n) (σ : Representation k G W) (i₀ : Fin n)
    (hzero : ∀ i, i ≠ i₀ → length (s.gradedRepresentation i).ρ σ = 0) :
    length A.ρ σ ≤ length (s.gradedRepresentation i₀).ρ σ := by
  classical
  have hsum : ∑ i : Fin n, length (s.gradedRepresentation i).ρ σ =
      length (s.gradedRepresentation i₀).ρ σ :=
    Finset.sum_eq_single i₀ (fun i _ hi => hzero i hi)
      (fun h => (h (Finset.mem_univ i₀)).elim)
  exact hsum ▸ length_le_sum s σ

/-- Length at most one implies proportionality to each nonzero intertwiner. -/
theorem exists_smul_eq_of_length_le_one
    (ρ : Representation k G V) (σ : Representation k G W)
    (h : length ρ σ ≤ 1) (f g : ρ.IntertwiningMap σ) (hf : f ≠ 0) :
    ∃ a : k, g = a • f := by
  have hne : length ρ σ ≠ 0 := by
    intro hz
    have hs : Subsingleton (ρ.IntertwiningMap σ) := Module.length_eq_zero_iff.mp hz
    exact hf (hs.elim _ _)
  have hone : Module.length k (ρ.IntertwiningMap σ) = 1 :=
    le_antisymm h (Order.one_le_iff_ne_zero.mpr hne)
  let : IsSimpleModule k (ρ.IntertwiningMap σ) := Module.length_eq_one_iff.mp hone
  have hmem : g ∈ Submodule.span k {f} := by
    rw [IsSimpleModule.span_singleton_eq_top k hf]
    trivial
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hmem
  exact ⟨a, ha.symm⟩

/-- One grade of length at most one gives proportionality on the filtered source. -/
theorem exists_smul_eq_of_single_piece {A : Rep.{uV} k G} {n : ℕ}
    (s : ObjectRepFiltration A n) (σ : Representation k G W) (i₀ : Fin n)
    (hzero : ∀ i, i ≠ i₀ → length (s.gradedRepresentation i).ρ σ = 0)
    (hone : length (s.gradedRepresentation i₀).ρ σ ≤ 1)
    (f g : A.ρ.IntertwiningMap σ) (hf : f ≠ 0) :
    ∃ a : k, g = a • f :=
  exists_smul_eq_of_length_le_one A.ρ σ
    ((length_le_of_single_piece s σ i₀ hzero).trans hone) f g hf

end Langlands.HomSpace
