import Langlands.Representation.Induction.OpenAdjunction
import Langlands.Representation.Jacquet.Localization

/-! # Compact induction from an open normal subgroup: fixed vectors and coinvariants -/

noncomputable section
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.Induction

universe uR uG uV

variable {R : Type uR} {G : Type uG} {V : Type uV}
variable [CommRing R] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable [AddCommGroup V] [Module R V]

/-- Let `H` be an open normal subgroup of `G` and `t ∈ G` an element none of whose positive
powers lies in `H`. Then the only compactly induced function fixed by right translation by `t`
is zero. -/
theorem compactInduced_eq_zero_of_fixed (H : Subgroup G) [H.Normal] (hH : IsOpen (H : Set G))
    (σ : Representation R H V) (t : G) (ht : ∀ n : ℕ, 0 < n → t ^ n ∉ H)
    (f : CompactFunctions H σ) (hf : compactInduced H σ t f = f) : f = 0 := by
  have hpow : ∀ n : ℕ, compactInduced H σ (t ^ n) f = f := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ, map_mul, Module.End.mul_apply, hf, ih]
  by_contra hne
  have hx : ∃ x, eval H σ f.1 x ≠ 0 := by
    by_contra hall
    push Not at hall
    exact hne (compactFunctions_ext H σ fun x => hall x)
  obtain ⟨x, hx⟩ := hx
  have hval : ∀ n : ℕ, eval H σ f.1 (x * t ^ n) = eval H σ f.1 x := by
    intro n
    rw [← eval_compactInduced, hpow n]
  have hinj : Function.Injective fun n : ℕ => quotientMap H (x * t ^ n) := by
    intro m n hmn
    by_contra hne'
    have hmem := (quotientMap_eq_iff H _ _).mp hmn
    have hconj : t ^ n * (t ^ m)⁻¹ ∈ H := by
      have := Subgroup.Normal.conj_mem ‹H.Normal› _ hmem x⁻¹
      simpa [mul_assoc] using this
    rcases lt_or_gt_of_ne hne' with h | h
    · apply ht (n - m) (Nat.sub_pos_of_lt h)
      have : t ^ n * (t ^ m)⁻¹ = t ^ (n - m) := by
        rw [← pow_sub_mul_pow t h.le]; simp
      rwa [this] at hconj
    · apply ht (m - n) (Nat.sub_pos_of_lt h)
      have : (t ^ n * (t ^ m)⁻¹)⁻¹ = t ^ (m - n) := by
        rw [← pow_sub_mul_pow t h.le]; simp
      rw [← this]
      exact H.inv_mem hconj
  apply Set.infinite_of_injective_forall_mem hinj (s := quotientSupport H (eval H σ f.1))
  · intro n
    exact ⟨x * t ^ n, by
      change eval H σ f.1 (x * t ^ n) ≠ 0
      rw [hval n]
      exact hx, rfl⟩
  · exact quotientSupport_finite H σ hH f

/-- Let `H` be an open normal subgroup of `G`, `π` a representation of `G` whose restriction
to `H` is smooth, and `U ≤ H` a subgroup such that every vector of `π` lies in the
`U`-coinvariant relations. Then every compactly induced function of the restriction of `π`
to `H` lies in the `U`-coinvariant relations of the compact induction. -/
theorem compactInduced_restrict_mem_relations (H : Subgroup G) [H.Normal]
    (hH : IsOpen (H : Set G)) (π : Representation R G V) (hπ : IsSmooth (π.comp H.subtype))
    (U : Subgroup G) (hUH : U ≤ H)
    (hπU : ∀ v : V, v ∈ Jacquet.Localization.relations π U 1)
    (f : CompactFunctions H (π.comp H.subtype)) :
    f ∈ Jacquet.Localization.relations (compactInduced H (π.comp H.subtype)) U 1 := by
  classical
  let σ := π.comp H.subtype
  let cI := compactInduced H σ
  let rel := Jacquet.Localization.relations cI U 1
  rw [← cosetSum_unitMap H hH σ hπ f, cosetSum_apply]
  refine finsum_induction (fun g => g ∈ rel) rel.zero_mem (fun _ _ => rel.add_mem) ?_
  intro q
  obtain ⟨x, rfl⟩ := Quotient.exists_rep q
  let Ψ : V →ₗ[R] CompactFunctions H σ :=
    (cI x⁻¹) ∘ₗ (unitMap H hH σ hπ).toLinearMap ∘ₗ (π x)
  have hgen : ∀ (u : U) (w : V), Ψ (π u w) = cI u (Ψ w) := by
    intro u w
    have hmem : x * (u : G) * x⁻¹ ∈ H := Subgroup.Normal.conj_mem ‹H.Normal› _ (hUH u.2) x
    have hπx : π x (π u w) = σ ⟨x * (u : G) * x⁻¹, hmem⟩ (π x w) := by
      change π x (π u w) = π (x * (u : G) * x⁻¹) (π x w)
      rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]
      congr 2
      group
    change cI x⁻¹ (unitMap H hH σ hπ (π x (π u w))) =
      cI u (cI x⁻¹ (unitMap H hH σ hπ (π x w)))
    rw [hπx, (unitMap H hH σ hπ).isIntertwining]
    change cI x⁻¹ (cI (x * (u : G) * x⁻¹) (unitMap H hH σ hπ (π x w))) =
      cI u (cI x⁻¹ (unitMap H hH σ hπ (π x w)))
    rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]
    congr 2
    group
  have hΨ : Jacquet.Localization.relations π U 1 ≤ rel.comap Ψ := by
    apply Submodule.span_le.mpr
    rintro _ ⟨⟨u, w⟩, rfl⟩
    change Ψ (π u w - ((1 : U →* Rˣ) u : R) • w) ∈ rel
    rw [map_sub, map_smul, hgen]
    exact Jacquet.Localization.sub_mem_relations cI U 1 u (Ψ w)
  have hterm : cosetTerm H cI σ (unitMap H hH σ hπ) f (quotientMap H x) =
      Ψ (π x⁻¹ (eval H σ f.1 x)) := by
    rw [cosetTerm_quotientMap]
    change cI x⁻¹ (unitMap H hH σ hπ (eval H σ f.1 x)) =
      cI x⁻¹ (unitMap H hH σ hπ (π x (π x⁻¹ (eval H σ f.1 x))))
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
  change cosetTerm H cI σ (unitMap H hH σ hπ) f (quotientMap H x) ∈ rel
  rw [hterm]
  exact hΨ (hπU _)

end Langlands.Induction
