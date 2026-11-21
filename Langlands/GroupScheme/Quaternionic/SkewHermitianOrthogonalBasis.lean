import Langlands.GroupScheme.Quaternionic.AntihermitianForm
import Mathlib.LinearAlgebra.Basis.Prod

/-! # Orthogonal bases for antihermitian division-space pairings -/

noncomputable section

universe u v w

namespace Langlands.GroupScheme.Quaternionic.AntihermitianForm

variable {F : Type u} {D : Type v} [Field F] [DivisionRing D] [Algebra F D]
  {τ : FirstKindInvolution F D}
  {V : Type w} [AddCommGroup V] [Module F V] [Module D V] [IsScalarTower F D V]
  (B : AntihermitianForm τ V)

/-- A separating antihermitian form for a nontrivial involution has a nondegenerate
  line in every positive-dimensional space. -/
theorem exists_self_ne_zero [Nontrivial V] (hτ : ∃ a, τ a ≠ a)
    (hB : B.toBilin.SeparatingLeft) : ∃ x, B x x ≠ 0 := by
  by_contra! h
  obtain ⟨x, hx⟩ := exists_ne (0 : V)
  obtain ⟨y, hy⟩ : ∃ y, B x y ≠ 0 := by
    by_contra! hxy
    exact hx (hB x hxy)
  obtain ⟨a, ha⟩ := hτ
  let z := (a * (B x y)⁻¹) • x
  have hz : B z y = a := by
    change B ((a * (B x y)⁻¹) • x) y = a
    rw [B.smul_left, mul_assoc, inv_mul_cancel₀ hy, mul_one]
  change ∀ x, B x x = 0 at h
  have hzy := h (z + y)
  change B (z + y) (z + y) = 0 at hzy
  rw [B.add_left, B.add_right, B.add_right, h z, h y, zero_add, add_zero,
    B.skew z y, hz, ← sub_eq_add_neg] at hzy
  exact ha (sub_eq_zero.mp hzy).symm

private theorem exists_orthogonalBasis_aux (hτ : ∃ a, τ a ≠ a) (n : ℕ) :
    ∀ {V : Type w} [AddCommGroup V] [Module F V] [Module D V] [IsScalarTower F D V]
      [FiniteDimensional D V] (B : AntihermitianForm τ V),
      B.toBilin.SeparatingLeft → Module.finrank D V = n →
      ∃ b : Module.Basis (Fin n) D V,
        (∀ i j, i ≠ j → B (b i) (b j) = 0) ∧ (∀ i, B (b i) (b i) ≠ 0) := by
  induction n with
  | zero =>
    intro V _ _ _ _ _ B _ hV
    exact ⟨(Module.finBasis D V).reindex (finCongr hV), fun i => Fin.elim0 i, fun i => Fin.elim0 i⟩
  | succ n ih =>
    intro V _ _ _ _ _ B hB hV
    let : Nontrivial V := Module.nontrivial_of_finrank_eq_succ hV
    obtain ⟨x, hx⟩ := B.exists_self_ne_zero hτ hB
    let W := B.orthogonalLine x
    let e := B.splitLine x hx
    have hr := e.finrank_eq
    simp only [Module.finrank_prod, Module.finrank_self, hV] at hr
    change 1 + Module.finrank D W = n + 1 at hr
    obtain ⟨b, hb, hd⟩ := ih (B.pullback W.subtype)
      (B.orthogonalLine_separatingLeft hB x hx) (by omega)
    let db := Module.Basis.singleton (Fin 1) D
    let c := (db.prod b).map e
    let p : Fin 1 ⊕ Fin n ≃ Fin (n + 1) := finSumFinEquiv.trans (finCongr (Nat.add_comm 1 n))
    have hleft (i : Fin 1) : c (Sum.inl i) = x := by
      simp [c, db, e, W]
    have hright (i : Fin n) : c (Sum.inr i) = (b i : V) := by
      simp [c, e, W]
    refine ⟨c.reindex p, ?_, ?_⟩
    · intro i j hij
      obtain ⟨i, rfl⟩ := p.surjective i
      obtain ⟨j, rfl⟩ := p.surjective j
      have hn : i ≠ j := fun h => hij (congrArg p h)
      rw [Module.Basis.reindex_apply, Module.Basis.reindex_apply, p.symm_apply_apply, p.symm_apply_apply]
      rcases i with i | i <;> rcases j with j | j
      · exact (hn (congrArg Sum.inl (Subsingleton.elim i j))).elim
      · have hj : B (b j) x = 0 := (b j).property
        rw [hleft, hright, B.skew (b j : V) x, hj, τ.map_zero, neg_zero]
      · rw [hright, hleft]
        exact (b i).property
      · rw [hright, hright]
        exact hb i j (fun h => hn (congrArg Sum.inr h))
    · intro i
      obtain ⟨i, rfl⟩ := p.surjective i
      rw [Module.Basis.reindex_apply, p.symm_apply_apply]
      rcases i with i | i
      · rw [hleft]
        exact hx
      · rw [hright]
        exact hd i

/-- A separating antihermitian pairing for a nontrivial involution has an orthogonal
  division-algebra basis with nonzero diagonal values. -/
def OrthogonalBasisStatement : Prop :=
  ∀ (F : Type u) (D : Type v) [Field F] [DivisionRing D] [Algebra F D]
    (τ : FirstKindInvolution F D) (V : Type w) [AddCommGroup V]
    [Module F V] [Module D V] [IsScalarTower F D V] [FiniteDimensional D V]
    (B : AntihermitianForm τ V), (∃ a, τ a ≠ a) → B.toBilin.SeparatingLeft →
    ∃ b : Module.Basis (Fin (Module.finrank D V)) D V,
      (∀ i j, i ≠ j → B (b i) (b j) = 0) ∧ (∀ i, B (b i) (b i) ≠ 0)

theorem orthogonalBasis : OrthogonalBasisStatement.{u, v, w} := by
  intro F D _ _ _ τ V _ _ _ _ _ B hτ hB
  exact exists_orthogonalBasis_aux hτ (Module.finrank D V) B hB rfl

end Langlands.GroupScheme.Quaternionic.AntihermitianForm
