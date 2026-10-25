import Langlands.Representation.Category.IrreducibleSumInjectionStatement

/-! Injectivity of the actual sum of two inequivalent irreducible embeddings. -/

noncomputable section

namespace Langlands

universe uK uG uV uW uX

/-- The exact sum-injection assertion for independent representation carriers. -/
theorem irreducibleSumInjection :
    IrreducibleSumInjectionStatement.{uK, uG, uV, uW, uX} := by
  classical
  intro k _ G _ A B C hA hB hAB f g hf hg
  let : Representation.IsIrreducible A.ρ := hA
  let : Representation.IsIrreducible B.ρ := hB
  have hgi : Function.Injective g :=
    (Representation.IsIrreducible.injective_or_eq_zero g).resolve_right hg
  let K : Subrepresentation A.ρ :=
    { toSubmodule := g.range.toSubmodule.comap f.toLinearMap
      apply_mem_toSubmodule m a ha := by
        change f (A.ρ m a) ∈ g.range.toSubmodule
        rw [f.isIntertwining]
        exact g.range.apply_mem_toSubmodule m ha }
  have hK : K = ⊥ := by
    rcases hA.eq_bot_or_eq_top K with h | h
    · exact h
    · exfalso
      have hfmem (a : A) : f a ∈ g.toLinearMap.range := by
        change a ∈ K.toSubmodule
        rw [h]
        exact Submodule.mem_top
      let l : A →ₗ[k] B :=
        (LinearEquiv.ofInjective g.toLinearMap hgi).symm.toLinearMap.comp
          (f.toLinearMap.codRestrict g.toLinearMap.range hfmem)
      have hl (a : A) : g (l a) = f a :=
        LinearEquiv.ofInjective_symm_apply g.toLinearMap (h := hgi)
          ⟨f a, hfmem a⟩
      let q : A.ρ.IntertwiningMap B.ρ :=
        { toLinearMap := l
          isIntertwining' m := by
            ext a
            apply hgi
            change g (l (A.ρ m a)) = g (B.ρ m (l a))
            rw [hl, g.isIntertwining, hl, f.isIntertwining] }
      have hq : q ≠ 0 := by
        intro hq0
        apply hf
        ext a
        have hqa : l a = 0 :=
          congrArg (fun u : A.ρ.IntertwiningMap B.ρ => u a) hq0
        have := hl a
        simpa [hqa] using this.symm
      exact hAB
        ⟨q.ofBijective
          ((Representation.IsIrreducible.bijective_or_eq_zero q).resolve_right hq)⟩
  let s : (A.ρ.prod B.ρ).IntertwiningMap C.ρ :=
    f.comp (Representation.IntertwiningMap.fst k A.ρ B.ρ) +
      g.comp (Representation.IntertwiningMap.snd k A.ρ B.ρ)
  change Function.Injective s.toLinearMap
  apply LinearMap.ker_eq_bot.mp
  apply le_antisymm _ bot_le
  intro x hx
  have hx0 : f x.1 + g x.2 = 0 := hx
  have hxK : x.1 ∈ K.toSubmodule := by
    change f x.1 ∈ g.toLinearMap.range
    refine ⟨-x.2, ?_⟩
    rw [map_neg]
    exact (eq_neg_of_add_eq_zero_left hx0).symm
  have ha : x.1 = 0 := by
    rw [hK] at hxK
    exact hxK
  have hb : x.2 = 0 := by
    apply hgi
    simpa [ha] using hx0
  exact show x = 0 from Prod.ext ha hb

end Langlands
