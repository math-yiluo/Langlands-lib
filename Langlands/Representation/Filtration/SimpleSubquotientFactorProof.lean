import Langlands.Representation.Filtration.SimpleSubquotientFactorStatement
import Langlands.Representation.Filtration.SubsingletonProof
import Mathlib.LinearAlgebra.Isomorphisms

/-! Every simple actual subquotient occurs in a supplied composition series. -/

namespace Langlands

universe uK uG uV uW

private theorem intertwiner_descends
    {k G X Y Z : Type*} [Field k] [Monoid G]
    [AddCommGroup X] [Module k X] [AddCommGroup Y] [Module k Y]
    [AddCommGroup Z] [Module k Z]
    {ρ : Representation k G X} {σ : Representation k G Y} {τ : Representation k G Z}
    (g : ρ.IntertwiningMap σ) (f : ρ.IntertwiningMap τ)
    (hg : Function.Surjective g) (hker : g.toLinearMap.ker ≤ f.toLinearMap.ker) :
    ∃ h : σ.IntertwiningMap τ, ∀ x, h (g x) = f x := by
  let l : Y →ₗ[k] Z :=
    (g.toLinearMap.ker.liftQ f.toLinearMap hker).comp
      (g.toLinearMap.quotKerEquivOfSurjective hg).symm.toLinearMap
  have hl (x : X) : l (g x) = f x := by
    change (g.toLinearMap.ker.liftQ f.toLinearMap hker)
      ((g.toLinearMap.quotKerEquivOfSurjective hg).symm (g.toLinearMap x)) = f x
    rw [LinearMap.quotKerEquivOfSurjective_symm_apply]
    rfl
  refine ⟨⟨l, fun a => ?_⟩, hl⟩
  ext y
  obtain ⟨x, rfl⟩ := hg y
  change l (σ a (g x)) = τ a (l (g x))
  rw [← Representation.IntertwiningMap.isIntertwining _ _ g a x, hl, hl]
  exact Representation.IntertwiningMap.isIntertwining _ _ f a x

/-- An irreducible actual subquotient is one of the actual factors of the given
composition series, with independent ambient and constituent carrier universes. -/
theorem simpleSubquotientFactor : SimpleSubquotientFactorTheorem.{uK, uG, uV, uW} := by
  classical
  intro k _ G _ _ A r s hs D S U hD he
  let : D.representation.IsIrreducible := hD
  let : Nontrivial D :=
    IsSimpleModule.nontrivial (MonoidAlgebra k G) D.representation.asModule
  obtain ⟨e⟩ := he
  let f : S.toRepresentation.IntertwiningMap D.representation :=
    e.symm.toIntertwiningMap.comp (SmoothRep.hom (SmoothRep.mkQ
      (SmoothRep.subrepresentation A S) U))
  have hf : Function.Surjective f :=
    e.symm.toLinearEquiv.surjective.comp (SmoothRep.mkQ_surjective _ U)
  let P (i : Fin (r + 1)) : Prop :=
    ∀ x : S.toSubmodule, (x : A) ∈ s.subrepresentation i → f x = 0
  have hzero : P 0 := by
    intro x hx
    rw [s.subrepresentation_zero] at hx
    have hx0 : x = 0 := Subtype.ext hx
    rw [hx0, map_zero]
  have hlast : ¬ P (Fin.last r) := by
    intro h
    obtain ⟨d, hd⟩ := exists_ne (0 : D)
    obtain ⟨x, rfl⟩ := hf d
    exact hd (h x (by rw [s.subrepresentation_last]; trivial))
  have hstep : ∃ j : Fin r, P j.castSucc ∧ ¬ P j.succ := by
    by_contra h
    have hnext : ∀ j : Fin r, P j.castSucc → P j.succ := by
      intro j hj
      by_contra hj'
      exact h ⟨j, hj, hj'⟩
    exact hlast (Fin.induction hzero hnext (Fin.last r))
  obtain ⟨j, hj, hj'⟩ := hstep
  change ¬ (∀ x : S.toSubmodule, (x : A) ∈ s.subrepresentation j.succ → f x = 0) at hj'
  push Not at hj'
  obtain ⟨x, hx, hfx⟩ := hj'
  let X : Subrepresentation A.representation := S ⊓ s.subrepresentation j.succ
  let iS : X.toRepresentation.IntertwiningMap S.toRepresentation :=
    { toLinearMap :=
        { toFun := fun v => ⟨v.val, v.property.1⟩
          map_add' := fun _ _ => rfl
          map_smul' := fun _ _ => rfl }
      isIntertwining' := fun _ => rfl }
  let iT : X.toRepresentation.IntertwiningMap
      (s.subrepresentation j.succ).toRepresentation :=
    { toLinearMap :=
        { toFun := fun v => ⟨v.val, v.property.2⟩
          map_add' := fun _ _ => rfl
          map_smul' := fun _ _ => rfl }
      isIntertwining' := fun _ => rfl }
  let q := (s.gradedProjection j).hom.comp iT
  let fX := f.comp iS
  have hker : q.toLinearMap.ker ≤ fX.toLinearMap.ker := by
    intro v hv
    exact hj (iS v) ((s.gradedProjection_eq_zero_iff j (iT v)).mp hv)
  let v : X.toSubmodule := ⟨x.val, x.property, hx⟩
  have hfv : fX v ≠ 0 := hfx
  have hq : q ≠ 0 := by
    intro hq
    apply hfv
    apply hker
    change q v = 0
    rw [hq]
    rfl
  let : (s.gradedRepresentation j).ρ.IsIrreducible := hs j
  have hqsurj : Function.Surjective q :=
    (Representation.IsIrreducible.surjective_or_eq_zero q).resolve_right hq
  obtain ⟨h, hh⟩ := intertwiner_descends q fX hqsurj hker
  have hn : h ≠ 0 := by
    intro hz
    apply hfv
    rw [← hh v, hz]
    rfl
  have hb : Function.Bijective h :=
    (Representation.IsIrreducible.bijective_or_eq_zero h).resolve_right hn
  exact ⟨j, ⟨(h.ofBijective hb).symm⟩⟩

end Langlands
