import Langlands.Representation.CompactCoefficient.IsotypicSemisimplicityProof
import Langlands.Representation.Classification.OppositeJacquetReciprocity

/-!
# Quotients from a supplied isotypic range

This purely algebraic constructor turns a supplied endomorphism whose range is
an intrinsic irreducible-isotypic sum and whose kernel has no occurrence of
that irreducible into an actual quotient map. It constructs no analytic
projector and assumes no semisimplicity of the ambient representation.
-/

noncomputable section

namespace Langlands

universe uR uG uV uW

/-- An actual quotient from a supplied intrinsic isotypic range, when its kernel
has no subquotient of the prescribed irreducible type. -/
def quotientOfIsotypicRange
    {R : Type uR} [Field R] {G : Type uG} [Monoid G]
    {V : Type uV} {W : Type uW}
    [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W]
    {ρ : Representation R G V} {σ : Representation R G W}
    (hσ : Representation.IsIrreducible σ)
    (P : ρ.IntertwiningMap ρ)
    (hrange : P.range = ⨆ f : σ.IntertwiningMap ρ, f.range)
    (hker : ∀ K : Subrepresentation P.ker.toRepresentation,
      ¬ ∃ q : K.toRepresentation.IntertwiningMap σ, Function.Surjective q)
    (hocc : ∃ S : Subrepresentation ρ,
      ∃ q : S.toRepresentation.IntertwiningMap σ, Function.Surjective q) :
    {q : ρ.IntertwiningMap σ // Function.Surjective q} := by
  classical
  have hex : ∃ q : ρ.IntertwiningMap σ, Function.Surjective q := by
    have hP : P ≠ 0 := by
      intro hP
      obtain ⟨S, q, hq⟩ := hocc
      let K : Subrepresentation P.ker.toRepresentation :=
        { toSubmodule :=
            { carrier := {v | v.val ∈ S}
              add_mem' := fun hx hy => S.toSubmodule.add_mem hx hy
              zero_mem' := S.toSubmodule.zero_mem
              smul_mem' := fun c _ hx => S.toSubmodule.smul_mem c hx }
          apply_mem_toSubmodule := fun g _ hv => S.apply_mem_toSubmodule g hv }
      let qK : K.toRepresentation.IntertwiningMap σ :=
        { toLinearMap :=
            { toFun := fun v => q ⟨v.val.val, v.property⟩
              map_add' := fun v w => by
                change q ((⟨v.val.val, v.property⟩ : S.toSubmodule) +
                  (⟨w.val.val, w.property⟩ : S.toSubmodule)) =
                  q ⟨v.val.val, v.property⟩ + q ⟨w.val.val, w.property⟩
                exact map_add q _ _
              map_smul' := fun c v => by
                change q (c • (⟨v.val.val, v.property⟩ : S.toSubmodule)) =
                  c • q ⟨v.val.val, v.property⟩
                exact map_smul q c _ }
          isIntertwining' := fun g => by
            ext v
            exact Representation.IntertwiningMap.isIntertwining _ _ q g
              ⟨v.val.val, v.property⟩ }
      apply hker K
      refine ⟨qK, fun w => ?_⟩
      obtain ⟨v, hv⟩ := hq w
      have hvP : v.val ∈ P.ker := by
        change P v.val = 0
        rw [hP]
        rfl
      exact ⟨⟨⟨v.val, hvP⟩, v.property⟩, hv⟩
    have hmap : ∃ f : σ.IntertwiningMap ρ, f ≠ 0 := by
      by_contra h
      push Not at h
      have hr : P.range = ⊥ := by
        rw [hrange]
        apply eq_bot_iff.mpr
        apply iSup_le_iff.mpr
        intro f
        rw [h f]
        intro v hv
        obtain ⟨w, hw⟩ := hv
        exact hw.symm
      apply hP
      ext v
      exact hr.le ⟨v, rfl⟩
    obtain ⟨f, hf⟩ := hmap
    let := hσ
    have hf_inj : Function.Injective f :=
      (Representation.IsIrreducible.injective_or_eq_zero f).resolve_right hf
    have hσss : Representation.IsSemisimpleRepresentation σ := by
      rw [Representation.isSemisimpleRepresentation_iff_isSemisimpleModule_asModule]
      infer_instance
    have hrss : Representation.IsSemisimpleRepresentation P.range.toRepresentation := by
      rw [hrange]
      exact CompactCoefficientClass.isSemisimpleRepresentation_iSup _ fun f =>
        CompactCoefficientClass.isSemisimpleRepresentation_range hσss f
    have hf_mem (w : W) : f w ∈ P.range := by
      rw [hrange]
      exact le_iSup (fun f : σ.IntertwiningMap ρ => f.range) f ⟨w, rfl⟩
    let i : σ.IntertwiningMap P.range.toRepresentation :=
      { toLinearMap := f.toLinearMap.codRestrict P.range.toSubmodule hf_mem
        isIntertwining' := fun g => by
          ext w
          exact Representation.IntertwiningMap.isIntertwining _ _ f g w }
    have hi : Function.Injective i := fun _ _ h => hf_inj (congrArg Subtype.val h)
    let r := (semisimpleRetraction hrss i hi).val
    have hr : r.comp i = Representation.IntertwiningMap.id σ :=
      (semisimpleRetraction hrss i hi).property
    have hr_surj : Function.Surjective r := by
      intro w
      exact ⟨i w, congrArg (fun h : σ.IntertwiningMap σ => h w) hr⟩
    let p : ρ.IntertwiningMap P.range.toRepresentation :=
      { toLinearMap := P.toLinearMap.rangeRestrict
        isIntertwining' := fun g => by
          ext v
          exact Representation.IntertwiningMap.isIntertwining _ _ P g v }
    have hp : Function.Surjective p := by
      rintro ⟨v, w, hw⟩
      exact ⟨w, Subtype.ext hw⟩
    exact ⟨r.comp p, hr_surj.comp hp⟩
  exact ⟨Classical.choose hex, Classical.choose_spec hex⟩

end Langlands
