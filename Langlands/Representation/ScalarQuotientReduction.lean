import Langlands.Representation.Filtration.RepresentationLength
import Mathlib.RepresentationTheory.Irreducible
import Mathlib.RingTheory.Noetherian.Orzech

/-!
# Quotients from scalar central quotients

Internal algebraic reduction by finite composition length. No analytic assertion
or existence of an analytic projector is part of this module.
-/

noncomputable section

namespace Langlands.ScalarQuotientReduction

universe uR uG uV uW

variable {R : Type uR} [Field R] {G : Type uG} [Group G]
  {V : Type uV} {W : Type uW}
  [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W]

private def inclusion (ρ : Representation R G V) (S : Subrepresentation ρ) :
    S.toRepresentation.IntertwiningMap ρ :=
  { toLinearMap := S.toSubmodule.subtype
    isIntertwining' := fun _ => rfl }

private def quotientProjection (ρ : Representation R G V) (S : Subrepresentation ρ) :
    ρ.IntertwiningMap
      (ρ.quotient S.toSubmodule (fun g _ hv => S.apply_mem_toSubmodule g hv)) :=
  { toLinearMap := S.toSubmodule.mkQ
    isIntertwining' := fun _ => rfl }

private def rangeProjection {ρ : Representation R G V} {σ : Representation R G W}
    (f : ρ.IntertwiningMap σ) : ρ.IntertwiningMap f.range.toRepresentation :=
  { toLinearMap := f.toLinearMap.rangeRestrict
    isIntertwining' g := by
      ext v
      change f (ρ g v) = σ g (f v)
      exact Representation.IntertwiningMap.isIntertwining _ _ f g v }

private theorem rangeProjection_surjective
    {ρ : Representation R G V} {σ : Representation R G W}
    (f : ρ.IntertwiningMap σ) : Function.Surjective (rangeProjection f) := by
  rintro ⟨v, w, hw⟩
  exact ⟨w, Subtype.ext hw⟩

private def centralDefect (ρ : Representation R G V)
    (z : Subgroup.center G) (c : R) : ρ.IntertwiningMap ρ :=
  { toLinearMap := ρ z
    isIntertwining' g := by
      change ρ (z : G) * ρ g = ρ g * ρ (z : G)
      rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp z.property g] } -
    c • Representation.IntertwiningMap.id ρ

private theorem occurrence_dichotomy
    {ρ : Representation R G V} {σ : Representation R G W}
    (hσ : σ.IsIrreducible)
    (hocc : ∃ S : Subrepresentation ρ,
      ∃ q : S.toRepresentation.IntertwiningMap σ, Function.Surjective q)
    (A : Subrepresentation ρ) :
    (∃ S : Subrepresentation A.toRepresentation,
      ∃ q : S.toRepresentation.IntertwiningMap σ, Function.Surjective q) ∨
    (∃ S : Subrepresentation
        (ρ.quotient A.toSubmodule (fun g _ hv => A.apply_mem_toSubmodule g hv)),
      ∃ q : S.toRepresentation.IntertwiningMap σ, Function.Surjective q) := by
  let := hσ
  obtain ⟨S, q, hq⟩ := hocc
  let f := (quotientProjection ρ A).comp (inclusion ρ S)
  let K := f.ker
  let qK := q.comp (inclusion S.toRepresentation K)
  rcases Representation.IsIrreducible.surjective_or_eq_zero qK with hs | hz
  · left
    let L : Subrepresentation A.toRepresentation :=
      { toSubmodule :=
          { carrier := {v | v.val ∈ S}
            zero_mem' := S.toSubmodule.zero_mem
            add_mem' := fun hx hy => S.toSubmodule.add_mem hx hy
            smul_mem' := fun c _ hx => S.toSubmodule.smul_mem c hx }
        apply_mem_toSubmodule := fun g _ hv => S.apply_mem_toSubmodule g hv }
    let r : L.toRepresentation.IntertwiningMap σ :=
      { toLinearMap :=
          { toFun v := q ⟨v.val.val, v.property⟩
            map_add' v w := by
              change q ((⟨v.val.val, v.property⟩ : S.toSubmodule) +
                (⟨w.val.val, w.property⟩ : S.toSubmodule)) = _
              exact map_add q _ _
            map_smul' c v := by
              change q (c • (⟨v.val.val, v.property⟩ : S.toSubmodule)) = _
              exact map_smul q c _ }
        isIntertwining' g := by
          ext v
          exact Representation.IntertwiningMap.isIntertwining _ _ q g ⟨v.val.val, v.property⟩ }
    refine ⟨L, r, fun w => ?_⟩
    obtain ⟨v, hv⟩ := hs w
    have hvA : v.val.val ∈ A := by
      exact (Submodule.Quotient.mk_eq_zero A.toSubmodule).mp v.property
    exact ⟨⟨⟨v.val.val, hvA⟩, v.val.property⟩, hv⟩
  · right
    have hK : K.toSubmodule ≤ q.toLinearMap.ker := by
      intro v hv
      exact congrArg (fun r : K.toRepresentation.IntertwiningMap σ => r ⟨v, hv⟩) hz
    let qbar :
        (S.toRepresentation.quotient K.toSubmodule
          (fun g _ hv => K.apply_mem_toSubmodule g hv)).IntertwiningMap σ :=
      { toLinearMap := K.toSubmodule.liftQ q.toLinearMap hK
        isIntertwining' g := by
          apply Submodule.linearMap_qext
          ext v
          exact Representation.IntertwiningMap.isIntertwining _ _ q g v }
    let e :
        (S.toRepresentation.quotient K.toSubmodule
          (fun g _ hv => K.apply_mem_toSubmodule g hv)).Equiv f.range.toRepresentation :=
      Representation.Equiv.mk f.toLinearMap.quotKerEquivRange fun g => by
        apply Submodule.linearMap_qext
        ext v
        change f (S.toRepresentation g v) =
          (ρ.quotient A.toSubmodule (fun g _ hv => A.apply_mem_toSubmodule g hv)) g (f v)
        exact Representation.IntertwiningMap.isIntertwining _ _ f g v
    refine ⟨f.range, qbar.comp e.symm.toIntertwiningMap, ?_⟩
    apply Function.Surjective.comp _ e.symm.surjective
    intro w
    obtain ⟨v, hv⟩ := hq w
    exact ⟨K.toSubmodule.mkQ v, hv⟩

private theorem centralDefect_not_surjective
    {ρ : Representation R G V} {σ : Representation R G W}
    (hfin : IsFiniteLength (MonoidAlgebra R G) ρ.asModule)
    (hσ : σ.IsIrreducible) (z : Subgroup.center G) (c : R)
    (hσz : ∀ w, σ z w = c • w)
    (hocc : ∃ S : Subrepresentation ρ,
      ∃ q : S.toRepresentation.IntertwiningMap σ, Function.Surjective q) :
    ¬ Function.Surjective (centralDefect ρ z c) := by
  let := hσ
  let : IsSimpleModule (MonoidAlgebra R G) σ.asModule :=
    (Representation.irreducible_iff_isSimpleModule_asModule σ).mp hσ
  have hnontriv : Nontrivial σ.asModule :=
    IsSimpleModule.nontrivial (MonoidAlgebra R G) σ.asModule
  let := hnontriv
  let : Nontrivial W := σ.asModuleEquiv.toEquiv.symm.nontrivial
  obtain ⟨hnoeth, hart⟩ := isFiniteLength_iff_isNoetherian_isArtinian.mp hfin
  let := hnoeth
  let := hart
  intro hsurj
  have hinj : Function.Injective (centralDefect ρ z c) :=
    IsNoetherian.injective_of_surjective_endomorphism
      (Representation.IntertwiningMap.equivLinearMapAsModule _ _ (centralDefect ρ z c)) hsurj
  obtain ⟨S, q, hq⟩ := hocc
  have hartS : IsArtinian (MonoidAlgebra R G) S.toRepresentation.asModule :=
    isArtinian_of_injective
      (Representation.IntertwiningMap.equivLinearMapAsModule _ _ (inclusion ρ S))
      (Submodule.injective_subtype _)
  let := hartS
  have hinjS : Function.Injective (centralDefect S.toRepresentation z c) := by
    intro v w h
    apply Subtype.ext
    exact hinj (congrArg Subtype.val h)
  have hsurjS : Function.Surjective (centralDefect S.toRepresentation z c) :=
    IsArtinian.surjective_of_injective_endomorphism
      (Representation.IntertwiningMap.equivLinearMapAsModule _ _
        (centralDefect S.toRepresentation z c)) hinjS
  have hzero (v : S.toSubmodule) : q (centralDefect S.toRepresentation z c v) = 0 := by
    change q (S.toRepresentation z v - c • v) = 0
    rw [map_sub, map_smul, Representation.IntertwiningMap.isIntertwining _ _ q, hσz, sub_self]
  obtain ⟨w, hw⟩ := exists_ne (0 : W)
  obtain ⟨v, hv⟩ := hq w
  obtain ⟨x, hx⟩ := hsurjS v
  apply hw
  rw [← hv, ← hx]
  exact hzero x

private theorem quotient_exists
    (ρ : Representation R G V) (σ : Representation R G W)
    (χ : Subgroup.center G → R)
    (hfin : IsFiniteLength (MonoidAlgebra R G) ρ.asModule)
    (hσ : σ.IsIrreducible) (hχ : ∀ (z : Subgroup.center G) w, σ z w = χ z • w)
    (hscalar : ∀ {U : Type uV} [AddCommGroup U] [Module R U]
      (τ : Representation R G U) (p : ρ.IntertwiningMap τ),
      Function.Surjective p →
      (∀ (z : Subgroup.center G) u, τ z u = χ z • u) →
      (∃ S : Subrepresentation τ,
        ∃ q : S.toRepresentation.IntertwiningMap σ, Function.Surjective q) →
      ∃ q : τ.IntertwiningMap σ, Function.Surjective q)
    (hocc : ∃ S : Subrepresentation ρ,
      ∃ q : S.toRepresentation.IntertwiningMap σ, Function.Surjective q) :
    ∃ q : ρ.IntertwiningMap σ, Function.Surjective q := by
  classical
  have key : ∀ n : ℕ, ∀ {U : Type uV} [AddCommGroup U] [Module R U]
      (τ : Representation R G U) (p : ρ.IntertwiningMap τ),
      Function.Surjective p → (repLength τ).toNat = n →
      (∃ S : Subrepresentation τ,
        ∃ q : S.toRepresentation.IntertwiningMap σ, Function.Surjective q) →
      ∃ q : τ.IntertwiningMap σ, Function.Surjective q := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro U _ _ τ p hp hn hoccτ
      by_cases hτχ : ∀ (z : Subgroup.center G) u, τ z u = χ z • u
      · exact hscalar τ p hp hτχ hoccτ
      · push Not at hτχ
        obtain ⟨z, v, hv⟩ := hτχ
        let D := centralDefect τ z (χ z)
        let A := D.range
        let B := τ.quotient A.toSubmodule (fun g _ hu => A.apply_mem_toSubmodule g hu)
        let pA := rangeProjection D
        let pB := quotientProjection τ A
        have hpA : Function.Surjective pA := rangeProjection_surjective D
        have hpB : Function.Surjective pB := Submodule.mkQ_surjective A.toSubmodule
        have hfinτ : IsFiniteLength (MonoidAlgebra R G) τ.asModule :=
          hfin.of_surjective
            (f := Representation.IntertwiningMap.equivLinearMapAsModule _ _ p) hp
        have hfinA : IsFiniteLength (MonoidAlgebra R G) A.toRepresentation.asModule :=
          hfinτ.of_surjective
            (f := Representation.IntertwiningMap.equivLinearMapAsModule _ _ pA) hpA
        have hfinB : IsFiniteLength (MonoidAlgebra R G) B.asModule :=
          hfinτ.of_surjective
            (f := Representation.IntertwiningMap.equivLinearMapAsModule _ _ pB) hpB
        have hAfin : repLength A.toRepresentation ≠ ⊤ :=
          Module.length_ne_top_iff.mpr hfinA
        have hBfin : repLength B ≠ ⊤ :=
          Module.length_ne_top_iff.mpr hfinB
        have hAne : repLength A.toRepresentation ≠ 0 := by
          intro hzero
          let := repLength_eq_zero_iff.mp hzero
          have hz : (⟨D v, ⟨v, rfl⟩⟩ : A.toSubmodule) = 0 := Subsingleton.elim _ _
          have hz' : D v = 0 := congrArg Subtype.val hz
          apply hv
          exact sub_eq_zero.mp hz'
        have hD : ¬ Function.Surjective D :=
          centralDefect_not_surjective hfinτ hσ z (χ z) (hχ z) hoccτ
        have hBne : repLength B ≠ 0 := by
          intro hzero
          let := repLength_eq_zero_iff.mp hzero
          apply hD
          intro u
          have hu : A.toSubmodule.mkQ u = 0 := Subsingleton.elim _ _
          exact (Submodule.Quotient.mk_eq_zero A.toSubmodule).mp hu
        have hAnpos := ENat.toNat_pos hAne hAfin
        have hBnpos := ENat.toNat_pos hBne hBfin
        have hadd : n = (repLength A.toRepresentation).toNat + (repLength B).toNat := by
          rw [← hn, repLength_eq_subrepresentation_add_quotient τ A]
          exact ENat.toNat_add hAfin hBfin
        rcases occurrence_dichotomy hσ hoccτ A with hoccA | hoccB
        · obtain ⟨q, hq⟩ := ih (repLength A.toRepresentation).toNat (by omega)
            A.toRepresentation (pA.comp p) (hpA.comp hp) rfl hoccA
          exact ⟨q.comp pA, hq.comp hpA⟩
        · obtain ⟨q, hq⟩ := ih (repLength B).toNat (by omega)
            B (pB.comp p) (hpB.comp hp) rfl hoccB
          exact ⟨q.comp pB, hq.comp hpB⟩
  exact key (repLength ρ).toNat ρ (Representation.IntertwiningMap.id ρ)
    Function.surjective_id rfl hocc

end Langlands.ScalarQuotientReduction

namespace Langlands

universe uR uG uV uW

/-- Reduce quotient extraction to quotients on which the full center acts by
the prescribed scalar function, using finite composition length. -/
noncomputable def quotientOfScalarCentralQuotients
    {R : Type uR} [Field R] {G : Type uG} [Group G]
    {V : Type uV} {W : Type uW}
    [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W]
    (ρ : Representation R G V) (σ : Representation R G W)
    (χ : Subgroup.center G → R)
    (hfin : IsFiniteLength (MonoidAlgebra R G) ρ.asModule)
    (hσ : σ.IsIrreducible) (hχ : ∀ (z : Subgroup.center G) w, σ z w = χ z • w)
    (hscalar : ∀ {U : Type uV} [AddCommGroup U] [Module R U]
      (τ : Representation R G U) (p : ρ.IntertwiningMap τ),
      Function.Surjective p →
      (∀ (z : Subgroup.center G) u, τ z u = χ z • u) →
      (∃ S : Subrepresentation τ,
        ∃ q : S.toRepresentation.IntertwiningMap σ, Function.Surjective q) →
      ∃ q : τ.IntertwiningMap σ, Function.Surjective q)
    (hocc : ∃ S : Subrepresentation ρ,
      ∃ q : S.toRepresentation.IntertwiningMap σ, Function.Surjective q) :
    {q : ρ.IntertwiningMap σ // Function.Surjective q} :=
  ⟨Classical.choose (ScalarQuotientReduction.quotient_exists ρ σ χ hfin hσ hχ hscalar hocc),
    Classical.choose_spec
      (ScalarQuotientReduction.quotient_exists ρ σ χ hfin hσ hχ hscalar hocc)⟩

end Langlands
