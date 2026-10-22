import Langlands.Representation.Filtration.ObjectDefinitions
import Mathlib.RingTheory.Length

/-!
# Composition length of actual representations

The length of a representation is Mathlib's module length of its module over
the monoid algebra. It is additive on short exact sequences of actual
intertwiners, invariant under actual equivalences, zero exactly on zero
representations, one exactly on irreducible representations, and it adds up
along every finite object filtration.
-/

open scoped MonoidAlgebra

namespace Langlands

universe uK uG uU uV uW

variable {k : Type uK} {G : Type uG} [Field k] [Monoid G]
  {U : Type uU} {V : Type uV} {W : Type uW}
  [AddCommGroup U] [Module k U] [AddCommGroup V] [Module k V]
  [AddCommGroup W] [Module k W]

/-- The composition length of an actual representation: the module length of
its module over the monoid algebra, with value `⊤` for infinite length. -/
noncomputable def repLength (ρ : Representation k G V) : ℕ∞ :=
  Module.length k[G] ρ.asModule

/-- An actual equivalence of representations as a linear equivalence of the
monoid-algebra modules, with the same underlying functions. -/
noncomputable def repAsModuleEquiv {ρ : Representation k G V}
    {σ : Representation k G W} (e : ρ.Equiv σ) :
    ρ.asModule ≃ₗ[k[G]] σ.asModule :=
  { Representation.IntertwiningMap.equivLinearMapAsModule ρ σ e.toIntertwiningMap with
    invFun := e.symm
    left_inv := e.symm_apply_apply
    right_inv := e.apply_symm_apply }

/-- Length is invariant under actual equivalences, across carrier universes. -/
theorem repLength_congr {ρ : Representation k G V} {σ : Representation k G W}
    (e : ρ.Equiv σ) : repLength ρ = repLength σ :=
  (repAsModuleEquiv e).length_eq

/-- Length is additive on a short exact sequence of actual intertwiners. -/
theorem repLength_eq_add_of_exact {ρ : Representation k G U}
    {σ : Representation k G V} {τ : Representation k G W}
    (f : ρ.IntertwiningMap σ) (g : σ.IntertwiningMap τ)
    (hf : Function.Injective f) (hg : Function.Surjective g)
    (hfg : LinearMap.range f.toLinearMap = LinearMap.ker g.toLinearMap) :
    repLength σ = repLength ρ + repLength τ := by
  have H : Function.Exact f.toLinearMap g.toLinearMap :=
    LinearMap.exact_iff.mpr hfg.symm
  exact Module.length_eq_add_of_exact
    (Representation.IntertwiningMap.equivLinearMapAsModule ρ σ f)
    (Representation.IntertwiningMap.equivLinearMapAsModule σ τ g) hf hg H

/-- A representation has length zero exactly when its carrier is zero. -/
theorem repLength_eq_zero_iff {ρ : Representation k G V} :
    repLength ρ = 0 ↔ Subsingleton V :=
  Module.length_eq_zero_iff

/-- A representation has positive length exactly when its carrier is nonzero. -/
theorem repLength_pos_iff {ρ : Representation k G V} :
    0 < repLength ρ ↔ Nontrivial V :=
  Module.length_pos_iff

/-- A representation has length one exactly when it is irreducible. -/
theorem repLength_eq_one_iff {ρ : Representation k G V} :
    repLength ρ = 1 ↔ ρ.IsIrreducible := by
  rw [Representation.irreducible_iff_isSimpleModule_asModule]
  exact Module.length_eq_one_iff

/-- The length of an invariant subspace plus that of the actual quotient. -/
theorem repLength_eq_subrepresentation_add_quotient (ρ : Representation k G V)
    (S : Subrepresentation ρ) :
    repLength ρ = repLength S.toRepresentation +
      repLength (ρ.quotient S.toSubmodule (fun g _ hv => S.apply_mem_toSubmodule g hv)) := by
  let f : S.toRepresentation.IntertwiningMap ρ :=
    { toLinearMap := S.toSubmodule.subtype
      isIntertwining' := fun _ => rfl }
  let q : ρ.IntertwiningMap
      (ρ.quotient S.toSubmodule (fun g _ hv => S.apply_mem_toSubmodule g hv)) :=
    { toLinearMap := S.toSubmodule.mkQ
      isIntertwining' := fun _ => rfl }
  refine repLength_eq_add_of_exact f q (Submodule.injective_subtype _)
    (Submodule.mkQ_surjective _) ?_
  change LinearMap.range S.toSubmodule.subtype = LinearMap.ker S.toSubmodule.mkQ
  rw [Submodule.range_subtype, Submodule.ker_mkQ]

/-- The whole invariant subspace has the length of the representation. -/
theorem repLength_top (ρ : Representation k G V) :
    repLength (⊤ : Subrepresentation ρ).toRepresentation = repLength ρ := by
  refine repLength_congr
    { toLinearMap := (⊤ : Subrepresentation ρ).toSubmodule.subtype
      isIntertwining' := fun _ => rfl
      invFun := fun v => ⟨v, trivial⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

/-- The zero invariant subspace has length zero. -/
theorem repLength_bot (ρ : Representation k G V) :
    repLength (⊥ : Subrepresentation ρ).toRepresentation = 0 := by
  rw [repLength_eq_zero_iff]
  constructor
  rintro ⟨a, ha⟩ ⟨b, hb⟩
  have ha' : a = 0 := ha
  have hb' : b = 0 := hb
  subst ha' hb'
  rfl

/-- In a finite object filtration, each step is the previous step plus the
corresponding graded quotient. -/
theorem repLength_filtration_step {A : Rep.{uV} k G} {n : ℕ}
    (s : ObjectRepFiltration A n) (i : Fin n) :
    repLength (s.subrepresentation i.succ).toRepresentation =
      repLength (s.subrepresentation i.castSucc).toRepresentation +
        repLength (s.gradedRepresentation i).ρ := by
  have hle : s.subrepresentation i.castSucc ≤ s.subrepresentation i.succ :=
    s.monotone_subrepresentation (Fin.castSucc_le_succ i)
  let f : (s.subrepresentation i.castSucc).toRepresentation.IntertwiningMap
      (s.subrepresentation i.succ).toRepresentation :=
    { toLinearMap := Submodule.inclusion hle
      isIntertwining' := fun _ => rfl }
  let q := (s.gradedProjection i).hom
  refine repLength_eq_add_of_exact f q (Submodule.inclusion_injective hle)
    (s.gradedProjection_surjective i) ?_
  ext ⟨v, hv⟩
  constructor
  · rintro ⟨⟨w, hw⟩, hwv⟩
    have hvw : v = w := (congrArg Subtype.val hwv).symm
    subst hvw
    change Submodule.Quotient.mk _ = 0
    exact (Submodule.Quotient.mk_eq_zero _).mpr hw
  · intro hq
    change Submodule.Quotient.mk _ = 0 at hq
    have hq' := (Submodule.Quotient.mk_eq_zero _).mp hq
    exact ⟨⟨v, hq'⟩, rfl⟩

/-- Length adds up along every finite object filtration. -/
theorem repLength_eq_sum_of_filtration {A : Rep.{uV} k G} {n : ℕ}
    (s : ObjectRepFiltration A n) :
    repLength A.ρ = ∑ i : Fin n, repLength (s.gradedRepresentation i).ρ := by
  have key : ∀ j : ℕ, (hj : j ≤ n) →
      repLength (s.subrepresentation ⟨j, Nat.lt_succ_of_le hj⟩).toRepresentation =
        ∑ i : Fin j, repLength (s.gradedRepresentation
          ⟨i, lt_of_lt_of_le i.isLt hj⟩).ρ := by
    intro j
    induction j with
    | zero =>
      intro hj
      have h0 : s.subrepresentation ⟨0, Nat.lt_succ_of_le hj⟩ = ⊥ :=
        s.subrepresentation_zero
      simp only [Finset.univ_eq_empty, Finset.sum_empty]
      rw [h0]
      exact repLength_bot A.ρ
    | succ j ih =>
      intro hj
      have hjn : j < n := hj
      rw [Fin.sum_univ_castSucc]
      simp only [Fin.val_castSucc, Fin.val_last]
      rw [← ih hjn.le]
      exact repLength_filtration_step s ⟨j, hjn⟩
  have h := key n le_rfl
  have hl : (⟨n, Nat.lt_succ_of_le le_rfl⟩ : Fin (n + 1)) = Fin.last n := rfl
  rw [hl, s.subrepresentation_last, repLength_top] at h
  exact h

/-- A filtration with irreducible graded quotients has length its number of
steps. -/
theorem repLength_eq_of_hasSimpleFactors {A : Rep.{uV} k G} {n : ℕ}
    (s : ObjectRepFiltration A n) (hs : s.HasSimpleFactors) :
    repLength A.ρ = n := by
  rw [repLength_eq_sum_of_filtration s]
  simp only [fun i => repLength_eq_one_iff.mpr (hs i), Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]

end Langlands
