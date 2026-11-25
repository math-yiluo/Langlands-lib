/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.Order.OrderIsoNat
public import Mathlib.RepresentationTheory.Irreducible
public import Mathlib.RingTheory.SimpleModule.Basic
public import WeilConjectures.Mathlib.RepresentationTheory.Subrepresentation

/-!
# Constituents of a representation

The constituents of a finite-dimensional representation are the irreducible successive
quotients of a composition series, counted with multiplicity; equivalently, by Jordan-Hölder,
the irreducible subquotients. Irreducibility itself is `Representation.IsIrreducible`.

`Representation.IsConstituent` forgets the multiplicity, being a `Prop`. Invariants of the
composition factors counted with multiplicity are recorded by
`Subrepresentation.factorMultiset` (in `WeilConjectures.RepresentationTheory.CompositionFactors`);
the rank `N_γ` and the weight sum `B_γ` of blueprint `definition-determinant-weight--1` are sums
over it.

## Main definitions

- `Representation.IsConstituent`
- `Representation.Equiv.asModuleLinearEquiv`, `Representation.Equiv.ofAsModuleLinearEquiv`:
  equivalences of representations are the `k[G]`-linear equivalences of the associated modules.
- `Subrepresentation.subquotientAsModuleLinearEquiv`: the subquotient `M ⧸ N` of two
  subrepresentations is the quotient of the associated `k[G]`-submodules.

## Main statements

- `Representation.isIrreducible_iff`: `ρ` is irreducible if and only if `V` is nonzero and its
  only invariant subspaces are `0` and `V` (blueprint: `def-wf-simple-module`).
- `Subrepresentation.isIrreducible_subquotient_iff`: the subquotient `M ⧸ N` is irreducible if
  and only if `M` covers `N`.
- `Representation.IsConstituent.exists_covBy`: a constituent is equivalent to the subquotient of
  a covering pair of subrepresentations.
- `Subrepresentation.exists_covBy_chain`: a covering pair of subrepresentations of a
  finite-dimensional representation is a step of a composition series.
- `Representation.IsIrreducible.dual`: the contragredient of a finite-dimensional irreducible
  representation is irreducible.
-/

@[expose] public section

namespace Representation

variable {k G V V' : Type*} [Field k] [Monoid G]
  [AddCommGroup V] [Module k V] [AddCommGroup V'] [Module k V']

/-- Blueprint `definition-weil-representation`: Operations, constituents and coinvariants.

`σ.IsConstituent ρ` says that `σ` is a *constituent* of `ρ`: it is irreducible and isomorphic
to a subquotient of `ρ`. By Jordan-Hölder these are exactly the irreducible successive
quotients of a composition series of `ρ`. -/
def IsConstituent (σ : Representation k G V') (ρ : Representation k G V) : Prop :=
  σ.IsIrreducible ∧ ∃ N M : Subrepresentation ρ, N ≤ M ∧
    Nonempty (σ.asModule ≃ₗ[MonoidAlgebra k G]
      (M.asSubmodule ⧸ Submodule.comap M.asSubmodule.subtype N.asSubmodule))

end Representation

namespace Representation

open scoped MonoidAlgebra

variable {k G V W : Type*} [Field k] [Group G] [AddCommGroup V] [Module k V] [AddCommGroup W]
  [Module k W] {ρ : Representation k G V} {σ : Representation k G W}

/-- An equivalence of representations is a `k[G]`-linear equivalence of the associated
`k[G]`-modules. -/
noncomputable def Equiv.asModuleLinearEquiv (e : ρ.Equiv σ) : ρ.asModule ≃ₗ[k[G]] σ.asModule :=
  LinearEquiv.ofLinearMap (IntertwiningMap.equivLinearMapAsModule ρ σ e.toIntertwiningMap)
    (IntertwiningMap.equivLinearMapAsModule σ ρ e.symm.toIntertwiningMap)
    (LinearMap.ext fun x ↦ e.apply_symm_apply x) (LinearMap.ext fun x ↦ e.symm_apply_apply x)

/-- A `k[G]`-linear equivalence of the associated `k[G]`-modules is an equivalence of
representations. -/
noncomputable def Equiv.ofAsModuleLinearEquiv (e : ρ.asModule ≃ₗ[k[G]] σ.asModule) :
    ρ.Equiv σ :=
  Equiv.mk ((ρ.asModuleEquiv.symm.trans (e.restrictScalars k)).trans σ.asModuleEquiv) fun g ↦ by
    ext v
    change σ.asModuleEquiv (e (ρ.asModuleEquiv.symm (ρ g v))) =
      σ g (σ.asModuleEquiv (e (ρ.asModuleEquiv.symm v)))
    rw [asModuleEquiv_symm_map_rho, map_smul, asModuleEquiv_map_smul, asAlgebraHom_of]

end Representation

namespace Subrepresentation

open scoped MonoidAlgebra

open Representation

variable {k G V : Type*} [Field k] [Group G] [AddCommGroup V] [Module k V]
  {ρ : Representation k G V}

/-- The subquotient `M ⧸ N` of two subrepresentations, viewed as a `k[G]`-module, is the
quotient of the associated `k[G]`-submodules. -/
noncomputable def subquotientAsModuleLinearEquiv (M N : Subrepresentation ρ) :
    (M.subquotient N).asModule ≃ₗ[k[G]]
      (M.asSubmodule ⧸ N.asSubmodule.comap M.asSubmodule.subtype) := by
  let Q := N.asSubmodule.comap M.asSubmodule.subtype
  let P := N.toSubmodule.comap M.toSubmodule.subtype
  let φ : M.toSubmodule →ₗ[k] (M.asSubmodule ⧸ Q) :=
    { toFun x := Submodule.Quotient.mk ⟨ρ.asModuleEquiv.symm x, x.2⟩
      map_add' x y := Submodule.Quotient.mk_add _
      map_smul' c x := by
        rw [RingHom.id_apply, ← Submodule.Quotient.mk_smul]
        exact congrArg Submodule.Quotient.mk
          (Subtype.ext (map_smul ρ.asModuleEquiv.symm c (x : V))) }
  let ψ : (M.toSubmodule ⧸ P) →ₗ[k] (M.asSubmodule ⧸ Q) :=
    P.liftQ φ fun x hx ↦ (Submodule.Quotient.mk_eq_zero _).2 hx
  let fwd₀ : M.asSubmodule →ₗ[k] (M.subquotient N).asModule :=
    { toFun y := (M.subquotient N).asModuleEquiv.symm
        (Submodule.Quotient.mk ⟨ρ.asModuleEquiv y, y.2⟩)
      map_add' x y := by
        rw [← map_add, ← Submodule.Quotient.mk_add]
        rfl
      map_smul' c y := by
        rw [RingHom.id_apply, ← map_smul, ← Submodule.Quotient.mk_smul]
        rfl }
  let fwd : M.asSubmodule →ₗ[k[G]] (M.subquotient N).asModule :=
    MonoidAlgebra.equivariantOfLinearOfComm fwd₀ fun g y ↦ by
      apply (M.subquotient N).asModuleEquiv.injective
      rw [asModuleEquiv_map_smul, asAlgebraHom_single_one]
      change Submodule.Quotient.mk _ = (M.subquotient N) g (Submodule.Quotient.mk _)
      refine congrArg Submodule.Quotient.mk (Subtype.ext ?_)
      change ρ.asModuleEquiv (MonoidAlgebra.single g 1 • (y : ρ.asModule)) = _
      rw [asModuleEquiv_map_smul, asAlgebraHom_single_one]
      rfl
  let fwdQ : (M.asSubmodule ⧸ Q) →ₗ[k[G]] (M.subquotient N).asModule :=
    Q.liftQ fwd fun x hx ↦
      ((M.subquotient N).asModuleEquiv.symm.map_eq_zero_iff).2
        ((Submodule.Quotient.mk_eq_zero _).2 hx)
  refine LinearEquiv.symm
    { fwdQ with
      invFun x := ψ ((M.subquotient N).asModuleEquiv x)
      left_inv x := ?_
      right_inv x := ?_ }
  · induction x using Submodule.Quotient.induction_on with
    | H y => rfl
  · obtain ⟨y, rfl⟩ := (M.subquotient N).asModuleEquiv.symm.surjective x
    induction y using Submodule.Quotient.induction_on with
    | H y => rfl

/-- For subrepresentations `N ≤ M`, the subquotient `M ⧸ N` is irreducible if and only if `M`
covers `N`. -/
theorem isIrreducible_subquotient_iff {M N : Subrepresentation ρ} (h : N ≤ M) :
    (M.subquotient N).IsIrreducible ↔ N ⋖ M := by
  let e := M.subquotientAsModuleLinearEquiv N
  rw [irreducible_iff_isSimpleModule_asModule,
    ← apply_covBy_apply_iff (subrepresentationSubmoduleOrderIso (ρ := ρ)),
    subrepresentationSubmoduleOrderIso_apply, subrepresentationSubmoduleOrderIso_apply,
    covBy_iff_quot_is_simple (show N.asSubmodule ≤ M.asSubmodule from h)]
  exact ⟨fun _ ↦ IsSimpleModule.congr e.symm, fun _ ↦ IsSimpleModule.congr e⟩

/-- In a finite-dimensional representation, every covering pair `N ⋖ M` of subrepresentations
is a step of a composition series: a chain `0 = F 0 ⋖ F 1 ⋖ ⋯ ⋖ F n = ρ` with `F i₀ = N` and
`F (i₀ + 1) = M`. -/
theorem exists_covBy_chain [FiniteDimensional k V] {M N : Subrepresentation ρ} (h : N ⋖ M) :
    ∃ (n : ℕ) (F : ℕ → Subrepresentation ρ) (i₀ : ℕ), F 0 = ⊥ ∧ F n = ⊤ ∧
      (∀ i < n, F i ⋖ F (i + 1)) ∧ i₀ < n ∧ F i₀ = N ∧ F (i₀ + 1) = M := by
  have : WellFoundedLT (Subrepresentation ρ) :=
    Subrelation.wf (r := fun a b ↦ a.toSubmodule < b.toSubmodule) (fun h ↦ h)
      (InvImage.wf _ wellFounded_lt)
  have : WellFoundedGT (Subrepresentation ρ) :=
    Subrelation.wf (r := fun a b ↦ b.toSubmodule < a.toSubmodule) (fun h ↦ h)
      (InvImage.wf _ wellFounded_gt)
  obtain ⟨a, ha₀, n₁, hn₁, ha⟩ :=
    exists_covBy_seq_of_wellFoundedLT_wellFoundedGT_of_le (bot_le : ⊥ ≤ N)
  obtain ⟨b, hb₀, n₂, hn₂, hb⟩ :=
    exists_covBy_seq_of_wellFoundedLT_wellFoundedGT_of_le (le_top : M ≤ ⊤)
  refine ⟨n₁ + 1 + n₂, fun i ↦ if i ≤ n₁ then a i else b (i - (n₁ + 1)), n₁, by simp [ha₀], ?_,
    fun i hi ↦ ?_, by omega, by simp [hn₁], by simp [hb₀]⟩
  · dsimp only
    rw [ite_eq_right (by omega), show n₁ + 1 + n₂ - (n₁ + 1) = n₂ by omega, hn₂]
  · dsimp only
    rcases lt_trichotomy i n₁ with hi₁ | rfl | hi₁
    · rw [ite_eq_left hi₁.le, ite_eq_left (by omega)]
      exact ha i hi₁
    · rw [ite_eq_left le_rfl, ite_eq_right (by omega), hn₁, Nat.sub_self, hb₀]
      exact h
    · rw [ite_eq_right (by omega), ite_eq_right (by omega),
        show i + 1 - (n₁ + 1) = i - (n₁ + 1) + 1 by omega]
      exact hb _ (by omega)

end Subrepresentation

namespace Representation

open scoped MonoidAlgebra

variable {k G V W : Type*} [Field k] [Group G] [AddCommGroup V] [Module k V] [AddCommGroup W]
  [Module k W] {ρ : Representation k G V} {σ : Representation k G W}

/-- A constituent of `ρ` is equivalent to the subquotient `M ⧸ N` of a covering pair `N ⋖ M`
of subrepresentations of `ρ`. -/
theorem IsConstituent.exists_covBy (hσ : σ.IsConstituent ρ) :
    ∃ N M : Subrepresentation ρ, N ⋖ M ∧ Nonempty (σ.Equiv (M.subquotient N)) := by
  obtain ⟨hirr, N, M, hNM, ⟨e⟩⟩ := hσ
  let E : σ.Equiv (M.subquotient N) :=
    Equiv.ofAsModuleLinearEquiv (e.trans (M.subquotientAsModuleLinearEquiv N).symm)
  exact ⟨N, M, (Subrepresentation.isIrreducible_subquotient_iff hNM).1
    (E.isIrreducible_iff.1 hirr), ⟨E⟩⟩

end Representation

namespace Representation

variable {k G V : Type*} [Field k] [Monoid G] [AddCommGroup V] [Module k V]

/-- A representation is irreducible if and only if `V` is nonzero and its only invariant
subspaces are `0` and `V`. (blueprint: `def-wf-simple-module`) -/
theorem isIrreducible_iff {ρ : Representation k G V} :
    ρ.IsIrreducible ↔
      Nontrivial V ∧ ∀ U : Submodule k V, (∀ g, ∀ v ∈ U, ρ g v ∈ U) → U = ⊥ ∨ U = ⊤ := by
  constructor
  · intro h
    refine ⟨not_subsingleton_iff_nontrivial.1 fun _ ↦ h.bot_ne_top ?_, fun U hU ↦ ?_⟩
    · ext x
      simp [Subsingleton.elim x 0]
    · exact (IsSimpleOrder.eq_bot_or_eq_top (⟨U, fun g v hv ↦ hU g v hv⟩ :
        Subrepresentation ρ)).imp (congrArg Subrepresentation.toSubmodule)
        (congrArg Subrepresentation.toSubmodule)
  · rintro ⟨hV, h⟩
    have : Nontrivial (Subrepresentation ρ) :=
      ⟨⊥, ⊤, fun e ↦ bot_ne_top (congrArg Subrepresentation.toSubmodule e)⟩
    exact ⟨fun U ↦ (h U.toSubmodule fun g v hv ↦ U.apply_mem_toSubmodule g hv).imp
      (fun e ↦ Subrepresentation.toSubmodule_injective e)
      (fun e ↦ Subrepresentation.toSubmodule_injective e)⟩

end Representation

namespace Representation

variable {k G H V W : Type*} [Field k] [Group G] [Group H] [AddCommGroup V] [Module k V]
  [AddCommGroup W] [Module k W] {ρ : Representation k G V} {σ : Representation k G W}

/-- **Schur's scalar lemma.** An endomorphism `c` of a finite-dimensional irreducible representation
over an algebraically closed field commuting with the action is a scalar `a • 1` for a unique
`a`: an eigenspace of `c` is a nonzero subrepresentation, hence everything.
(blueprint: `proposition-central-element-arithmetic-monodromy-group--2`) -/
theorem IsIrreducible.existsUnique_eq_smul_id [IsAlgClosed k] [FiniteDimensional k V]
    (hρ : ρ.IsIrreducible) (c : Module.End k V)
    (hc : ∀ g, c ∘ₗ ρ g = ρ g ∘ₗ c) : ∃! a : k, c = a • LinearMap.id := by
  have := hρ.nontrivial
  obtain ⟨a, ha⟩ := Module.End.exists_eigenvalue c
  let E : Subrepresentation ρ :=
    ⟨Module.End.eigenspace c a, fun g v hv ↦ by
      rw [Module.End.mem_eigenspace_iff] at hv ⊢
      rw [← LinearMap.comp_apply, hc, LinearMap.comp_apply, hv, map_smul]⟩
  have hE : E ≠ ⊥ := fun h ↦ Module.End.hasEigenvalue_iff.1 ha
    (congrArg Subrepresentation.toSubmodule h)
  have htop : E = ⊤ := (hρ.eq_bot_or_eq_top E).resolve_left hE
  refine ⟨a, LinearMap.ext fun v ↦ ?_, fun b hb ↦ ?_⟩
  · have hv : v ∈ E := htop ▸ Submodule.mem_top
    exact Module.End.mem_eigenspace_iff.1 hv
  · obtain ⟨v, hv⟩ := exists_ne (0 : V)
    have h1 : c v = a • v := Module.End.mem_eigenspace_iff.1 (htop ▸ Submodule.mem_top : v ∈ E)
    rw [hb, LinearMap.smul_apply, LinearMap.id_apply] at h1
    exact smul_left_injective k hv h1

/-- An irreducible representation equivalent to a subquotient `M ⧸ N` of `ρ` is a constituent
of `ρ`. -/
theorem isConstituent_of_equiv_subquotient (hσ : σ.IsIrreducible) {N M : Subrepresentation ρ}
    (h : N ≤ M) (e : σ.Equiv (M.subquotient N)) : σ.IsConstituent ρ :=
  ⟨hσ, N, M, h, ⟨e.asModuleLinearEquiv.trans (M.subquotientAsModuleLinearEquiv N)⟩⟩

/-- Restricting an irreducible representation along a surjective homomorphism keeps it
irreducible: both have the same invariant subspaces. -/
theorem IsIrreducible.comp (hσ : σ.IsIrreducible) {f : H →* G} (hf : Function.Surjective f) :
    Representation.IsIrreducible (σ.comp f) := by
  rw [isIrreducible_iff] at hσ ⊢
  refine ⟨hσ.1, fun U hU ↦ hσ.2 U fun g v hv ↦ ?_⟩
  obtain ⟨h, rfl⟩ := hf g
  exact hU h v hv

/-- A constituent of `ρ` restricted along a surjective homomorphism `f` is a constituent of the
restriction of `ρ`: subrepresentations of `ρ` are subrepresentations of `ρ ∘ f`, with the same
subquotients. -/
theorem IsConstituent.comp (hσ : σ.IsConstituent ρ) {f : H →* G} (hf : Function.Surjective f) :
    Representation.IsConstituent (σ.comp f) (ρ.comp f) := by
  obtain ⟨N, M, hNM, ⟨e⟩⟩ := hσ.exists_covBy
  let N' : Subrepresentation (ρ.comp f) := ⟨N.toSubmodule, fun h _ hv ↦ N.apply_mem_toSubmodule
    (f h) hv⟩
  let M' : Subrepresentation (ρ.comp f) := ⟨M.toSubmodule, fun h _ hv ↦ M.apply_mem_toSubmodule
    (f h) hv⟩
  refine isConstituent_of_equiv_subquotient (hσ.1.comp hf) (N := N') (M := M') hNM.le
    (Equiv.mk e.toLinearEquiv fun h ↦ ?_)
  exact e.isIntertwining' (f h)

end Representation

namespace Representation

variable {k G V : Type*} [Field k] [Group G] [AddCommGroup V] [Module k V]
  {ρ : Representation k G V}

/-- The contragredient of a finite-dimensional irreducible representation is irreducible: the
annihilator in `V` of an invariant subspace of `V^∨` is invariant, hence `0` or `V`.
(blueprint: part L3 of `lemma-tensor-exterior-powers-filtered-representations--3`) -/
theorem IsIrreducible.dual [FiniteDimensional k V] (h : ρ.IsIrreducible) :
    ρ.dual.IsIrreducible := by
  obtain ⟨hV, hU⟩ := isIrreducible_iff.1 h
  refine isIrreducible_iff.2 ⟨(Module.nontrivial_dual_iff k).2 hV, fun T hT ↦ ?_⟩
  have hC : ∀ g, ∀ v ∈ T.dualCoannihilator, ρ g v ∈ T.dualCoannihilator := fun g v hv ↦ by
    rw [Submodule.mem_dualCoannihilator] at hv ⊢
    intro f hf
    have := hv _ (hT g⁻¹ f hf)
    simp only [dual_apply, inv_inv] at this
    exact this
  rw [← Subspace.dualCoannihilator_dualAnnihilator_eq (W := T)]
  rcases hU _ hC with h | h <;> rw [h]
  · exact Or.inr Submodule.dualAnnihilator_bot
  · exact Or.inl Submodule.dualAnnihilator_top

end Representation
