import Langlands.WeilDeligne.BlockStatements
import Langlands.Representation.Category.FiniteIndexRestriction
import Mathlib.LinearAlgebra.TensorProduct.Pi

/-!
# Existence of block decompositions with semisimple Weil part

Proof of `Blocks.DecompositionExistence`. Inside the carrier of the pair, an
irreducible Weil subrepresentation `σ` on which `N^(m-1)` is injective, where `m`
is the nilpotency order on a stable subspace `U`, spans the copy
`v ⊗ e_j ↦ N^j v` of the block `σ ⊗ S_m`. A stable complement inside `U` is cut
out by a Weil-stable complement `T` of `N^(m-1) σ`. Strong induction on the
dimension of `U` gives finitely many embedded blocks spanning the carrier with
total dimension equal to its dimension, and their sum map is an isomorphism.
-/

noncomputable section

namespace Langlands.WeilDeligneRepresentation.Blocks

universe uG uV

open scoped TensorProduct

namespace DecompositionExistenceProof

variable {G : Type uG} [Group G] {ν : G →* ℂˣ}
  (A : WeilDeligneRepresentation.{0, uG, uV} ℂ G ν)

/-- Covariance in the form `r(g) N^j = ν(g)^j N^j r(g)`. -/
theorem representation_monodromy_pow (g : G) (j : ℕ) (v : A) :
    A.representation g ((A.monodromy ^ j) v) =
      (ν g : ℂ) ^ j • (A.monodromy ^ j) (A.representation g v) := by
  have h1 : ∀ w : A, A.representation g (A.monodromy w) =
      (ν g : ℂ) • A.monodromy (A.representation g w) := by
    intro w
    have h := LinearMap.congr_fun (A.covariance g) (A.representation g w)
    simp only [Module.End.mul_apply, LinearMap.smul_apply] at h
    rwa [← Module.End.mul_apply (A.representation g⁻¹), ← map_mul, inv_mul_cancel, map_one,
      Module.End.one_apply] at h
  induction j generalizing v with
  | zero => simp
  | succ j ih =>
    rw [pow_succ, Module.End.mul_apply, ih, h1, map_smul, smul_smul, ← pow_succ,
      Module.End.mul_apply]

/-- Powers of monodromy preserve a monodromy-stable subspace. -/
theorem monodromy_pow_mem {U : Submodule ℂ A} (hU : ∀ v ∈ U, A.monodromy v ∈ U) (j : ℕ)
    {v : A} (hv : v ∈ U) : (A.monodromy ^ j) v ∈ U := by
  induction j with
  | zero => simpa using hv
  | succ j ih =>
    rw [pow_succ', Module.End.mul_apply]
    exact hU _ ih

/-- The kernel of `N^n` is a Weil subrepresentation. -/
def kerPow (n : ℕ) : Subrepresentation A.representation where
  toSubmodule := LinearMap.ker (A.monodromy ^ n)
  apply_mem_toSubmodule g v hv := by
    have h := representation_monodromy_pow A g n v
    rw [LinearMap.mem_ker.mp hv, map_zero] at h
    exact LinearMap.mem_ker.mpr
      ((smul_eq_zero.mp h.symm).resolve_left (pow_ne_zero _ (Units.ne_zero _)))

/-- The image `N^n σ` of a Weil subrepresentation is a Weil subrepresentation. -/
def imagePow (σ : Subrepresentation A.representation) (n : ℕ) :
    Subrepresentation A.representation where
  toSubmodule := LinearMap.range ((A.monodromy ^ n) ∘ₗ σ.toSubmodule.subtype)
  apply_mem_toSubmodule g w hw := by
    obtain ⟨v, rfl⟩ := LinearMap.mem_range.mp hw
    refine LinearMap.mem_range.mpr
      ⟨(ν g : ℂ) ^ n • ⟨A.representation g v, σ.apply_mem_toSubmodule g v.property⟩, ?_⟩
    simp only [LinearMap.comp_apply, Submodule.subtype_apply, map_smul]
    exact (representation_monodromy_pow A g n v).symm

/-- In finite dimension the lattice of subrepresentations is well founded. -/
theorem wellFoundedLT_subrepresentation :
    WellFoundedLT (Subrepresentation A.representation) :=
  let emb : Subrepresentation A.representation ↪o Submodule ℂ A :=
    ⟨⟨Subrepresentation.toSubmodule, Subrepresentation.toSubmodule_injective⟩, Iff.rfl⟩
  emb.wellFoundedLT

variable {A}

/-- The linear map `f ↦ Σ_j N^j (f j)` on `m` copies of a Weil subrepresentation. -/
def sumMap (σ : Subrepresentation A.representation) (m : ℕ) :
    (Fin m → σ.toSubmodule) →ₗ[ℂ] A :=
  ∑ j : Fin m, (A.monodromy ^ (j : ℕ)) ∘ₗ σ.toSubmodule.subtype ∘ₗ LinearMap.proj j

theorem sumMap_apply (σ : Subrepresentation A.representation) (m : ℕ)
    (f : Fin m → σ.toSubmodule) :
    sumMap σ m f = ∑ j : Fin m, (A.monodromy ^ (j : ℕ)) (f j : A) := by
  simp [sumMap]

/-- The block map `v ⊗ w ↦ Σ_j w_j N^j v` on `σ ⊗ S_m`. -/
def blockLinear (σ : Subrepresentation A.representation) (m : ℕ) :
    block ν (FiniteRepresentation.of σ.toRepresentation) m →ₗ[ℂ] A :=
  sumMap σ m ∘ₗ (TensorProduct.piScalarRight ℂ ℂ σ.toSubmodule (Fin m)).toLinearMap

theorem blockLinear_tmul (σ : Subrepresentation A.representation) (m : ℕ)
    (x : σ.toSubmodule) (w : Fin m → ℂ) :
    blockLinear σ m (x ⊗ₜ[ℂ] w : block ν (FiniteRepresentation.of σ.toRepresentation) m) =
      ∑ j : Fin m, w j • (A.monodromy ^ (j : ℕ)) (x : A) := by
  change sumMap σ m (TensorProduct.piScalarRight ℂ ℂ σ.toSubmodule (Fin m) (x ⊗ₜ[ℂ] w)) = _
  rw [TensorProduct.piScalarRight_apply, TensorProduct.piScalarRightHom_tmul, sumMap_apply]
  simp

theorem blockLinear_injective (σ : Subrepresentation A.representation) (m : ℕ)
    (h : Function.Injective (sumMap σ m)) :
    Function.Injective (blockLinear (ν := ν) σ m) :=
  h.comp (TensorProduct.piScalarRight ℂ ℂ σ.toSubmodule (Fin m)).injective

theorem range_blockLinear (σ : Subrepresentation A.representation) (m : ℕ) :
    LinearMap.range (blockLinear (ν := ν) σ m) = LinearMap.range (sumMap σ m) :=
  LinearMap.range_comp_of_range_eq_top _
    (LinearEquiv.range (TensorProduct.piScalarRight ℂ ℂ σ.toSubmodule (Fin m)))

/-- The embedded block, when `N^m` kills `σ`. -/
def pieceHom (σ : Subrepresentation A.representation) (m : ℕ)
    (hnil : ∀ v ∈ σ.toSubmodule, (A.monodromy ^ m) v = 0) :
    Hom (block ν (FiniteRepresentation.of σ.toRepresentation) m) A where
  intertwiner :=
    { toLinearMap := blockLinear σ m
      isIntertwining' := fun g => by
        apply TensorProduct.ext'
        intro (x : σ.toSubmodule) (w : Fin m → ℂ)
        change blockLinear σ m ((σ.toRepresentation g x) ⊗ₜ[ℂ] (Special.action ν m g w)) =
          A.representation g (blockLinear σ m (x ⊗ₜ[ℂ] w))
        rw [blockLinear_tmul, blockLinear_tmul, map_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [map_smul, representation_monodromy_pow, Special.action_apply, smul_smul, mul_comm]
        rfl }
  comm_monodromy := by
    apply TensorProduct.ext'
    intro (x : σ.toSubmodule) (w : Fin m → ℂ)
    change blockLinear σ m ((block ν (FiniteRepresentation.of σ.toRepresentation) m).monodromy
      (x ⊗ₜ[ℂ] w)) = A.monodromy (blockLinear σ m (x ⊗ₜ[ℂ] w))
    rw [block_monodromy_tmul]
    erw [blockLinear_tmul (ν := ν) σ m x (Special.raising ℂ m w)]
    rw [blockLinear_tmul, map_sum]
    cases m with
    | zero => simp
    | succ n =>
      rw [Fin.sum_univ_succ, Fin.sum_univ_castSucc]
      have hlast : A.monodromy (w (Fin.last n) • (A.monodromy ^ ((Fin.last n : Fin (n + 1)) :
          ℕ)) (x : A)) = 0 := by
        rw [map_smul, ← Module.End.mul_apply, ← pow_succ', Fin.val_last, hnil _ x.property,
          smul_zero]
      have h0 : Special.raising ℂ (n + 1) w 0 = 0 := by simp [Special.raising_apply]
      rw [hlast, add_zero, h0, zero_smul, zero_add]
      refine Finset.sum_congr rfl fun i _ => ?_
      have hr : Special.raising ℂ (n + 1) w i.succ = w i.castSucc := by
        rw [Special.raising_apply]
        split_ifs with h
        · rfl
        · exact absurd (Nat.succ_pos _) h
      rw [hr, map_smul, ← Module.End.mul_apply, ← pow_succ']
      congr 2

/-- Complements of subrepresentations are complements of their subspaces. -/
theorem isCompl_toSubmodule {σ τ : Subrepresentation A.representation} (h : IsCompl σ τ) :
    IsCompl σ.toSubmodule τ.toSubmodule :=
  ⟨disjoint_iff.mpr (congrArg Subrepresentation.toSubmodule h.inf_eq_bot),
    codisjoint_iff.mpr (congrArg Subrepresentation.toSubmodule h.sup_eq_top)⟩

/-- If every power of `N` sends `Σ_j N^j (f j)` into a subspace meeting `N^n σ`
trivially, then `f = 0`. -/
theorem eq_zero_of_forall_monodromy_pow_mem {σ : Subrepresentation A.representation} {n : ℕ}
    (hnil : ∀ v ∈ σ.toSubmodule, (A.monodromy ^ (n + 1)) v = 0)
    (hinj : ∀ v ∈ σ.toSubmodule, (A.monodromy ^ n) v = 0 → v = 0)
    {T : Submodule ℂ A} (hT : Disjoint T (imagePow A σ n).toSubmodule)
    (f : Fin (n + 1) → σ.toSubmodule)
    (hf : ∀ e : ℕ, (A.monodromy ^ e) (sumMap σ (n + 1) f) ∈ T) : f = 0 := by
  classical
  by_contra hne
  have hS : (Finset.univ.filter fun j => f j ≠ 0).Nonempty := by
    obtain ⟨j, hj⟩ := Function.ne_iff.mp hne
    exact ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩⟩
  set j0 := (Finset.univ.filter fun j => f j ≠ 0).min' hS
  have hfj0 : f j0 ≠ 0 := (Finset.mem_filter.mp (Finset.min'_mem _ hS)).2
  have hlt : ∀ j, j < j0 → f j = 0 := fun j hj => by
    by_contra h
    exact absurd (Finset.min'_le _ j (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩))
      (not_le.mpr hj)
  have hsum : (A.monodromy ^ (n - j0)) (sumMap σ (n + 1) f) =
      (A.monodromy ^ n) (f j0 : A) := by
    rw [sumMap_apply, map_sum, Finset.sum_eq_single j0]
    · rw [← Module.End.mul_apply, ← pow_add, Nat.sub_add_cancel (Nat.lt_succ_iff.mp j0.isLt)]
    · intro j _ hj
      rcases lt_or_gt_of_ne hj with h | h
      · simp [hlt j h]
      · have h' : (j0 : ℕ) < j := h
        have hj' := j.isLt
        rw [← Module.End.mul_apply, ← pow_add,
          show n - j0 + j = (n - j0 + j - (n + 1)) + (n + 1) by omega, pow_add,
          Module.End.mul_apply, hnil _ (f j).property, map_zero]
    · intro h
      exact absurd (Finset.mem_univ _) h
  have hmemT := hf (n - j0)
  rw [hsum] at hmemT
  have hmemI : (A.monodromy ^ n) (f j0 : A) ∈ (imagePow A σ n).toSubmodule :=
    ⟨f j0, rfl⟩
  exact hfj0 (Subtype.ext (hinj _ (f j0).property
    (Submodule.disjoint_def.mp hT _ hmemT hmemI)))

theorem sumMap_injective {σ : Subrepresentation A.representation} {n : ℕ}
    (hnil : ∀ v ∈ σ.toSubmodule, (A.monodromy ^ (n + 1)) v = 0)
    (hinj : ∀ v ∈ σ.toSubmodule, (A.monodromy ^ n) v = 0 → v = 0)
    {T : Submodule ℂ A} (hT : Disjoint T (imagePow A σ n).toSubmodule) :
    Function.Injective (sumMap σ (n + 1)) :=
  (injective_iff_map_eq_zero _).mpr fun f hf =>
    eq_zero_of_forall_monodromy_pow_mem hnil hinj hT f fun e => by
      rw [hf, map_zero]
      exact T.zero_mem

variable (A) in
/-- An embedded block `σ ⊗ S_m` with irreducible Weil factor `σ`. -/
structure Piece where
  /-- The Weil factor, as a subrepresentation of the carrier. -/
  carrier : Subrepresentation A.representation
  /-- The length of the block. -/
  length : ℕ
  length_pos : 0 < length
  isIrreducible : carrier.toRepresentation.IsIrreducible
  /-- The embedding of the block into the pair. -/
  map : Hom (block ν (FiniteRepresentation.of carrier.toRepresentation) length) A
  injective : Function.Injective map.intertwiner.toLinearMap

/-- The image of an embedded block. -/
def Piece.range (p : Piece A) : Submodule ℂ A :=
  LinearMap.range p.map.intertwiner.toLinearMap

/-- One step: a nonzero stable subspace `U` splits as an embedded block plus a
stable subspace `D`, with additive dimensions. -/
theorem exists_piece (hss : A.toFiniteRepresentation.IsSemisimple)
    (U : Subrepresentation A.representation)
    (hUN : ∀ v ∈ U.toSubmodule, A.monodromy v ∈ U.toSubmodule) (hU : U ≠ ⊥) :
    ∃ (p : Piece A) (D : Subrepresentation A.representation),
      (∀ v ∈ D.toSubmodule, A.monodromy v ∈ D.toSubmodule) ∧
      p.range ⊔ D.toSubmodule = U.toSubmodule ∧
      Module.finrank ℂ p.range + Module.finrank ℂ D.toSubmodule =
        Module.finrank ℂ U.toSubmodule ∧
      0 < Module.finrank ℂ p.range := by
  classical
  have : ComplementedLattice (Subrepresentation A.representation) := hss
  have := wellFoundedLT_subrepresentation A
  -- The nilpotency order of `N` on `U` is `n + 1`.
  have hex : ∃ k, ∀ v ∈ U.toSubmodule, (A.monodromy ^ k) v = 0 := by
    obtain ⟨k, hk⟩ := A.nilpotent
    exact ⟨k, fun v _ => by rw [hk, LinearMap.zero_apply]⟩
  have hm0 : ∀ v ∈ U.toSubmodule, (A.monodromy ^ Nat.find hex) v = 0 := Nat.find_spec hex
  obtain ⟨n, hn⟩ : ∃ n, Nat.find hex = n + 1 := by
    refine Nat.exists_eq_succ_of_ne_zero fun h0 => hU ?_
    rw [h0] at hm0
    apply Subrepresentation.toSubmodule_injective
    exact (Submodule.eq_bot_iff _).mpr fun v hv => by simpa using hm0 v hv
  have hnilU : ∀ v ∈ U.toSubmodule, (A.monodromy ^ (n + 1)) v = 0 := hn ▸ hm0
  obtain ⟨v, hvU, hvn⟩ : ∃ v ∈ U.toSubmodule, (A.monodromy ^ n) v ≠ 0 := by
    have := Nat.find_min hex (show n < Nat.find hex by omega)
    push Not at this
    exact this
  -- An atom `σ` of a Weil complement of `U ⊓ ker N^n` inside `U`.
  obtain ⟨C, hC⟩ := exists_isCompl (U ⊓ kerPow A n)
  have hCs := isCompl_toSubmodule hC
  have hv' : v ∈ (U ⊓ kerPow A n).toSubmodule ⊔ C.toSubmodule := by
    rw [hCs.sup_eq_top]
    exact Submodule.mem_top
  obtain ⟨a, ha, c, hc, hac⟩ := Submodule.mem_sup.mp hv'
  have haU : a ∈ U.toSubmodule := (Submodule.mem_inf.mp ha).1
  have haK : a ∈ LinearMap.ker (A.monodromy ^ n) := (Submodule.mem_inf.mp ha).2
  have hcU : c ∈ U.toSubmodule := by
    rw [← add_sub_cancel_left a c, hac]
    exact U.toSubmodule.sub_mem hvU haU
  have hcn : (A.monodromy ^ n) c ≠ 0 := by
    intro h
    apply hvn
    rw [← hac, map_add, LinearMap.mem_ker.mp haK, h, add_zero]
  have hCU : C ⊓ U ≠ ⊥ := by
    intro h
    have hmem : c ∈ (C ⊓ U).toSubmodule := Submodule.mem_inf.mpr ⟨hc, hcU⟩
    rw [h] at hmem
    have hc0 : c = 0 := (Submodule.mem_bot ℂ).mp hmem
    exact hcn (by rw [hc0, map_zero])
  obtain ⟨σ, hσ, hσle⟩ := (eq_bot_or_exists_atom_le (C ⊓ U)).resolve_left hCU
  have hσC : ∀ x ∈ σ.toSubmodule, x ∈ C.toSubmodule := fun x hx =>
    (Submodule.mem_inf.mp (hσle hx)).1
  have hσU : ∀ x ∈ σ.toSubmodule, x ∈ U.toSubmodule := fun x hx =>
    (Submodule.mem_inf.mp (hσle hx)).2
  have hnil : ∀ x ∈ σ.toSubmodule, (A.monodromy ^ (n + 1)) x = 0 := fun x hx =>
    hnilU x (hσU x hx)
  have hinj : ∀ x ∈ σ.toSubmodule, (A.monodromy ^ n) x = 0 → x = 0 := fun x hx h0 =>
    Submodule.disjoint_def.mp hCs.disjoint x
      (Submodule.mem_inf.mpr ⟨hσU x hx, LinearMap.mem_ker.mpr h0⟩) (hσC x hx)
  -- A Weil complement `T` of `N^n σ`, and the embedded block.
  obtain ⟨T, hT⟩ := exists_isCompl (imagePow A σ n)
  have hTs := isCompl_toSubmodule hT
  have hinjS : Function.Injective (sumMap σ (n + 1)) :=
    sumMap_injective hnil hinj hTs.disjoint.symm
  let p : Piece A :=
    { carrier := σ
      length := n + 1
      length_pos := Nat.succ_pos n
      isIrreducible :=
        Langlands.FiniteIndexRestriction.isIrreducible_toRepresentation_of_isAtom σ hσ
      map := pieceHom σ (n + 1) hnil
      injective := blockLinear_injective σ (n + 1) hinjS }
  have hprange : p.range = LinearMap.range (sumMap σ (n + 1)) := range_blockLinear σ (n + 1)
  -- The stable complement `D`.
  let D : Subrepresentation A.representation :=
    { toSubmodule := U.toSubmodule ⊓ ⨅ e : ℕ, T.toSubmodule.comap (A.monodromy ^ e)
      apply_mem_toSubmodule := fun g x hx => by
        obtain ⟨hxU, hxT⟩ := Submodule.mem_inf.mp hx
        refine Submodule.mem_inf.mpr
          ⟨U.apply_mem_toSubmodule g hxU, (Submodule.mem_iInf _).mpr fun e => ?_⟩
        have hTe : (A.monodromy ^ e) x ∈ T.toSubmodule := (Submodule.mem_iInf _).mp hxT e
        have h2 : (A.monodromy ^ e) (A.representation g x) =
            ((ν g : ℂ) ^ e)⁻¹ • A.representation g ((A.monodromy ^ e) x) := by
          rw [representation_monodromy_pow, smul_smul,
            inv_mul_cancel₀ (pow_ne_zero _ (Units.ne_zero _)), one_smul]
        rw [Submodule.mem_comap, h2]
        exact T.toSubmodule.smul_mem _ (T.apply_mem_toSubmodule g hTe) }
  have hDdef : D.toSubmodule =
      U.toSubmodule ⊓ ⨅ e : ℕ, T.toSubmodule.comap (A.monodromy ^ e) := rfl
  clear_value D
  have hDN : ∀ x ∈ D.toSubmodule, A.monodromy x ∈ D.toSubmodule := fun x hx => by
    rw [hDdef] at hx ⊢
    obtain ⟨hxU, hxT⟩ := Submodule.mem_inf.mp hx
    refine Submodule.mem_inf.mpr ⟨hUN x hxU, (Submodule.mem_iInf _).mpr fun e => ?_⟩
    rw [Submodule.mem_comap, ← Module.End.mul_apply, ← pow_succ]
    exact (Submodule.mem_iInf _).mp hxT (e + 1)
  have hdisj : Disjoint D.toSubmodule (LinearMap.range (sumMap σ (n + 1))) := by
    rw [Submodule.disjoint_def]
    rintro x hx ⟨f, rfl⟩
    rw [hDdef] at hx
    rw [eq_zero_of_forall_monodromy_pow_mem hnil hinj hTs.disjoint.symm f
      fun e => (Submodule.mem_iInf _).mp (Submodule.mem_inf.mp hx).2 e, map_zero]
  have hBU : LinearMap.range (sumMap σ (n + 1)) ≤ U.toSubmodule := by
    rintro x ⟨f, rfl⟩
    rw [sumMap_apply]
    exact Submodule.sum_mem _ fun j _ => monodromy_pow_mem A hUN j (hσU _ (f j).property)
  -- Dimension count.
  have hfinB : Module.finrank ℂ (LinearMap.range (sumMap σ (n + 1))) =
      (n + 1) * Module.finrank ℂ σ.toSubmodule := by
    rw [LinearMap.finrank_range_of_inj hinjS, Module.finrank_pi_fintype, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  have hfinQ : Module.finrank ℂ (A ⧸ T.toSubmodule) = Module.finrank ℂ σ.toSubmodule := by
    have h1 := Submodule.finrank_quotient_add_finrank T.toSubmodule
    have h2 := Submodule.finrank_add_eq_of_isCompl hTs
    have hi : Function.Injective ((A.monodromy ^ n) ∘ₗ σ.toSubmodule.subtype) := by
      rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
      intro x hx
      exact Subtype.ext (hinj _ x.property hx)
    have h3 : Module.finrank ℂ (imagePow A σ n).toSubmodule =
        Module.finrank ℂ σ.toSubmodule :=
      LinearMap.finrank_range_of_inj hi
    omega
  let Ψ : A →ₗ[ℂ] (Fin (n + 1) → A ⧸ T.toSubmodule) :=
    LinearMap.pi fun j => T.toSubmodule.mkQ ∘ₗ A.monodromy ^ (j : ℕ)
  let Ψ' := Ψ ∘ₗ U.toSubmodule.subtype
  have hker : (LinearMap.ker Ψ').map U.toSubmodule.subtype ≤ D.toSubmodule := by
    rintro x ⟨y, hy, rfl⟩
    rw [Submodule.subtype_apply, hDdef]
    refine Submodule.mem_inf.mpr ⟨y.property, (Submodule.mem_iInf _).mpr fun e => ?_⟩
    rw [Submodule.mem_comap]
    by_cases he : e < n + 1
    · have h := congr_fun (LinearMap.mem_ker.mp hy) ⟨e, he⟩
      simpa [Ψ', Ψ, Submodule.Quotient.mk_eq_zero] using h
    · rw [show e = (e - (n + 1)) + (n + 1) by omega, pow_add, Module.End.mul_apply,
        hnilU _ y.property, map_zero]
      exact T.toSubmodule.zero_mem
  have hrk := LinearMap.finrank_range_add_finrank_ker Ψ'
  have hrange : Module.finrank ℂ (LinearMap.range Ψ') ≤
      (n + 1) * Module.finrank ℂ σ.toSubmodule := by
    refine (Submodule.finrank_le _).trans (le_of_eq ?_)
    rw [Module.finrank_pi_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      smul_eq_mul, hfinQ]
  have hkerD : Module.finrank ℂ (LinearMap.ker Ψ') ≤ Module.finrank ℂ D.toSubmodule := by
    rw [LinearEquiv.finrank_eq (Submodule.equivMapOfInjective _
      (Submodule.injective_subtype _) (LinearMap.ker Ψ'))]
    exact Submodule.finrank_mono hker
  have hsupU : LinearMap.range (sumMap σ (n + 1)) ⊔ D.toSubmodule = U.toSubmodule := by
    apply Submodule.eq_of_le_of_finrank_le (sup_le hBU (by rw [hDdef]; exact inf_le_left))
    have h := Submodule.finrank_sup_add_finrank_inf_eq
      (LinearMap.range (sumMap σ (n + 1))) D.toSubmodule
    rw [hdisj.symm.eq_bot, finrank_bot, add_zero] at h
    omega
  have hdimU : Module.finrank ℂ (LinearMap.range (sumMap σ (n + 1))) +
      Module.finrank ℂ D.toSubmodule = Module.finrank ℂ U.toSubmodule := by
    have h := Submodule.finrank_sup_add_finrank_inf_eq
      (LinearMap.range (sumMap σ (n + 1))) D.toSubmodule
    rw [hdisj.symm.eq_bot, finrank_bot, add_zero, hsupU] at h
    exact h.symm
  have hσpos : 0 < Module.finrank ℂ σ.toSubmodule :=
    Nat.pos_of_ne_zero fun h =>
      hσ.1 (Subrepresentation.toSubmodule_injective (Submodule.finrank_eq_zero.mp h))
  refine ⟨p, D, hDN, ?_, ?_, ?_⟩
  · rw [hprange, hsupU]
  · rw [hprange, hdimU]
  · rw [hprange, hfinB]
    exact Nat.mul_pos (Nat.succ_pos n) hσpos

/-- Strong induction on the dimension: every stable subspace is spanned by finitely
many embedded blocks whose dimensions add up to its dimension. -/
theorem exists_pieces (hss : A.toFiniteRepresentation.IsSemisimple) (d : ℕ) :
    ∀ U : Subrepresentation A.representation, Module.finrank ℂ U.toSubmodule = d →
      (∀ v ∈ U.toSubmodule, A.monodromy v ∈ U.toSubmodule) →
      ∃ (k : ℕ) (p : Fin k → Piece A), ⨆ i, (p i).range = U.toSubmodule ∧
        ∑ i, Module.finrank ℂ (p i).range = Module.finrank ℂ U.toSubmodule := by
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    intro U hd hUN
    by_cases hU : U = ⊥
    · subst hU
      refine ⟨0, Fin.elim0, iSup_of_empty _, ?_⟩
      rw [Fin.sum_univ_zero]
      exact (finrank_bot ℂ A).symm
    · obtain ⟨p, D, hDN, hsup, hdim, hpos⟩ := exists_piece hss U hUN hU
      obtain ⟨k, q, hq, hqdim⟩ := ih _ (by omega) D rfl hDN
      have e0 : Fin.cons (α := fun _ => Piece A) p q 0 = p := rfl
      have es : ∀ j : Fin k, Fin.cons (α := fun _ => Piece A) p q j.succ = q j :=
        fun j => rfl
      refine ⟨k + 1, Fin.cons (α := fun _ => Piece A) p q, ?_, ?_⟩
      · rw [← hsup, ← hq]
        apply le_antisymm
        · refine iSup_le fun i => ?_
          refine Fin.cases ?_ (fun j => ?_) i
          · exact le_sup_left
          · exact le_sup_of_le_right (le_iSup (fun j => (q j).range) j)
        · exact sup_le (le_iSup_of_le 0 le_rfl) (iSup_le fun j => le_iSup_of_le j.succ le_rfl)
      · have hs : ∑ j : Fin k,
            Module.finrank ℂ (Fin.cons (α := fun _ => Piece A) p q j.succ).range =
            ∑ j, Module.finrank ℂ (q j).range := Finset.sum_congr rfl fun j _ => by rw [es]
        rw [Fin.sum_univ_succ, e0, hs]
        omega

variable (A) in
/-- Morphisms from finitely many pairs into `A` whose images span `A`, and whose
source dimensions add up to the dimension of `A`, assemble to an isomorphism of
`A` with the direct sum of the sources. -/
theorem nonempty_equiv_directSum_of_span {k : ℕ}
    (B : Fin k → WeilDeligneRepresentation.{0, uG, uV} ℂ G ν) (φ : ∀ i, Hom (B i) A)
    (hspan : ⨆ i, LinearMap.range (φ i).intertwiner.toLinearMap = ⊤)
    (hdim : ∑ i, Module.finrank ℂ (B i) = Module.finrank ℂ A) :
    Nonempty (WeilDeligneRepresentation.Equiv A (WeilDeligneRepresentation.directSum B)) := by
  classical
  let Φ : WeilDeligneRepresentation.directSum B →ₗ[ℂ] A :=
    DirectSum.toModule ℂ (Fin k) A fun i => (φ i).intertwiner.toLinearMap
  have hΦ : ∀ i (x : B i),
      Φ (DirectSum.lof ℂ (Fin k) (fun i => B i) i x) = (φ i).intertwiner x :=
    fun i x => by
      change DirectSum.toModule ℂ (Fin k) A (fun i => (φ i).intertwiner.toLinearMap)
        (DirectSum.lof ℂ (Fin k) (fun i => B i) i x) = (φ i).intertwiner.toLinearMap x
      exact DirectSum.toModule_lof ℂ (M := fun i => B i) i x
  have hint : ∀ g : G, Φ ∘ₗ (WeilDeligneRepresentation.directSum B).representation g =
      A.representation g ∘ₗ Φ := by
    intro g
    refine DirectSum.linearMap_ext ℂ fun i => LinearMap.ext fun x => ?_
    change Φ (DirectSum.lmap (fun i => (B i).representation g)
        (DirectSum.lof ℂ (Fin k) (fun i => B i) i x)) =
      A.representation g (Φ (DirectSum.lof ℂ (Fin k) (fun i => B i) i x))
    rw [DirectSum.lmap_lof, hΦ, hΦ]
    exact LinearMap.congr_fun ((φ i).intertwiner.isIntertwining' g) x
  have hmon : Φ ∘ₗ (WeilDeligneRepresentation.directSum B).monodromy = A.monodromy ∘ₗ Φ := by
    refine DirectSum.linearMap_ext ℂ fun i => LinearMap.ext fun x => ?_
    change Φ (DirectSum.lmap (fun i => (B i).monodromy)
        (DirectSum.lof ℂ (Fin k) (fun i => B i) i x)) =
      A.monodromy (Φ (DirectSum.lof ℂ (Fin k) (fun i => B i) i x))
    rw [DirectSum.lmap_lof, hΦ, hΦ]
    exact LinearMap.congr_fun (φ i).comm_monodromy x
  have hsurj : Function.Surjective Φ := by
    refine LinearMap.range_eq_top.mp (top_unique ?_)
    rw [← hspan]
    refine iSup_le fun i => ?_
    rintro _ ⟨x, rfl⟩
    exact ⟨DirectSum.lof ℂ (Fin k) (fun i => B i) i x, hΦ i x⟩
  have hfin : Module.finrank ℂ (WeilDeligneRepresentation.directSum B) =
      Module.finrank ℂ A := by
    rw [← hdim]
    exact Module.finrank_directSum ℂ fun i => (B i : Type uV)
  have hbij : Function.Bijective Φ :=
    ⟨(LinearMap.injective_iff_surjective_of_finrank_eq_finrank hfin).mpr hsurj, hsurj⟩
  let f : (WeilDeligneRepresentation.directSum B).representation.IntertwiningMap
      A.representation := ⟨Φ, hint⟩
  let e : WeilDeligneRepresentation.Equiv (WeilDeligneRepresentation.directSum B) A :=
    ⟨Representation.IntertwiningMap.ofBijective f hbij, hmon⟩
  exact ⟨e.symm⟩

end DecompositionExistenceProof

open DecompositionExistenceProof in
/-- Every Weil–Deligne pair with semisimple Weil part is isomorphic to a finite
direct sum of blocks `σ ⊗ S_m` with irreducible Weil factor `σ`. -/
theorem decompositionExistence : DecompositionExistence.{uG, uV} := by
  intro G _ ν A hss
  obtain ⟨k, p, hsup, hdim⟩ := exists_pieces hss _ ⊤ rfl fun v _ => Submodule.mem_top
  refine ⟨k, fun i => ⟨FiniteRepresentation.of (p i).carrier.toRepresentation, (p i).length,
    (p i).length_pos⟩, fun i => (p i).isIrreducible, ?_⟩
  refine nonempty_equiv_directSum_of_span A _ (fun i => (p i).map) hsup ?_
  rw [← finrank_top ℂ A]
  refine Eq.trans (Finset.sum_congr rfl fun i _ => ?_) hdim
  exact (LinearMap.finrank_range_of_inj (p i).injective).symm

end Langlands.WeilDeligneRepresentation.Blocks
