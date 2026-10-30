import Langlands.Representation.Filtration.ObjectDefinitions
import Langlands.Representation.SubrepresentationLattice
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.LinearAlgebra.Eigenspace.Minpoly

/-!
# Splitting a filtration by the scalars of a central element

A finite filtration whose graded pieces are acted on by a central element `z`
through pairwise distinct scalars splits into the `z`-eigenspaces. Each
eigenspace is equivalent to the corresponding graded piece, and every invariant
subspace is the sum of its intersections with the eigenspaces.
-/

noncomputable section

open Polynomial

namespace Langlands.CentralEigenspaceSplitting

universe uK uG uV uW

section Linear

variable {k : Type uK} [Field k] {V : Type uV} [AddCommGroup V] [Module k V]
  {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A polynomial in an endomorphism preserves every submodule the endomorphism
preserves. -/
theorem aeval_apply_mem (f : Module.End k V) (W : Submodule k V)
    (hW : ∀ v ∈ W, f v ∈ W) (p : k[X]) {v : V} (hv : v ∈ W) :
    aeval f p v ∈ W := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simpa only [map_add, LinearMap.add_apply] using W.add_mem hp hq
  | monomial m a =>
    have hpow : ∀ j : ℕ, (f ^ j) v ∈ W := by
      intro j
      induction j with
      | zero => simpa using hv
      | succ j ih =>
        rw [pow_succ', Module.End.mul_apply]
        exact hW _ ih
    rw [aeval_monomial, Module.End.mul_apply, Module.algebraMap_end_apply]
    exact W.smul_mem a (hpow m)

/-- The Lagrange basis polynomial at a node, evaluated at an endomorphism
annihilated by the nodal polynomial, takes values in that node's eigenspace. -/
theorem aeval_basis_mem_eigenspace (f : Module.End k V) (c : ι → k)
    (hf : aeval f (Lagrange.nodal Finset.univ c) = 0) (i : ι) (v : V) :
    aeval f (Lagrange.basis Finset.univ c i) v ∈ f.eigenspace (c i) := by
  have hmul : (X - C (c i)) * Lagrange.basis Finset.univ c i =
      C (Lagrange.nodalWeight Finset.univ c i) * Lagrange.nodal Finset.univ c := by
    rw [Lagrange.basis_eq_prod_sub_inv_mul_nodal_div (Finset.mem_univ i),
      ← Lagrange.nodal_erase_eq_nodal_div (Finset.mem_univ i),
      Lagrange.nodal_eq_mul_nodal_erase (Finset.mem_univ i)]
    ring
  have h := congrArg (fun p => aeval f p v) hmul
  simp only [map_mul, hf, mul_zero, LinearMap.zero_apply, Module.End.mul_apply, map_sub,
    aeval_X, aeval_C, LinearMap.sub_apply, Module.algebraMap_end_apply] at h
  rw [Module.End.mem_eigenspace_iff]
  exact sub_eq_zero.mp h

/-- The Lagrange projections at distinct nodes sum to the identity. -/
theorem sum_aeval_basis (f : Module.End k V) (c : ι → k) (hc : Function.Injective c)
    (hf : aeval f (Lagrange.nodal Finset.univ c) = 0) (v : V) :
    ∑ i, aeval f (Lagrange.basis Finset.univ c i) v = v := by
  rcases isEmpty_or_nonempty ι with hι | hι
  · have h1 : Lagrange.nodal (Finset.univ : Finset ι) c = 1 := by
      rw [Finset.univ_eq_empty, Lagrange.nodal_empty]
    rw [h1, map_one] at hf
    have hv : v = 0 := by
      simpa using congrArg (fun g : Module.End k V => g v) hf
    simp [hv]
  · have hsum := Lagrange.sum_basis (s := Finset.univ) hc.injOn Finset.univ_nonempty
    have h := congrArg (fun p => aeval f p v) hsum
    simpa only [map_sum, LinearMap.sum_apply, map_one, Module.End.one_apply] using h

end Linear

section Representation

variable {k : Type uK} [Field k] {G : Type uG} [Monoid G]
  {V : Type uV} [AddCommGroup V] [Module k V]

theorem mem_bot_iff {ρ : Representation k G V} {v : V} :
    v ∈ (⊥ : Subrepresentation ρ) ↔ v = 0 :=
  Submodule.mem_bot k

theorem mem_top {ρ : Representation k G V} (v : V) : v ∈ (⊤ : Subrepresentation ρ) :=
  Submodule.mem_top

/-- Irreducibility is invariant under equivalence of representations. -/
theorem isIrreducible_iff_of_equiv {W : Type uW} [AddCommGroup W] [Module k W]
    {ρ : Representation k G V} {σ : Representation k G W} (e : ρ.Equiv σ) :
    ρ.IsIrreducible ↔ σ.IsIrreducible := by
  rw [Representation.irreducible_iff_isSimpleModule_asModule,
    Representation.irreducible_iff_isSimpleModule_asModule]
  exact LinearMap.isSimpleModule_iff_of_bijective
    (Representation.IntertwiningMap.equivLinearMapAsModule ρ σ e.toIntertwiningMap) e.bijective

/-- An irreducible representation has a nonzero vector. -/
theorem exists_ne_zero_of_isIrreducible {ρ : Representation k G V} (hρ : ρ.IsIrreducible) :
    ∃ v : V, v ≠ 0 := by
  by_contra h
  push Not at h
  apply hρ.bot_ne_top
  apply le_antisymm bot_le
  intro v _
  exact mem_bot_iff.mpr (h v)

/-- A group element acting by a scalar on one representation acts by the same
scalar on every equivalent representation. -/
theorem apply_eq_smul_of_equiv {W : Type uW} [AddCommGroup W] [Module k W]
    {ρ : Representation k G V} {σ : Representation k G W} (φ : ρ.Equiv σ) (z : G) (c : k)
    (h : ∀ w, σ z w = c • w) (v : V) : ρ z v = c • v := by
  apply φ.toLinearEquiv.injective
  have h1 := LinearMap.congr_fun (φ.toIntertwiningMap.isIntertwining' z) v
  change φ.toIntertwiningMap.toLinearMap (ρ z v) = φ.toIntertwiningMap.toLinearMap (c • v)
  rw [map_smul]
  exact h1.trans (h _)

/-- An intertwining map commutes with polynomials in the action of a group element. -/
theorem intertwining_aeval {W : Type uW} [AddCommGroup W] [Module k W]
    {ρ : Representation k G V} {σ : Representation k G W} (f : ρ.IntertwiningMap σ) (z : G)
    (p : k[X]) (v : V) : f (aeval (ρ z) p v) = aeval (σ z) p (f v) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp only [map_add, LinearMap.add_apply, hp, hq]
  | monomial m a =>
    have hpow : ∀ j : ℕ, f ((ρ z ^ j) v) = (σ z ^ j) (f v) := by
      intro j
      induction j with
      | zero => rfl
      | succ j ih =>
        rw [pow_succ', Module.End.mul_apply, f.isIntertwining, ih, pow_succ',
          Module.End.mul_apply]
    simp only [aeval_monomial, Module.End.mul_apply, Module.algebraMap_end_apply, map_smul,
      hpow]

/-- The inclusion of a subrepresentation, as an intertwining map. -/
def subrepInclusion {ρ : Representation k G V} (S : Subrepresentation ρ) :
    S.toRepresentation.IntertwiningMap ρ where
  toLinearMap := S.toSubmodule.subtype
  isIntertwining' _ := rfl

@[simp]
theorem subrepInclusion_apply {ρ : Representation k G V} (S : Subrepresentation ρ)
    (v : S.toSubmodule) : subrepInclusion S v = v := rfl

/-- The `a`-eigenspace of the action of a central element `z`, as a
subrepresentation. -/
def eigenSubrep (ρ : Representation k G V) (z : G) (hz : ∀ g, z * g = g * z) (a : k) :
    Subrepresentation ρ where
  toSubmodule := Module.End.eigenspace (ρ z) a
  apply_mem_toSubmodule g v hv := by
    rw [Module.End.mem_eigenspace_iff] at hv ⊢
    calc ρ z (ρ g v) = ρ (z * g) v := by rw [map_mul, Module.End.mul_apply]
      _ = ρ (g * z) v := by rw [hz]
      _ = a • ρ g v := by rw [map_mul, Module.End.mul_apply, hv, map_smul]

theorem mem_eigenSubrep {ρ : Representation k G V} {z : G} {hz : ∀ g, z * g = g * z} {a : k}
    {v : V} : v ∈ eigenSubrep ρ z hz a ↔ ρ z v = a • v :=
  Module.End.mem_eigenspace_iff

/-- If the action of a central element is annihilated by the nodal polynomial of
distinct scalars, every subrepresentation is the sum of its intersections with
the eigenspaces. -/
theorem eq_iSup_inf_eigenSubrep {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ρ : Representation k G V) (z : G) (hz : ∀ g, z * g = g * z)
    (c : ι → k) (hc : Function.Injective c)
    (hf : aeval (ρ z) (Lagrange.nodal Finset.univ c) = 0) (S : Subrepresentation ρ) :
    S = ⨆ i, S ⊓ eigenSubrep ρ z hz (c i) := by
  refine le_antisymm (fun v hv => ?_) (iSup_le fun i => inf_le_left)
  change v ∈ (⨆ i, S ⊓ eigenSubrep ρ z hz (c i)).toSubmodule
  rw [Langlands.Subrepresentation.toSubmodule_iSup, ← sum_aeval_basis (ρ z) c hc hf v]
  refine Submodule.sum_mem_iSup fun i => Submodule.mem_inf.mpr ⟨?_, ?_⟩
  · exact aeval_apply_mem (ρ z) S.toSubmodule (fun w hw => S.apply_mem_toSubmodule z hw) _ hv
  · exact aeval_basis_mem_eigenspace (ρ z) c hf i v

/-- If a polynomial in `z` kills a representation mapping into `ρ`, the image meets
every eigenspace at which the polynomial does not vanish trivially. -/
theorem range_inf_eigenSubrep_eq_bot {W : Type uW} [AddCommGroup W] [Module k W]
    {ρ : Representation k G V} {τ : Representation k G W} (ι : τ.IntertwiningMap ρ) (z : G)
    (hz : ∀ g, z * g = g * z) (p : k[X]) (hp : aeval (τ z) p = 0) (a : k)
    (ha : p.eval a ≠ 0) : ι.range ⊓ eigenSubrep ρ z hz a = ⊥ := by
  rw [eq_bot_iff]
  intro v hv
  obtain ⟨hvr, hvE⟩ := Submodule.mem_inf.mp hv
  obtain ⟨u, rfl⟩ := (Representation.IntertwiningMap.mem_range _ _ ι _).mp hvr
  have h := intertwining_aeval ι z p u
  rw [hp, LinearMap.zero_apply, map_zero,
    Module.End.aeval_apply_of_mem_apply_eq_smul (mem_eigenSubrep.mp hvE)] at h
  exact mem_bot_iff.mpr ((smul_eq_zero.mp h.symm).resolve_left ha)

end Representation

section Filtration

variable {k : Type uK} [Field k] {G : Type uG} [Monoid G] {A : Rep.{uV} k G} {n : ℕ}

/-- A vector of the upper step projects to zero in the graded piece exactly when
it lies in the lower step. -/
theorem gradedProjection_eq_zero_iff (s : ObjectRepFiltration A n) (i : Fin n)
    (w : (s.subrepresentation i.succ).toSubmodule) :
    (s.gradedProjection i).hom w = 0 ↔ (w : A) ∈ s.subrepresentation i.castSucc :=
  Submodule.Quotient.mk_eq_zero _

/-- If `z` acts on the `i`th graded piece by `d i`, then `z - d i` maps the upper
step into the lower step. -/
theorem sub_smul_mem_of_graded (s : ObjectRepFiltration A n) (z : G) (d : Fin n → k)
    (hgr : ∀ i v, (s.gradedRepresentation i).ρ z v = d i • v) (i : Fin n) {v : A}
    (hv : v ∈ s.subrepresentation i.succ) :
    A.ρ z v - d i • v ∈ s.subrepresentation i.castSucc := by
  let w : (s.subrepresentation i.succ).toSubmodule := ⟨v, hv⟩
  have h := Rep.hom_comm_apply (s.gradedProjection i) z w
  rw [hgr] at h
  have h0 : (s.gradedProjection i).hom
      ((s.subrepresentation i.succ).toRepresentation z w - d i • w) = 0 := by
    rw [map_sub, map_smul]
    exact sub_eq_zero.mpr h
  exact (gradedProjection_eq_zero_iff s i _).mp h0

/-- The product of the linear factors `X - d i` over the graded indices `i` with
`a ≤ i < b`. -/
def intervalPoly (d : Fin n → k) (a b : ℕ) : k[X] :=
  ∏ i ∈ Finset.univ.filter (fun i : Fin n => a ≤ i.val ∧ i.val < b), (X - C (d i))

theorem intervalPoly_of_le (d : Fin n → k) {a b : ℕ} (h : b ≤ a) : intervalPoly d a b = 1 := by
  unfold intervalPoly
  refine Finset.prod_eq_one fun i hi => ?_
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
  omega

theorem intervalPoly_succ (d : Fin n → k) {a : ℕ} (i : Fin n) (h : a ≤ i.val) :
    intervalPoly d a (i.val + 1) = intervalPoly d a i.val * (X - C (d i)) := by
  unfold intervalPoly
  have hset : Finset.univ.filter (fun j : Fin n => a ≤ j.val ∧ j.val < i.val + 1) =
      insert i (Finset.univ.filter (fun j : Fin n => a ≤ j.val ∧ j.val < i.val)) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Fin.ext_iff]
    omega
  rw [hset, Finset.prod_insert (by simp), mul_comm]

theorem intervalPoly_zero_last (d : Fin n → k) : intervalPoly d 0 n = ∏ i, (X - C (d i)) := by
  unfold intervalPoly
  congr 1
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
  omega

/-- The interval product of the graded scalars maps the step `b` into the step `a`. -/
theorem aeval_intervalPoly_mem (s : ObjectRepFiltration A n) (z : G) (d : Fin n → k)
    (hgr : ∀ i v, (s.gradedRepresentation i).ρ z v = d i • v) (b : Fin (n + 1)) :
    ∀ a : Fin (n + 1), a ≤ b → ∀ v ∈ s.subrepresentation b,
      aeval (A.ρ z) (intervalPoly d a b) v ∈ s.subrepresentation a := by
  induction b using Fin.induction with
  | zero =>
    intro a ha v hv
    have ha0 : a = 0 := le_antisymm ha (Fin.zero_le _)
    subst ha0
    rw [intervalPoly_of_le d le_rfl, map_one, Module.End.one_apply]
    exact hv
  | succ i ih =>
    intro a ha v hv
    rcases ha.lt_or_eq with hlt | heq
    · have hle : a ≤ i.castSucc := Fin.le_castSucc_iff.mpr hlt
      have hai : (a : ℕ) ≤ i.val := hle
      rw [Fin.val_succ, intervalPoly_succ d i hai, map_mul, Module.End.mul_apply]
      have hstep : aeval (A.ρ z) (X - C (d i)) v = A.ρ z v - d i • v := by
        simp [Module.algebraMap_end_apply]
      rw [hstep]
      exact ih a hle _ (sub_smul_mem_of_graded s z d hgr i hv)
    · subst heq
      rw [intervalPoly_of_le d le_rfl, map_one, Module.End.one_apply]
      exact hv

/-- A filtration on whose graded pieces `z` acts by scalars is annihilated by the
product of the corresponding linear factors. -/
theorem aeval_prod_eq_zero (s : ObjectRepFiltration A n) (z : G) (d : Fin n → k)
    (hgr : ∀ i v, (s.gradedRepresentation i).ρ z v = d i • v) :
    aeval (A.ρ z) (∏ i, (X - C (d i))) = 0 := by
  ext v
  have h := aeval_intervalPoly_mem s z d hgr (Fin.last n) 0 (Fin.zero_le _) v
    (by rw [s.subrepresentation_last]; exact mem_top v)
  rw [s.subrepresentation_zero] at h
  simpa [intervalPoly_zero_last] using mem_bot_iff.mp h

section Distinct

variable (s : ObjectRepFiltration A n) (z : G) (hz : ∀ g, z * g = g * z) (c : Fin n → k)
  (hc : Function.Injective c) (hgr : ∀ i v, (s.gradedRepresentation i).ρ z v = c i • v)

include hgr in
theorem aeval_nodal_eq_zero : aeval (A.ρ z) (Lagrange.nodal Finset.univ c) = 0 :=
  aeval_prod_eq_zero s z c hgr

include hc in
theorem eval_intervalPoly_ne_zero (i : Fin n) {a b : ℕ} (h : ¬ (a ≤ i.val ∧ i.val < b)) :
    (intervalPoly c a b).eval (c i) ≠ 0 := by
  unfold intervalPoly
  rw [eval_prod, Finset.prod_ne_zero_iff]
  intro j hj
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
  rw [eval_sub, eval_X, eval_C, sub_ne_zero]
  intro hij
  have := hc hij
  subst this
  exact h hj

include hc hgr in
/-- The eigenspace of the `i`th scalar lies in every step beyond the `i`th. -/
theorem eigenSubrep_le (i : Fin n) (b : Fin (n + 1)) (hb : i.val < b.val) :
    eigenSubrep A.ρ z hz (c i) ≤ s.subrepresentation b := by
  intro v hv
  have hv' : A.ρ z v = c i • v := mem_eigenSubrep.mp hv
  have h := aeval_intervalPoly_mem s z c hgr (Fin.last n) b (Fin.le_last b) v
    (by rw [s.subrepresentation_last]; exact mem_top v)
  rw [Fin.val_last, Module.End.aeval_apply_of_mem_apply_eq_smul hv'] at h
  have hne := eval_intervalPoly_ne_zero c hc i (a := b) (b := n) (by omega)
  have := (s.subrepresentation b).toSubmodule.smul_mem
    ((eval (c i) (intervalPoly c b n))⁻¹) h
  rwa [smul_smul, inv_mul_cancel₀ hne, one_smul] at this

include hc hgr in
/-- The eigenspace of the `i`th scalar meets the steps up to the `i`th trivially. -/
theorem eigenSubrep_inf_eq_bot (i : Fin n) (b : Fin (n + 1)) (hb : b.val ≤ i.val) :
    eigenSubrep A.ρ z hz (c i) ⊓ s.subrepresentation b = ⊥ := by
  rw [eq_bot_iff]
  intro v hv
  obtain ⟨hv, hvb⟩ := Submodule.mem_inf.mp hv
  have hv' : A.ρ z v = c i • v := mem_eigenSubrep.mp hv
  have h := aeval_intervalPoly_mem s z c hgr b 0 (Fin.zero_le _) v hvb
  rw [s.subrepresentation_zero, Module.End.aeval_apply_of_mem_apply_eq_smul hv'] at h
  have hne := eval_intervalPoly_ne_zero c hc i (a := 0) (b := b) (by omega)
  exact mem_bot_iff.mpr ((smul_eq_zero.mp (mem_bot_iff.mp h)).resolve_left hne)

/-- The graded projection restricted to the eigenspace of the `i`th scalar. -/
def eigenToGraded (i : Fin n) :
    (eigenSubrep A.ρ z hz (c i)).toRepresentation.IntertwiningMap
      (s.gradedRepresentation i).ρ where
  toLinearMap := (s.gradedProjection i).hom.toLinearMap ∘ₗ
    Submodule.inclusion (eigenSubrep_le s z hz c hc hgr i i.succ (by simp))
  isIntertwining' g := by
    ext v
    exact Rep.hom_comm_apply (s.gradedProjection i) g
      (Submodule.inclusion (eigenSubrep_le s z hz c hc hgr i i.succ (by simp)) v)

theorem eigenToGraded_apply (i : Fin n) (v : (eigenSubrep A.ρ z hz (c i)).toSubmodule) :
    eigenToGraded s z hz c hc hgr i v = (s.gradedProjection i).hom
      (Submodule.inclusion (eigenSubrep_le s z hz c hc hgr i i.succ (by simp)) v) := rfl

theorem eigenToGraded_bijective (i : Fin n) :
    Function.Bijective (eigenToGraded s z hz c hc hgr i) := by
  constructor
  · rw [injective_iff_map_eq_zero]
    intro v hv
    rw [eigenToGraded_apply, gradedProjection_eq_zero_iff] at hv
    have hmem : (v : A) ∈ eigenSubrep A.ρ z hz (c i) ⊓ s.subrepresentation i.castSucc :=
      Submodule.mem_inf.mpr ⟨v.2, hv⟩
    rw [eigenSubrep_inf_eq_bot s z hz c hc hgr i i.castSucc le_rfl] at hmem
    exact Subtype.ext (mem_bot_iff.mp hmem)
  · intro u
    obtain ⟨w, rfl⟩ := s.gradedProjection_surjective i u
    have hf := aeval_nodal_eq_zero s z c hgr
    let P : Fin n → A → A := fun j => aeval (A.ρ z) (Lagrange.basis Finset.univ c j)
    have hPE : ∀ j (x : A), P j x ∈ eigenSubrep A.ρ z hz (c j) := fun j x =>
      aeval_basis_mem_eigenspace (A.ρ z) c hf j x
    refine ⟨⟨P i w, hPE i w⟩, ?_⟩
    rw [eigenToGraded_apply, ← sub_eq_zero, ← map_sub, gradedProjection_eq_zero_iff]
    have hsum := sum_aeval_basis (A.ρ z) c hc hf (w : A)
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)] at hsum
    have hdiff : ((Submodule.inclusion (eigenSubrep_le s z hz c hc hgr i i.succ (by simp))
        ⟨P i w, hPE i w⟩ - w : (s.subrepresentation i.succ).toSubmodule) : A) =
        -∑ j ∈ Finset.univ.erase i, P j w := by
      rw [Submodule.coe_sub, Submodule.coe_inclusion]
      change P i w - (w : A) = _
      rw [eq_neg_iff_add_eq_zero, sub_add_eq_add_sub, sub_eq_zero]
      exact hsum
    rw [hdiff]
    refine Submodule.neg_mem _ (Submodule.sum_mem _ fun j hj => ?_)
    have hji : j ≠ i := Finset.ne_of_mem_erase hj
    rcases lt_or_gt_of_ne hji with hlt | hgt
    · exact eigenSubrep_le s z hz c hc hgr j i.castSucc hlt (hPE j w)
    · have hmem : P j w ∈ eigenSubrep A.ρ z hz (c j) ⊓ s.subrepresentation i.succ :=
        Submodule.mem_inf.mpr ⟨hPE j w, aeval_apply_mem (A.ρ z) _
          (fun x hx => (s.subrepresentation i.succ).apply_mem_toSubmodule z hx) _ w.2⟩
      rw [eigenSubrep_inf_eq_bot s z hz c hc hgr j i.succ (by simpa using hgt)] at hmem
      rw [mem_bot_iff.mp hmem]
      exact Submodule.zero_mem _

/-- The eigenspace of the `i`th scalar is equivalent to the `i`th graded piece. -/
def eigenEquivGraded (i : Fin n) :
    (eigenSubrep A.ρ z hz (c i)).toRepresentation.Equiv (s.gradedRepresentation i).ρ :=
  (eigenToGraded s z hz c hc hgr i).ofBijective (eigenToGraded_bijective s z hz c hc hgr i)

include hc hgr in
/-- The eigenspaces span the whole representation. -/
theorem iSup_eigenSubrep : ⨆ i, eigenSubrep A.ρ z hz (c i) = ⊤ := by
  rw [eq_iSup_inf_eigenSubrep A.ρ z hz c hc (aeval_nodal_eq_zero s z c hgr) ⊤]
  simp

include hc hgr in
/-- Every subrepresentation is the sum of its intersections with the eigenspaces. -/
theorem eq_iSup_inf (S : Subrepresentation A.ρ) :
    S = ⨆ i, S ⊓ eigenSubrep A.ρ z hz (c i) :=
  eq_iSup_inf_eigenSubrep A.ρ z hz c hc (aeval_nodal_eq_zero s z c hgr) S

section Simple

variable (hs : s.HasSimpleFactors)

include hc hgr hs in
theorem isIrreducible_eigenSubrep (i : Fin n) :
    (eigenSubrep A.ρ z hz (c i)).toRepresentation.IsIrreducible :=
  (isIrreducible_iff_of_equiv (eigenEquivGraded s z hz c hc hgr i)).mpr (hs i)

include hc hgr hs in
theorem eigenSubrep_ne_bot (i : Fin n) : eigenSubrep A.ρ z hz (c i) ≠ ⊥ := by
  obtain ⟨v, hv⟩ := exists_ne_zero_of_isIrreducible
    (isIrreducible_eigenSubrep s z hz c hc hgr hs i)
  intro h
  exact hv (Subtype.ext (mem_bot_iff.mp (h.le v.2)))

include hc hgr hs in
/-- An eigenspace either lies in a subrepresentation or meets it trivially. -/
theorem eigenSubrep_le_or_inf_eq_bot (S : Subrepresentation A.ρ) (i : Fin n) :
    eigenSubrep A.ρ z hz (c i) ≤ S ∨ S ⊓ eigenSubrep A.ρ z hz (c i) = ⊥ := by
  let E := eigenSubrep A.ρ z hz (c i)
  let T : Subrepresentation E.toRepresentation :=
    { toSubmodule := S.toSubmodule.comap E.toSubmodule.subtype
      apply_mem_toSubmodule := fun g _ hv => S.apply_mem_toSubmodule g hv }
  have := isIrreducible_eigenSubrep s z hz c hc hgr hs i
  rcases IsSimpleOrder.eq_bot_or_eq_top T with hT | hT
  · right
    rw [eq_bot_iff]
    intro v hv
    obtain ⟨hvS, hvE⟩ := Submodule.mem_inf.mp hv
    have hmem : (⟨v, hvE⟩ : E.toSubmodule) ∈ T := hvS
    rw [hT] at hmem
    exact mem_bot_iff.mpr (congrArg Subtype.val (mem_bot_iff.mp hmem))
  · left
    intro v hv
    have hmem : (⟨v, hv⟩ : E.toSubmodule) ∈ T := by
      rw [hT]
      exact mem_top _
    exact hmem

include hc hgr hs in
/-- Every subrepresentation is the sum of the eigenspaces it contains. -/
theorem eq_iSup_eigenSubrep_le (S : Subrepresentation A.ρ) :
    S = ⨆ (i : Fin n) (_ : eigenSubrep A.ρ z hz (c i) ≤ S), eigenSubrep A.ρ z hz (c i) := by
  conv_lhs => rw [eq_iSup_inf s z hz c hc hgr S]
  refine iSup_congr fun i => ?_
  by_cases h : eigenSubrep A.ρ z hz (c i) ≤ S
  · rw [inf_eq_right.mpr h, iSup_pos h]
  · rw [iSup_neg h]
    exact (eigenSubrep_le_or_inf_eq_bot s z hz c hc hgr hs S i).resolve_left h

include hc hgr hs in
/-- Subrepresentations are compared through the eigenspaces they contain. -/
theorem le_iff_eigenSubrep_le (S S' : Subrepresentation A.ρ) :
    S ≤ S' ↔ ∀ i, eigenSubrep A.ρ z hz (c i) ≤ S → eigenSubrep A.ρ z hz (c i) ≤ S' := by
  constructor
  · exact fun h i hi => hi.trans h
  · intro h
    rw [eq_iSup_eigenSubrep_le s z hz c hc hgr hs S]
    exact iSup₂_le fun i hi => h i hi

include hc hgr hs in
/-- An injective intertwiner from a representation with a nonzero `c j`-eigenvector
has image containing the `j`th eigenspace. -/
theorem eigenSubrep_le_range_of_eigenvector {W : Type uW} [AddCommGroup W] [Module k W]
    {τ : Representation k G W} (ι : τ.IntertwiningMap A.ρ) (hι : Function.Injective ι)
    (j : Fin n) (u : W) (hu : u ≠ 0) (hzu : τ z u = c j • u) :
    eigenSubrep A.ρ z hz (c j) ≤ ι.range := by
  have hE : ι u ∈ eigenSubrep A.ρ z hz (c j) := by
    rw [mem_eigenSubrep, ← ι.isIntertwining, hzu, map_smul]
  rcases eigenSubrep_le_or_inf_eq_bot s z hz c hc hgr hs ι.range j with h | h
  · exact h
  · exfalso
    have hmem : ι u ∈ ι.range ⊓ eigenSubrep A.ρ z hz (c j) :=
      Submodule.mem_inf.mpr ⟨(Representation.IntertwiningMap.mem_range _ _ ι _).mpr ⟨u, rfl⟩, hE⟩
    rw [h] at hmem
    exact hu (hι ((mem_bot_iff.mp hmem).trans (map_zero ι).symm))

include hc hgr hs in
/-- Subrepresentation clause of the detection lemma: if a representation maps
injectively into `A` and has a nonzero intertwiner to a representation on which
`z` acts by `a`, then `a` is some `c j` and the image contains the `j`th
eigenspace. -/
theorem exists_eigenSubrep_le_range {W : Type uW} [AddCommGroup W] [Module k W]
    {U : Type*} [AddCommGroup U] [Module k U]
    {τ : Representation k G W} {σ : Representation k G U}
    (ι : τ.IntertwiningMap A.ρ) (hι : Function.Injective ι)
    (f : τ.IntertwiningMap σ) (hf : f ≠ 0) (a : k) (hσ : ∀ u, σ z u = a • u) :
    ∃ j, c j = a ∧ eigenSubrep A.ρ z hz (c j) ≤ ι.range := by
  obtain ⟨u, hu⟩ : ∃ u, f u ≠ 0 := by
    by_contra h
    push Not at h
    exact hf (Representation.IntertwiningMap.ext (LinearMap.ext h))
  have hnodal := aeval_nodal_eq_zero s z c hgr
  have hfa : ∀ p : k[X], f (aeval (τ z) p u) = p.eval a • f u := fun p => by
    rw [intertwining_aeval f z p u, Module.End.aeval_apply_of_mem_apply_eq_smul (hσ _)]
  have hτ : aeval (τ z) (Lagrange.nodal Finset.univ c) u = 0 := by
    apply hι
    rw [intertwining_aeval ι z, hnodal, LinearMap.zero_apply, map_zero]
  have hev : (Lagrange.nodal Finset.univ c).eval a = 0 := by
    have h := hfa (Lagrange.nodal Finset.univ c)
    rw [hτ, map_zero] at h
    exact (smul_eq_zero.mp h.symm).resolve_right hu
  rw [Lagrange.eval_nodal, Finset.prod_eq_zero_iff] at hev
  obtain ⟨j, -, hj⟩ := hev
  have hja : c j = a := (sub_eq_zero.mp hj).symm
  refine ⟨j, hja, ?_⟩
  set u' := aeval (τ z) (Lagrange.basis Finset.univ c j) u with hu'
  have hfu' : f u' = f u := by
    rw [hfa, ← hja, Lagrange.eval_basis_self hc.injOn (Finset.mem_univ j), one_smul]
  have hu'0 : u' ≠ 0 := fun h0 => hu (by rw [← hfu', h0, map_zero])
  have hzu' : τ z u' = c j • u' := by
    have h := aeval_basis_mem_eigenspace (τ z) c ?_ j u
    · exact Module.End.mem_eigenspace_iff.mp h
    · ext x
      apply hι
      rw [LinearMap.zero_apply, map_zero, intertwining_aeval ι z, hnodal, LinearMap.zero_apply]
  exact eigenSubrep_le_range_of_eigenvector s z hz c hc hgr hs ι hι j u' hu'0 hzu'

include hc hgr hs in
/-- An injective intertwiner from a representation filtered by graded pieces on
which `z` acts by distinct scalars `c (e j)`, all nonzero, has image containing
exactly the eigenspaces indexed by the range of `e`. -/
theorem eigenSubrep_le_range_iff {B : Rep.{uW} k G} {n' : ℕ} (t : ObjectRepFiltration B n')
    (ht : t.HasSimpleFactors) (e : Fin n' → Fin n) (he : Function.Injective e)
    (htgr : ∀ j v, (t.gradedRepresentation j).ρ z v = c (e j) • v)
    (ι : B.ρ.IntertwiningMap A.ρ) (hι : Function.Injective ι) (i : Fin n) :
    eigenSubrep A.ρ z hz (c i) ≤ ι.range ↔ i ∈ Set.range e := by
  constructor
  · intro hle
    by_contra hi
    have hbot := range_inf_eigenSubrep_eq_bot ι z hz (∏ j, (X - C (c (e j))))
      (aeval_prod_eq_zero t z (c ∘ e) htgr) (c i) (by
        rw [eval_prod, Finset.prod_ne_zero_iff]
        intro j _
        rw [eval_sub, eval_X, eval_C, sub_ne_zero]
        intro hij
        exact hi ⟨j, (hc hij).symm⟩)
    rw [inf_eq_right.mpr hle] at hbot
    exact eigenSubrep_ne_bot s z hz c hc hgr hs i hbot
  · rintro ⟨j, rfl⟩
    have hce : Function.Injective (c ∘ e) := hc.comp he
    have hne := eigenSubrep_ne_bot t z hz (c ∘ e) hce htgr ht j
    obtain ⟨u, hu, hu0⟩ := (Submodule.ne_bot_iff _).mp
      (fun h => hne (Subrepresentation.toSubmodule_injective h))
    exact eigenSubrep_le_range_of_eigenvector s z hz c hc hgr hs ι hι (e j) u hu0
      (mem_eigenSubrep.mp hu)

end Simple

include hc hgr in
/-- Quotient clause of the detection lemma: if `A` maps onto a representation
receiving a nonzero intertwiner from a representation on which `z` acts by `a`,
then `a` is some `c j` and the kernel does not contain the `j`th eigenspace. -/
theorem exists_eigenSubrep_not_le_ker {W : Type uW} [AddCommGroup W] [Module k W]
    {U : Type*} [AddCommGroup U] [Module k U]
    {τ : Representation k G W} {σ : Representation k G U}
    (q : A.ρ.IntertwiningMap τ) (hq : Function.Surjective q)
    (f : σ.IntertwiningMap τ) (hf : f ≠ 0) (a : k) (hσ : ∀ u, σ z u = a • u) :
    ∃ j, c j = a ∧ ¬ eigenSubrep A.ρ z hz (c j) ≤ q.ker := by
  obtain ⟨u, hu⟩ : ∃ u, f u ≠ 0 := by
    by_contra h
    push Not at h
    exact hf (Representation.IntertwiningMap.ext (LinearMap.ext h))
  obtain ⟨w, hw⟩ := hq (f u)
  have hnodal := aeval_nodal_eq_zero s z c hgr
  have hzfu : τ z (f u) = a • f u := by rw [← f.isIntertwining, hσ, map_smul]
  have hqa : ∀ p : k[X], q (aeval (A.ρ z) p w) = p.eval a • f u := fun p => by
    rw [intertwining_aeval q z p w, hw, Module.End.aeval_apply_of_mem_apply_eq_smul hzfu]
  have hev : (Lagrange.nodal Finset.univ c).eval a = 0 := by
    have h := hqa (Lagrange.nodal Finset.univ c)
    rw [hnodal, LinearMap.zero_apply, map_zero] at h
    exact (smul_eq_zero.mp h.symm).resolve_right hu
  rw [Lagrange.eval_nodal, Finset.prod_eq_zero_iff] at hev
  obtain ⟨j, -, hj⟩ := hev
  have hja : c j = a := (sub_eq_zero.mp hj).symm
  refine ⟨j, hja, fun hle => hu ?_⟩
  have hmem := hle (aeval_basis_mem_eigenspace (A.ρ z) c hnodal j w)
  have h := hqa (Lagrange.basis Finset.univ c j)
  rw [← hja, Lagrange.eval_basis_self hc.injOn (Finset.mem_univ j), one_smul] at h
  rw [← h]
  exact hmem

section Isolation

variable (hs : s.HasSimpleFactors)

include hc hgr in
/-- A surjection onto a representation with a nonzero `c i`-eigenvector does not
kill the `i`th eigenspace. -/
theorem not_eigenSubrep_le_ker_of_eigenvector {B : Rep.{uW} k G}
    (p : A.ρ.IntertwiningMap B.ρ) (hp : Function.Surjective p) (i : Fin n) (u : B)
    (hu : u ≠ 0) (hzu : B.ρ z u = c i • u) :
    ¬ eigenSubrep A.ρ z hz (c i) ≤ p.ker := by
  let E := eigenSubrep B.ρ z hz (c i)
  have hf : subrepInclusion E ≠ 0 := by
    intro h
    apply hu
    have := congrArg (fun φ : E.toRepresentation.IntertwiningMap B.ρ =>
      φ ⟨u, mem_eigenSubrep.mpr hzu⟩) h
    simpa using this
  obtain ⟨j, hj, hle⟩ := exists_eigenSubrep_not_le_ker s z hz c hc hgr p hp
    (subrepInclusion E) hf (c i) (fun v => Subtype.ext (mem_eigenSubrep.mp v.2))
  rwa [hc hj] at hle

include hz hc hgr hs in
/-- Isolation, subrepresentation form. Let `ι : τ → A` be injective, with a
nonzero intertwiner from `τ` to a representation on which `z` acts by `c i0`.
Suppose every other index `i` is separated: some surjection `p` from `A` onto a
representation filtered by irreducible pieces with distinct scalars `c (e j)`,
where `i` occurs and `i0` does not, restricts on `τ` to an injective or zero map.
Then `τ` is equivalent to the `i0`th graded piece. -/
theorem nonempty_equiv_graded_of_sub {W : Type uW} [AddCommGroup W] [Module k W]
    {U : Type*} [AddCommGroup U] [Module k U]
    {τ : Representation k G W} {σ : Representation k G U}
    (ι : τ.IntertwiningMap A.ρ) (hι : Function.Injective ι)
    (f : τ.IntertwiningMap σ) (hf : f ≠ 0) (i0 : Fin n) (hσ : ∀ u, σ z u = c i0 • u)
    (hsep : ∀ i, i ≠ i0 → ∃ (B : Rep.{uW} k G) (n' : ℕ) (t : ObjectRepFiltration B n')
      (e : Fin n' → Fin n), t.HasSimpleFactors ∧ Function.Injective e ∧
      (∀ j v, (t.gradedRepresentation j).ρ z v = c (e j) • v) ∧
      i ∈ Set.range e ∧ i0 ∉ Set.range e ∧
      ∃ p : A.ρ.IntertwiningMap B.ρ, Function.Surjective p ∧
        (Function.Injective (p.comp ι) ∨ p.comp ι = 0)) :
    Nonempty (τ.Equiv (s.gradedRepresentation i0).ρ) := by
  obtain ⟨j0, hj0, hle0⟩ := exists_eigenSubrep_le_range s z hz c hc hgr hs ι hι f hf (c i0) hσ
  rw [hc hj0] at hle0
  have hnot : ∀ i, i ≠ i0 → ¬ eigenSubrep A.ρ z hz (c i) ≤ ι.range := by
    intro i hi hle
    obtain ⟨B, n', t, e, ht, he, htgr, ⟨j, rfl⟩, hi0, p, hp, hpι⟩ := hsep i hi
    have hzero : p.comp ι = 0 := by
      refine hpι.resolve_left fun hinj => ?_
      obtain ⟨j', hj', -⟩ := exists_eigenSubrep_le_range t z hz (c ∘ e) (hc.comp he) htgr ht
        (p.comp ι) hinj f hf (c i0) hσ
      exact hi0 ⟨j', hc hj'⟩
    have hker : ι.range ≤ p.ker := by
      intro v hv
      obtain ⟨u, rfl⟩ := (Representation.IntertwiningMap.mem_range _ _ ι _).mp hv
      change p (ι u) = 0
      exact congrArg (fun φ : τ.IntertwiningMap B.ρ => φ u) hzero
    have hne := eigenSubrep_ne_bot t z hz (c ∘ e) (hc.comp he) htgr ht j
    obtain ⟨u, hu, hu0⟩ := (Submodule.ne_bot_iff _).mp
      (fun h => hne (Subrepresentation.toSubmodule_injective h))
    exact not_eigenSubrep_le_ker_of_eigenvector s z hz c hc hgr p hp (e j) u hu0
      (mem_eigenSubrep.mp hu) (hle.trans hker)
  have hrange : ι.range = eigenSubrep A.ρ z hz (c i0) := by
    refine le_antisymm ?_ hle0
    rw [eq_iSup_eigenSubrep_le s z hz c hc hgr hs ι.range]
    refine iSup₂_le fun i hi => ?_
    by_cases h : i = i0
    · rw [h]
    · exact absurd hi (hnot i h)
  have hmem : ∀ v, ι v ∈ (eigenSubrep A.ρ z hz (c i0)).toSubmodule := fun v => by
    rw [← hrange]
    exact (Representation.IntertwiningMap.mem_range _ _ ι _).mpr ⟨v, rfl⟩
  let φ : τ.IntertwiningMap (eigenSubrep A.ρ z hz (c i0)).toRepresentation :=
    { toLinearMap := LinearMap.codRestrict _ ι.toLinearMap hmem
      isIntertwining' := fun g => by
        ext v
        exact LinearMap.congr_fun (ι.isIntertwining' g) v }
  have hφ : Function.Bijective φ := by
    constructor
    · intro v v' h
      exact hι (congrArg Subtype.val h)
    · intro x
      have hx : (x : A) ∈ ι.range := by
        rw [hrange]
        exact x.2
      obtain ⟨v, hv⟩ := (Representation.IntertwiningMap.mem_range _ _ ι _).mp hx
      exact ⟨v, Subtype.ext hv⟩
  exact ⟨(φ.ofBijective hφ).trans (eigenEquivGraded s z hz c hc hgr i0)⟩

include hz hc hgr hs in
/-- Isolation, quotient form. Let `q : A → τ` be surjective, with a nonzero
intertwiner into `τ` from a representation on which `z` acts by `c i0`. Suppose
every other index `i` is separated: some injection `ι` into `A` from a
representation filtered by irreducible pieces with distinct scalars `c (e j)`,
where `i` occurs and `i0` does not, composes with `q` to a surjective or zero
map. Then the `i0`th graded piece is equivalent to `τ`. -/
theorem nonempty_equiv_graded_of_quot {W : Type uW} [AddCommGroup W] [Module k W]
    {U : Type*} [AddCommGroup U] [Module k U]
    {τ : Representation k G W} {σ : Representation k G U}
    (q : A.ρ.IntertwiningMap τ) (hq : Function.Surjective q)
    (f : σ.IntertwiningMap τ) (hf : f ≠ 0) (i0 : Fin n) (hσ : ∀ u, σ z u = c i0 • u)
    (hsep : ∀ i, i ≠ i0 → ∃ (B : Rep.{uW} k G) (n' : ℕ) (t : ObjectRepFiltration B n')
      (e : Fin n' → Fin n), t.HasSimpleFactors ∧ Function.Injective e ∧
      (∀ j v, (t.gradedRepresentation j).ρ z v = c (e j) • v) ∧
      i ∈ Set.range e ∧ i0 ∉ Set.range e ∧
      ∃ ι : B.ρ.IntertwiningMap A.ρ, Function.Injective ι ∧
        (Function.Surjective (q.comp ι) ∨ q.comp ι = 0)) :
    Nonempty ((s.gradedRepresentation i0).ρ.Equiv τ) := by
  have hker : ∀ i, i ≠ i0 → eigenSubrep A.ρ z hz (c i) ≤ q.ker := by
    intro i hi
    obtain ⟨B, n', t, e, ht, he, htgr, hie, hi0, ι, hι, hqι⟩ := hsep i hi
    have hzero : q.comp ι = 0 := by
      refine hqι.resolve_left fun hsurj => ?_
      obtain ⟨j', hj', -⟩ := exists_eigenSubrep_not_le_ker t z hz (c ∘ e) (hc.comp he) htgr
        (q.comp ι) hsurj f hf (c i0) hσ
      exact hi0 ⟨j', hc hj'⟩
    refine ((eigenSubrep_le_range_iff s z hz c hc hgr hs t ht e he htgr ι hι i).mpr hie).trans ?_
    intro v hv
    obtain ⟨u, rfl⟩ := (Representation.IntertwiningMap.mem_range _ _ ι _).mp hv
    change q (ι u) = 0
    exact congrArg (fun φ : B.ρ.IntertwiningMap τ => φ u) hzero
  obtain ⟨j0, hj0, hnle⟩ := exists_eigenSubrep_not_le_ker s z hz c hc hgr q hq f hf (c i0) hσ
  rw [hc hj0] at hnle
  have hinf : q.ker ⊓ eigenSubrep A.ρ z hz (c i0) = ⊥ :=
    (eigenSubrep_le_or_inf_eq_bot s z hz c hc hgr hs q.ker i0).resolve_left hnle
  let φ := q.comp (subrepInclusion (eigenSubrep A.ρ z hz (c i0)))
  have hφ : Function.Bijective φ := by
    constructor
    · rw [injective_iff_map_eq_zero]
      intro v hv
      have hmem : (v : A) ∈ q.ker ⊓ eigenSubrep A.ρ z hz (c i0) :=
        Submodule.mem_inf.mpr ⟨hv, v.2⟩
      rw [hinf] at hmem
      exact Subtype.ext (mem_bot_iff.mp hmem)
    · intro y
      obtain ⟨w, rfl⟩ := hq y
      have hnodal := aeval_nodal_eq_zero s z c hgr
      refine ⟨⟨_, aeval_basis_mem_eigenspace (A.ρ z) c hnodal i0 w⟩, ?_⟩
      change q (aeval (A.ρ z) (Lagrange.basis Finset.univ c i0) w) = q w
      have hsum := sum_aeval_basis (A.ρ z) c hc hnodal w
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i0)] at hsum
      conv_rhs => rw [← hsum]
      have hzero : ∑ j ∈ Finset.univ.erase i0,
          q (aeval (A.ρ z) (Lagrange.basis Finset.univ c j) w) = 0 := by
        refine Finset.sum_eq_zero fun j hj => ?_
        have h := hker j (Finset.ne_of_mem_erase hj)
          (aeval_basis_mem_eigenspace (A.ρ z) c hnodal j w)
        exact h
      rw [map_add, map_sum, hzero, add_zero]
  exact ⟨(eigenEquivGraded s z hz c hc hgr i0).symm.trans (φ.ofBijective hφ)⟩

end Isolation

end Distinct

end Filtration

end Langlands.CentralEigenspaceSplitting
