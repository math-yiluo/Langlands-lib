import Langlands.Algebra.GradedHopf.Triangular
import Langlands.GroupScheme.ComoduleMatrixCoefficients
import Mathlib.RingTheory.FiniteType

/-! # Graded matrix coefficients of a graded bialgebra over a field -/

noncomputable section

open TensorProduct DirectSum Langlands.GroupScheme

namespace Langlands.Algebra.GradedHopf

namespace GradedComodule

variable {k A : Type*} [Field k] [CommRing A] [Bialgebra k A]

section Coalgebra

variable (k A)

theorem coassoc : Comodule.Coassoc (Coalgebra.comul (R := k) (A := A)) :=
  Coalgebra.coassoc

theorem rightCounit :
    Comodule.RightCounit (Coalgebra.comul (R := k) (A := A)) (Coalgebra.counit (R := k)) := by
  refine LinearMap.ext fun a => ?_
  simp [Coalgebra.lTensor_counit_comul]

theorem leftCounit :
    Comodule.LeftCounit (Coalgebra.comul (R := k) (A := A)) (Coalgebra.counit (R := k)) := by
  refine LinearMap.ext fun a => ?_
  simp [Coalgebra.rTensor_counit_comul]

end Coalgebra

variable {𝒜 : ℤ → Submodule k A} [GradedAlgebra 𝒜]

/-- Contracting the right factor of a tensor of total degree `d` and then projecting to degree
`e` is the contraction against the degree-`(d - e)` part of the functional. -/
theorem gradeProj_rid_lTensor {d : ℤ} {x : A ⊗[k] A} (hx : x ∈ tensorGrade 𝒜 𝒜 d)
    (m : A →ₗ[k] k) (e : ℤ) :
    gradeProj 𝒜 e (TensorProduct.rid k A (m.lTensor A x)) =
      TensorProduct.rid k A ((m ∘ₗ gradeProj 𝒜 (d - e)).lTensor A x) := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i, j, a, b, ha, hb, rfl, rfl⟩ := hx
    simp only [LinearMap.lTensor_tmul, TensorProduct.rid_tmul, LinearMap.comp_apply, map_smul]
    rw [gradeProj_of_mem 𝒜 ha, gradeProj_of_mem 𝒜 hb]
    by_cases h : i = e
    · subst h
      rw [ite_eq_left rfl, ite_eq_left (by ring)]
    · rw [ite_eq_right h, ite_eq_right (by omega), map_zero, zero_smul, smul_zero]
  | zero => simp
  | add x y _ _ hx hy => simp only [map_add, hx, hy]
  | smul c x _ hx => simp only [map_smul, hx]

/-- Contracting the left factor of a tensor of total degree `d` against a functional supported
in degree `e` gives an element of degree `d - e`. -/
theorem lid_rTensor_mem {d : ℤ} {x : A ⊗[k] A} (hx : x ∈ tensorGrade 𝒜 𝒜 d)
    (l : A →ₗ[k] k) (e : ℤ) :
    TensorProduct.lid k A ((l ∘ₗ gradeProj 𝒜 e).rTensor A x) ∈ 𝒜 (d - e) := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i, j, a, b, ha, hb, rfl, rfl⟩ := hx
    simp only [LinearMap.rTensor_tmul, TensorProduct.lid_tmul, LinearMap.comp_apply]
    rw [gradeProj_of_mem 𝒜 ha]
    split_ifs with h
    · subst h
      rw [add_sub_cancel_left]
      exact Submodule.smul_mem _ _ hb
    · rw [map_zero, zero_smul]
      exact zero_mem _
  | zero => simp
  | add x y _ _ hx hy => rw [map_add, map_add]; exact add_mem hx hy
  | smul c x _ hx => rw [map_smul, map_smul]; exact Submodule.smul_mem _ c hx

variable (𝒜) in
/-- A subspace closed under every homogeneous projection. -/
def IsGradedSubspace (V : Submodule k A) : Prop :=
  ∀ e, ∀ v ∈ V, gradeProj 𝒜 e v ∈ V

theorem IsGradedSubspace.sup {V W : Submodule k A} (hV : IsGradedSubspace 𝒜 V)
    (hW : IsGradedSubspace 𝒜 W) : IsGradedSubspace 𝒜 (V ⊔ W) := by
  intro e v hv
  obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp hv
  rw [map_add]
  exact Submodule.add_mem_sup (hV e y hy) (hW e z hz)

variable (h𝒜 : IsGradedBialgebra 𝒜)
include h𝒜

/-- The span of the right translates of a homogeneous element is closed under the homogeneous
projections. -/
theorem orbit_isGradedSubspace {d : ℤ} {x : A} (hx : x ∈ 𝒜 d) :
    IsGradedSubspace 𝒜 (Comodule.orbit (Coalgebra.comul (R := k) (A := A)) x) := by
  intro e v hv
  induction hv using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨m, rfl⟩ := hy
    show gradeProj 𝒜 e (Comodule.rightOp _ m x) ∈ _
    rw [Comodule.rightOp_apply, gradeProj_rid_lTensor (h𝒜.comul_mem d x hx)]
    exact Submodule.subset_span ⟨m ∘ₗ gradeProj 𝒜 (d - e), rfl⟩
  | zero => simp
  | add y z _ _ hy hz => rw [map_add]; exact add_mem hy hz
  | smul c y _ hy => rw [map_smul]; exact Submodule.smul_mem _ c hy

/-- Every finite set of homogeneous elements lies in a finite-dimensional subcomodule closed
under the homogeneous projections. -/
theorem exists_stable (s : Finset A) (hs : ∀ x ∈ s, ∃ d, x ∈ 𝒜 d) :
    ∃ V : Submodule k A, FiniteDimensional k V ∧
      Comodule.IsStable (Coalgebra.comul (R := k) (A := A)) V ∧ IsGradedSubspace 𝒜 V ∧
        ∀ x ∈ s, x ∈ V := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨⊥, inferInstance, fun m v hv => by simp_all, fun e v hv => by simp_all,
      by simp⟩
  | insert x s _ ih =>
    obtain ⟨V, hfd, hst, hgr, hsV⟩ := ih fun y hy => hs y (Finset.mem_insert_of_mem hy)
    obtain ⟨d, hd⟩ := hs x (Finset.mem_insert_self x s)
    have := Comodule.orbit_finiteDimensional (Δ := Coalgebra.comul (R := k) (A := A)) x
    refine ⟨Comodule.orbit _ x ⊔ V, inferInstance,
      (Comodule.orbit_isStable (coassoc k A) x).sup hst,
      (orbit_isGradedSubspace h𝒜 hd).sup hgr, ?_⟩
    intro y hy
    rcases Finset.mem_insert.mp hy with rfl | hy
    · exact Submodule.mem_sup_left (Comodule.mem_orbit (rightCounit k A) y)
    · exact Submodule.mem_sup_right (hsV y hy)

omit h𝒜 in
/-- A finite-dimensional subspace closed under the homogeneous projections has a basis of
homogeneous elements. -/
theorem exists_homogeneous_basis (V : Submodule k A) [FiniteDimensional k V]
    (hV : IsGradedSubspace 𝒜 V) :
    ∃ (n : ℕ) (e : Module.Basis (Fin n) k V) (w : Fin n → ℤ), ∀ i, (e i : A) ∈ 𝒜 (w i) := by
  classical
  let T : Set V := {v | ∃ d, (v : A) ∈ 𝒜 d}
  obtain ⟨b, hbT, hspan, hli⟩ := exists_linearIndependent k T
  have htop : Submodule.span k T = ⊤ := by
    rw [eq_top_iff]
    rintro ⟨v, hv⟩ -
    have hv' : (⟨v, hv⟩ : V) =
        ∑ i ∈ (decompose 𝒜 v).support, (⟨gradeProj 𝒜 i v, hV i v hv⟩ : V) := by
      ext
      rw [Submodule.coe_sum]
      exact (sum_gradeProj 𝒜 v).symm
    rw [hv']
    exact Submodule.sum_mem _ fun i _ => Submodule.subset_span ⟨i, gradeProj_mem 𝒜 i v⟩
  let B : Module.Basis b k V :=
    Module.Basis.mk hli (by rw [Subtype.range_coe, hspan, htop])
  have : Finite b := Module.Finite.finite_basis B
  let _ := Fintype.ofFinite b
  choose w hw using fun x : b => hbT x.2
  refine ⟨Fintype.card b, B.reindex (Fintype.equivFin b), fun i => w ((Fintype.equivFin b).symm i),
    fun i => ?_⟩
  rw [Module.Basis.reindex_apply, Module.Basis.mk_apply]
  exact hw _

omit h𝒜 in
/-- The coordinate functionals of a homogeneous basis vanish on the homogeneous components of
other degrees. -/
theorem coord_gradeProj {V : Submodule k A} (hV : IsGradedSubspace 𝒜 V) {n : ℕ}
    (e : Module.Basis (Fin n) k V) {w : Fin n → ℤ} (he : ∀ i, (e i : A) ∈ 𝒜 (w i)) (i : Fin n)
    (v : A) (hv : v ∈ V) :
    e.coord i ⟨gradeProj 𝒜 (w i) v, hV (w i) v hv⟩ = e.coord i ⟨v, hv⟩ := by
  let P : V →ₗ[k] V := (gradeProj 𝒜 (w i)).restrict fun v hv => hV (w i) v hv
  have hP : e.coord i ∘ₗ P = e.coord i := by
    refine e.ext fun j => ?_
    have hPj : P (e j) = if w j = w i then e j else 0 := by
      ext
      simp only [P, LinearMap.restrict_apply]
      rw [gradeProj_of_mem 𝒜 (he j)]
      split_ifs <;> simp
    rw [LinearMap.comp_apply, hPj]
    by_cases hij : j = i
    · subst hij
      rw [ite_eq_left rfl]
    · split_ifs <;> simp [Module.Basis.coord_apply, Ne.symm hij]
  exact LinearMap.congr_fun hP ⟨v, hv⟩

/-- A graded bialgebra over a field has graded matrix coefficients containing any given finite
set of homogeneous elements in their span. -/
theorem exists_corep (s : Finset A) (hs : ∀ x ∈ s, ∃ d, x ∈ 𝒜 d) :
    ∃ (n : ℕ) (w : Fin n → ℤ) (a : Matrix (Fin n) (Fin n) A), Triangular.IsCorep k a ∧
      Triangular.IsGraded 𝒜 w a ∧
        ∀ x ∈ s, x ∈ Submodule.span k (Set.range fun p : Fin n × Fin n => a p.1 p.2) := by
  classical
  set Δ := Coalgebra.comul (R := k) (A := A)
  obtain ⟨V, hfd, hst, hgr, hs⟩ := exists_stable h𝒜 s hs
  obtain ⟨n, e, w, he⟩ := exists_homogeneous_basis V hgr
  have hmu : ∀ i, ∃ g : A →ₗ[k] k, g.comp V.subtype = e.coord i :=
    fun i => LinearMap.exists_extend (e.coord i)
  choose mu hmu using hmu
  let lam : Fin n → A →ₗ[k] k := fun i => mu i ∘ₗ gradeProj 𝒜 (w i)
  have lam_apply : ∀ i (v : A) (hv : v ∈ V), lam i v = e.repr ⟨v, hv⟩ i := by
    intro i v hv
    have h1 := LinearMap.congr_fun (hmu i) ⟨gradeProj 𝒜 (w i) v, hgr (w i) v hv⟩
    simp only [LinearMap.comp_apply, Submodule.subtype_apply] at h1
    change mu i (gradeProj 𝒜 (w i) v) = _
    rw [h1, coord_gradeProj hgr e he i v hv, Module.Basis.coord_apply]
  have lam_e : ∀ i j, lam i (e j : A) = if i = j then 1 else 0 := by
    intro i j
    rw [lam_apply i _ (e j).2]
    simp [Finsupp.single_apply, eq_comm]
  -- The coaction formula on `V`.
  have hΔ : ∀ v ∈ V, Δ v = ∑ i, (e i : A) ⊗ₜ[k] Comodule.leftOp Δ (lam i) v := by
    intro v hv
    apply Comodule.tensor_ext_of_rid
    intro m
    have hw : Comodule.rightOp Δ m v ∈ V := hst m v hv
    have hsum := e.sum_repr ⟨Comodule.rightOp Δ m v, hw⟩
    have hsum' : Comodule.rightOp Δ m v =
        ∑ i, e.repr ⟨Comodule.rightOp Δ m v, hw⟩ i • (e i : A) := by
      have := congrArg Subtype.val hsum
      rw [Submodule.coe_sum] at this
      simp only [Submodule.coe_smul] at this
      exact this.symm
    rw [← Comodule.rightOp_apply, hsum']
    simp only [map_sum, LinearMap.lTensor_tmul, TensorProduct.rid_tmul]
    refine Finset.sum_congr rfl fun i _ => ?_
    congr 1
    rw [← lam_apply i _ hw, Comodule.rightOp_apply, Comodule.apply_rid_lTensor,
      Comodule.leftOp_apply]
  refine ⟨n, w, Matrix.of fun i j => Comodule.leftOp Δ (lam i) (e j), ?_, ?_, ?_⟩
  · refine (Triangular.isCorep_iff _).2 ⟨fun i j => ?_, fun i j => ?_⟩
    · simp only [Matrix.of_apply]
      rw [Comodule.comul_leftOp (coassoc k A), hΔ _ (e j).2]
      simp only [map_sum, LinearMap.rTensor_tmul]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [Comodule.leftOp_apply Δ (lam i) (e l : A)]
      generalize Comodule.leftOp Δ (lam l) (e j : A) = z
      generalize Δ (e l : A) = y
      induction y using TensorProduct.inductionOn with
      | tmul p q => simp [TensorProduct.smul_tmul']
      | add y y' hy hy' => simp only [TensorProduct.add_tmul, map_add, hy, hy']
    · simp only [Matrix.of_apply]
      rw [Comodule.leftOp_apply, ← Comodule.apply_rid_lTensor, ← Comodule.rightOp_apply,
        Comodule.rightOp_counit (rightCounit k A), lam_e]
  · intro i j
    exact lid_rTensor_mem (h𝒜.comul_mem (w j) _ (he j)) (mu i) (w i)
  · intro x hx
    have hxV := hs x hx
    have hej : ∀ j, (e j : A) ∈ Submodule.span k
        (Set.range fun p : Fin n × Fin n => Comodule.leftOp Δ (lam p.1) (e p.2)) := by
      intro j
      rw [← Comodule.leftOp_counit (leftCounit k A) (e j : A), Comodule.leftOp_apply,
        hΔ _ (e j).2]
      simp only [map_sum, LinearMap.rTensor_tmul, TensorProduct.lid_tmul]
      exact Submodule.sum_mem _ fun i _ =>
        Submodule.smul_mem _ _ (Submodule.subset_span ⟨(i, j), rfl⟩)
    have hsum := e.sum_repr ⟨x, hxV⟩
    have hx' : x = ∑ j, e.repr ⟨x, hxV⟩ j • (e j : A) := by
      have := congrArg Subtype.val hsum
      rw [Submodule.coe_sum] at this
      simp only [Submodule.coe_smul] at this
      exact this.symm
    rw [hx']
    exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (hej j)

/-- A finitely generated graded bialgebra over a field has graded matrix coefficients whose
entries generate it. -/
theorem exists_corep_adjoin_eq_top [Algebra.FiniteType k A] :
    ∃ (n : ℕ) (w : Fin n → ℤ) (a : Matrix (Fin n) (Fin n) A), Triangular.IsCorep k a ∧
      Triangular.IsGraded 𝒜 w a ∧
        Algebra.adjoin k (Set.range fun p : Fin n × Fin n => a p.1 p.2) = ⊤ := by
  classical
  obtain ⟨s₀, hs₀⟩ := Algebra.FiniteType.out (R := k) (A := A)
  let s : Finset A := s₀.biUnion fun x => (decompose 𝒜 x).support.image fun d => gradeProj 𝒜 d x
  have hs : ∀ x ∈ s, ∃ d, x ∈ 𝒜 d := by
    intro x hx
    obtain ⟨y, -, hy⟩ := Finset.mem_biUnion.1 hx
    obtain ⟨d, -, rfl⟩ := Finset.mem_image.1 hy
    exact ⟨d, gradeProj_mem 𝒜 d y⟩
  obtain ⟨n, w, a, ha, hg, hspan⟩ := exists_corep h𝒜 s hs
  refine ⟨n, w, a, ha, hg, eq_top_iff.2 ?_⟩
  rw [← hs₀]
  refine Algebra.adjoin_le fun x hx => ?_
  rw [← sum_gradeProj 𝒜 x]
  refine Subalgebra.sum_mem _ fun d hd => Algebra.span_le_adjoin k _ (hspan _ ?_)
  exact Finset.mem_biUnion.2 ⟨x, hx, Finset.mem_image.2 ⟨d, hd, rfl⟩⟩

end GradedComodule

end Langlands.Algebra.GradedHopf
