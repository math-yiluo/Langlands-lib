import Langlands.Algebra.GroupLikeBaseChange
import Langlands.Algebra.GroupLikeReconstruction
import Langlands.GroupScheme.StabilizerImageDichotomy
import Langlands.GroupScheme.CentralSurjectionImage.EigenGrading
import Mathlib.LinearAlgebra.Eigenspace.Pi
import Mathlib.LinearAlgebra.Eigenspace.Semisimple
import Mathlib.LinearAlgebra.Eigenspace.Minpoly
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import Mathlib.FieldTheory.Separable
import Mathlib.RingTheory.FiniteType

/-! # Matrix coefficients, group-like elements and semisimplicity -/

noncomputable section

universe u v w

open TensorProduct Polynomial

namespace Langlands.GroupScheme.SemisimplePoints

section Eigen

variable {K : Type u} [Field K] {V : Type v} [AddCommGroup V] [Module K V]

/-- An endomorphism is semisimple when the space is spanned by eigenvectors whose eigenvalues
lie in a fixed finite set. -/
theorem isSemisimple_of_span_eigenvectors (f : Module.End K V) (s : Finset K)
    (hspan : Submodule.span K {v : V | ∃ μ ∈ s, f v = μ • v} = ⊤) : f.IsSemisimple := by
  classical
  have hsep : (∏ μ ∈ s, (X - C ((fun x : K => x) μ))).Separable :=
    separable_prod_X_sub_C_iff'.mpr fun _ _ _ _ h => h
  refine Module.End.isSemisimple_of_squarefree_aeval_eq_zero hsep.squarefree ?_
  refine LinearMap.ext_on hspan ?_
  rintro v ⟨μ, hμ, hv⟩
  rw [Module.End.aeval_apply_of_mem_apply_eq_smul hv, LinearMap.zero_apply]
  have h0 : (∏ μ ∈ s, (X - C ((fun x : K => x) μ))).eval μ = 0 := by
    rw [eval_prod]
    exact Finset.prod_eq_zero hμ (by simp)
  rw [h0, zero_smul]

end Eigen

section Coefficients

variable {K : Type u} [Field K] {C : Type v} [AddCommGroup C] [Module K C] [Coalgebra K C]
  {n : Type w} [Fintype n] [DecidableEq n]

/-- If a coalgebra over a field is spanned by its group-like elements, then every linear
functional sends a matrix of matrix coefficients to a semisimple matrix. -/
theorem isSemisimple_map_of_span_groupLike
    (hspan : Submodule.span K {c : C | IsGroupLikeElem K c} = ⊤) (N : Matrix n n C)
    (hcomul : ∀ i j, Coalgebra.comul (R := K) (N i j) = ∑ l, N i l ⊗ₜ[K] N l j)
    (hcounit : ∀ i j, Coalgebra.counit (R := K) (N i j) = (1 : Matrix n n K) i j)
    (ψ : C →ₗ[K] K) : Module.End.IsSemisimple (Matrix.toLin' (N.map ψ)) := by
  classical
  let b := Langlands.GroupLike.basisOfSpan hspan
  let c : GroupLike K C → Matrix n n K := fun g => Matrix.of fun i j => b.repr (N i j) g
  have hc : ∀ g i j, c g i j = b.repr (N i j) g := fun _ _ _ => rfl
  let S : Finset (GroupLike K C) :=
    Finset.univ.biUnion fun p : n × n => (b.repr (N p.1 p.2)).support
  have hexp : ∀ i j, N i j = ∑ g ∈ S, c g i j • (g : C) := by
    intro i j
    have hsub : (b.repr (N i j)).support ⊆ S := fun g hg =>
      Finset.mem_biUnion.mpr ⟨(i, j), Finset.mem_univ _, hg⟩
    conv_lhs => rw [← b.linearCombination_repr (N i j)]
    rw [Finsupp.linearCombination_apply,
      Finsupp.sum_of_support_subset _ hsub (fun g a => a • b g) (fun _ _ => zero_smul K _)]
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [hc]
    congr 1
    exact Langlands.GroupLike.basisOfSpan_apply hspan g
  have hsum : ∑ g ∈ S, c g = 1 := by
    ext i j
    rw [Matrix.sum_apply, ← hcounit i j, hexp i j, map_sum]
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [map_smul, g.isGroupLikeElem_val.counit_eq_one, smul_eq_mul, mul_one]
  have hmul : ∀ g h, c g * c h = if g = h then c g else 0 := by
    intro g h
    let Φ : C ⊗[K] C →ₗ[K] K :=
      LinearMap.mul' K K ∘ₗ TensorProduct.map (b.coord g) (b.coord h)
    have hΦ : Φ ∘ₗ Coalgebra.comul = if g = h then b.coord g else 0 := by
      refine b.ext fun g' => ?_
      have hg' : Coalgebra.comul (R := K) (b g') = b g' ⊗ₜ[K] b g' := by
        simp only [b, Langlands.GroupLike.basisOfSpan_apply]
        exact g'.isGroupLikeElem_val.comul_eq_tmul_self
      rw [LinearMap.comp_apply, hg']
      simp only [Φ, LinearMap.comp_apply, TensorProduct.map_tmul, LinearMap.mul'_apply,
        Module.Basis.coord_apply, Module.Basis.repr_self]
      by_cases hgh : g = h
      · subst hgh
        rw [ite_eq_left rfl, Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply]
        split_ifs <;> simp
      · rw [ite_eq_right hgh, LinearMap.zero_apply, Finsupp.single_apply, Finsupp.single_apply]
        split_ifs with h1 h2
        · exact absurd (h1.symm.trans h2) hgh
        all_goals simp
    ext i j
    have h := LinearMap.congr_fun hΦ (N i j)
    rw [LinearMap.comp_apply, hcomul, map_sum] at h
    rw [Matrix.mul_apply]
    simp only [Φ, LinearMap.comp_apply, TensorProduct.map_tmul, LinearMap.mul'_apply,
      Module.Basis.coord_apply] at h
    simp only [hc]
    rw [h]
    split_ifs <;> rfl
  have hM : N.map ψ = ∑ g ∈ S, ψ g • c g := by
    ext i j
    rw [Matrix.map_apply, hexp i j, map_sum, Matrix.sum_apply]
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [map_smul, Matrix.smul_apply, smul_eq_mul, smul_eq_mul, mul_comm]
  refine isSemisimple_of_span_eigenvectors _ (S.image fun g : GroupLike K C => ψ (g : C)) ?_
  rw [eq_top_iff]
  intro w _
  have hw : w = ∑ g ∈ S, Matrix.toLin' (c g) w := by
    rw [← LinearMap.sum_apply, ← map_sum, hsum, Matrix.toLin'_one, LinearMap.id_apply]
  rw [hw]
  refine Submodule.sum_mem _ fun g hg => Submodule.subset_span
    ⟨ψ g, Finset.mem_image_of_mem _ hg, ?_⟩
  have hsimp : ∑ x ∈ S, ψ x • c x * c g = ψ g • c g := by
    simp only [Matrix.smul_mul, hmul, smul_ite, smul_zero]
    rw [Finset.sum_ite_eq' S g, ite_eq_left hg]
  rw [← Module.End.mul_apply, Module.End.mul_eq_comp, ← Matrix.toLin'_mul, hM, Finset.sum_mul,
    hsimp, map_smul, LinearMap.smul_apply]

end Coefficients

section Reconstruction

variable {K : Type u} [Field K] [IsAlgClosed K] {C : Type u} [CommRing C] [Bialgebra K C]
  [IsReduced C] [Algebra.FiniteType K C] {n : Type w} [Fintype n] [DecidableEq n]

/-- Over an algebraically closed field, if a reduced finite-type bialgebra has a matrix of
matrix coefficients whose values at all rational points are pairwise commuting semisimple
matrices, then every entry of that matrix is a linear combination of group-like elements. -/
theorem mem_span_groupLike_of_isSemisimple (N : Matrix n n C)
    (hcomul : ∀ i j, Coalgebra.comul (R := K) (N i j) = ∑ l, N i l ⊗ₜ[K] N l j)
    (hcounit : ∀ i j, Coalgebra.counit (R := K) (N i j) = (1 : Matrix n n K) i j)
    (hcomm : ∀ ψ ψ' : C →ₐ[K] K, Commute (N.map ψ) (N.map ψ'))
    (hss : ∀ ψ : C →ₐ[K] K, Module.End.IsSemisimple (Matrix.toLin' (N.map ψ))) (i j : n) :
    N i j ∈ Submodule.span K {c : C | IsGroupLikeElem K c} := by
  classical
  set P := Submodule.span K {c : C | IsGroupLikeElem K c}
  let f : (C →ₐ[K] K) → Module.End K (n → K) := fun ψ => Matrix.toLin' (N.map ψ)
  have hf : Pairwise fun ψ ψ' => Commute (f ψ) (f ψ') := fun ψ ψ' _ =>
    (hcomm ψ ψ').map (Matrix.toLinAlgEquiv' (R := K) (n := n))
  have htop := Module.End.iSup_iInf_maxGenEigenspace_eq_top_of_iSup_maxGenEigenspace_eq_top_of_commute
    f hf (fun ψ => Module.End.iSup_maxGenEigenspace_eq_top (f ψ))
  let T : n → (n → K) →ₗ[K] C := fun b => ∑ l, (LinearMap.proj l).smulRight (N b l)
  have hT : ∀ b w, T b w = ∑ l, w l • N b l := by
    intro b w
    simp [T]
  let W : Submodule K (n → K) := ⨅ b, P.comap (T b)
  have hW : W = ⊤ := by
    rw [eq_top_iff, ← htop]
    refine iSup_le fun χ v hv => ?_
    rw [Submodule.mem_iInf] at hv
    have hv' : ∀ ψ : C →ₐ[K] K, (N.map ψ).mulVec v = χ ψ • v := by
      intro ψ
      have h := hv ψ
      rw [(hss ψ).isFinitelySemisimple.maxGenEigenspace_eq_eigenspace,
        Module.End.mem_eigenspace_iff] at h
      simpa [f, Matrix.toLin'_apply] using h
    rw [Submodule.mem_iInf]
    intro b
    rw [Submodule.mem_comap]
    by_cases hv0 : v = 0
    · subst hv0
      simp
    obtain ⟨a, ha⟩ : ∃ a, v a ≠ 0 := by
      by_contra h
      push Not at h
      exact hv0 (funext h)
    have hψT : ∀ (ψ : C →ₐ[K] K) l, ψ (T l v) = χ ψ * v l := by
      intro ψ l
      have h := congrFun (hv' ψ) l
      simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, Pi.smul_apply, smul_eq_mul] at h
      rw [hT, map_sum, ← h]
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [map_smul, smul_eq_mul, mul_comm]
    obtain ⟨g, hgd⟩ : ∃ g : C, g = (v a)⁻¹ • T a v := ⟨_, rfl⟩
    have hTg : ∀ l, T l v = v l • g := by
      intro l
      have hnil : IsNilpotent (T l v - v l • g) := by
        apply StabilizerImageDichotomy.isNilpotent_of_forall_algHom (k := K)
        intro ψ
        rw [map_sub, map_smul, hgd, map_smul, hψT, hψT, smul_eq_mul, smul_eq_mul]
        field_simp
        ring
      exact sub_eq_zero.mp hnil.eq_zero
    have hg : IsGroupLikeElem K g := by
      constructor
      · rw [hgd, map_smul, hT, map_sum]
        simp only [map_smul, hcounit, Matrix.one_apply, smul_eq_mul, mul_ite, mul_one, mul_zero,
          Finset.sum_ite_eq, Finset.mem_univ, ite_true]
        exact inv_mul_cancel₀ ha
      · have h1 : Coalgebra.comul (R := K) (T a v) = ∑ m, N a m ⊗ₜ[K] T m v := by
          rw [hT, map_sum]
          simp_rw [map_smul, hcomul, Finset.smul_sum, hT, TensorProduct.tmul_sum,
            TensorProduct.tmul_smul]
          exact Finset.sum_comm
        have h2 : ∑ m, N a m ⊗ₜ[K] T m v = T a v ⊗ₜ[K] g := by
          rw [hT a v]
          simp_rw [hTg, ← TensorProduct.smul_tmul, ← TensorProduct.sum_tmul]
        rw [hgd, map_smul, h1, h2, TensorProduct.smul_tmul', ← hgd]
    rw [hTg b]
    exact P.smul_mem _ (Submodule.subset_span hg)
  have hmem : Pi.single j 1 ∈ W := hW ▸ Submodule.mem_top
  have h := (Submodule.mem_iInf _).mp hmem i
  rw [Submodule.mem_comap, hT] at h
  simpa [Pi.single_apply] using h

end Reconstruction

section FiniteGeneration

/-- A finite-type commutative Hopf algebra over a field that is spanned by its group-like
elements has a finitely generated group of group-like elements. -/
theorem addGroupFG_groupLike {K C : Type u} [Field K] [CommRing C] [HopfAlgebra K C]
    [Algebra.FiniteType K C]
    (hspan : Submodule.span K {c : C | IsGroupLikeElem K c} = ⊤) :
    AddGroup.FG (Additive (GroupLike K C)) := by
  let e : C ≃ₐ[K] AddMonoidAlgebra K (Additive (GroupLike K C)) :=
    ((Langlands.MonoidAlgebra.bialgEquivOfSpanGroupLike hspan).symm.trans
      (MonoidAlgebra.toAdditiveBialgEquiv K K (GroupLike K C))).toAlgEquiv
  have : Algebra.FiniteType K (AddMonoidAlgebra K (Additive (GroupLike K C))) :=
    Algebra.FiniteType.equiv inferInstance e
  exact AddMonoidAlgebra.finiteType_iff_group_fg.mp this

end FiniteGeneration

section BaseChange

open CentralSurjectionImage.EigenGrading

variable {k : Type u} [Field k] {H : Type u} [CommRing H] [HopfAlgebra k H]
  {K : Type u} [Field K] [Algebra k K] {n : Type} [Fintype n] [DecidableEq n]

omit [DecidableEq n] in
/-- Matrix coefficients stay matrix coefficients after scalar extension. -/
theorem comul_one_tmul_matrix (M : Matrix n n H)
    (hcomul : ∀ i j, Coalgebra.comul (R := k) (M i j) = ∑ l, M i l ⊗ₜ[k] M l j) (i j : n) :
    Coalgebra.comul (R := K) ((1 : K) ⊗ₜ[k] M i j : K ⊗[k] H) =
      ∑ l, ((1 : K) ⊗ₜ[k] M i l : K ⊗[k] H) ⊗ₜ[K] ((1 : K) ⊗ₜ[k] M l j : K ⊗[k] H) := by
  rw [comul_one_tmul, hcomul, map_sum]
  rfl

omit [Fintype n] in
/-- The counit of a scalar-extended matrix coefficient. -/
theorem counit_one_tmul_matrix (M : Matrix n n H)
    (hcounit : ∀ i j, Coalgebra.counit (R := k) (M i j) = (1 : Matrix n n k) i j) (i j : n) :
    Coalgebra.counit (R := K) ((1 : K) ⊗ₜ[k] M i j : K ⊗[k] H) = (1 : Matrix n n K) i j := by
  rw [TensorProduct.counit_tmul, hcounit, Matrix.one_apply, Matrix.one_apply]
  have h1 : Coalgebra.counit (R := K) (1 : K) = 1 := rfl
  rw [h1]
  split_ifs <;> simp

/-- If the scalar extension `K ⊗[k] H` is spanned by group-like elements, then every
`K`-valued point sends a matrix of matrix coefficients of `H` to a semisimple matrix. -/
theorem isSemisimple_of_span_baseChange
    (hspan : Submodule.span K {c : K ⊗[k] H | IsGroupLikeElem K c} = ⊤) (M : Matrix n n H)
    (hcomul : ∀ i j, Coalgebra.comul (R := k) (M i j) = ∑ l, M i l ⊗ₜ[k] M l j)
    (hcounit : ∀ i j, Coalgebra.counit (R := k) (M i j) = (1 : Matrix n n k) i j)
    (f : H →ₐ[k] K) : Module.End.IsSemisimple (Matrix.toLin' (M.map f)) := by
  have h := isSemisimple_map_of_span_groupLike hspan
    (M.map fun b => ((1 : K) ⊗ₜ[k] b : K ⊗[k] H)) (comul_one_tmul_matrix M hcomul)
    (counit_one_tmul_matrix M hcounit) (extend f).toLinearMap
  have hM : (M.map fun b => ((1 : K) ⊗ₜ[k] b : K ⊗[k] H)).map (extend f).toLinearMap =
      M.map f := by
    ext i j
    simp
  rwa [hM] at h

/-- Over an algebraically closed field `K`, if the matrices of all `K`-valued points on all
matrices of matrix coefficients of `H` commute pairwise and are semisimple, and every element
of `H` is a linear combination of matrix coefficients, then `K ⊗[k] H` is spanned by its
group-like elements (provided it is reduced and of finite type). -/
theorem span_baseChange_of_isSemisimple [IsAlgClosed K] [IsReduced (K ⊗[k] H)]
    [Algebra.FiniteType K (K ⊗[k] H)]
    (hcoeff : ∀ b : H, ∃ (N : ℕ) (M : Matrix (Fin N) (Fin N) H),
      (∀ i j, Coalgebra.comul (R := k) (M i j) = ∑ l, M i l ⊗ₜ[k] M l j) ∧
      (∀ i j, Coalgebra.counit (R := k) (M i j) = (1 : Matrix (Fin N) (Fin N) k) i j) ∧
      b ∈ Submodule.span k (Set.range fun p : Fin N × Fin N => M p.1 p.2))
    (hpts : ∀ (N : ℕ) (M : Matrix (Fin N) (Fin N) H),
      (∀ i j, Coalgebra.comul (R := k) (M i j) = ∑ l, M i l ⊗ₜ[k] M l j) →
      (∀ i j, Coalgebra.counit (R := k) (M i j) = (1 : Matrix (Fin N) (Fin N) k) i j) →
      (∀ f f' : H →ₐ[k] K, Commute (M.map f) (M.map f')) ∧
        ∀ f : H →ₐ[k] K, Module.End.IsSemisimple (Matrix.toLin' (M.map f))) :
    Submodule.span K {c : K ⊗[k] H | IsGroupLikeElem K c} = ⊤ := by
  set P := Submodule.span K {c : K ⊗[k] H | IsGroupLikeElem K c}
  have hone : ∀ b : H, ((1 : K) ⊗ₜ[k] b : K ⊗[k] H) ∈ P := by
    intro b
    obtain ⟨N, M, hcomul, hcounit, hb⟩ := hcoeff b
    obtain ⟨hcomm, hss⟩ := hpts N M hcomul hcounit
    let NC : Matrix (Fin N) (Fin N) (K ⊗[k] H) := M.map fun b => ((1 : K) ⊗ₜ[k] b : K ⊗[k] H)
    let res : (K ⊗[k] H →ₐ[K] K) → (H →ₐ[k] K) := fun ψ =>
      (ψ.restrictScalars k).comp Algebra.TensorProduct.includeRight
    have hres : ∀ ψ : K ⊗[k] H →ₐ[K] K, NC.map ψ = M.map (res ψ) := fun ψ => rfl
    have hle : Submodule.span k (Set.range fun p : Fin N × Fin N => M p.1 p.2) ≤
        (P.restrictScalars k).comap
          (Algebra.TensorProduct.includeRight : H →ₐ[k] K ⊗[k] H).toLinearMap := by
      rw [Submodule.span_le]
      rintro _ ⟨p, rfl⟩
      exact mem_span_groupLike_of_isSemisimple NC (comul_one_tmul_matrix M hcomul)
        (counit_one_tmul_matrix M hcounit)
        (fun ψ ψ' => by rw [hres, hres]; exact hcomm _ _)
        (fun ψ => by rw [hres]; exact hss _) p.1 p.2
    exact hle hb
  rw [eq_top_iff]
  rintro x -
  induction x using TensorProduct.induction_on with
  | zero => exact P.zero_mem
  | tmul a b =>
    have h : (a ⊗ₜ[k] b : K ⊗[k] H) = a • ((1 : K) ⊗ₜ[k] b : K ⊗[k] H) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [h]
    exact P.smul_mem a (hone b)
  | add x y hx hy => exact P.add_mem hx hy

end BaseChange

end Langlands.GroupScheme.SemisimplePoints
