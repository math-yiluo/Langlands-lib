import Langlands.GroupScheme.Unipotent.FieldReflectionStatement
import Langlands.GroupScheme.Unipotent.BaseChange

/-! # Reflection of unipotence under field extension -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry TensorProduct Coalgebra Module
open scoped CategoryTheory.MonObj CategoryTheory.Obj

namespace Langlands.GroupScheme.Unipotent

open AffineLinearEmbedding Chevalley

section CoordinateReflection

variable {k : Type*} [Field k] (K : Type*) [Field K] [Algebra k K]
  {B : Type*} [Ring B] [Bialgebra k B]

/-- In the scalar extension, the right translation of a lifted basis vector is a
linear combination of the same lifted basis. -/
theorem rightAct_one_tmul_basis
    (V : Submodule k B) {N : ℕ} (b : Basis (Fin N) k V)
    (hV : ∀ (f : Module.Dual k B) (v : B), v ∈ V → rightAct f v ∈ V)
    (f : Module.Dual K (K ⊗[k] B)) (j : Fin N) :
    rightAct f ((1 : K) ⊗ₜ[k] (b j : B)) =
      ∑ i, f ((1 : K) ⊗ₜ[k] subspaceMatrix V b i j) •
        ((1 : K) ⊗ₜ[k] (b i : B)) := by
  rw [rightAct_apply, TensorProduct.comul_tmul, CommSemiring.comul_apply,
    comul_basis V b hV, TensorProduct.tmul_sum, map_sum, map_sum, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp only [AlgebraTensorModule.tensorTensorTensorComm_tmul,
    LinearMap.lTensor_tmul, TensorProduct.rid_tmul]

/-- The coordinate unipotence predicate descends along an arbitrary field extension. -/
theorem OneMemStable.of_baseChange (hB : OneMemStable K (K ⊗[k] B)) :
    OneMemStable k B := by
  classical
  intro V hfin hV hV0
  let b := Module.finBasis k V
  let incl : K ⊗[k] V →ₗ[K] K ⊗[k] B := V.subtype.baseChange K
  let W : Submodule K (K ⊗[k] B) := LinearMap.range incl
  have hincl (c : K) (v : V) : incl (c ⊗ₜ[k] v) = c ⊗ₜ[k] (v : B) := rfl
  have hbmem (j : Fin (finrank k V)) :
      (1 : K) ⊗ₜ[k] (b j : B) ∈ W := ⟨1 ⊗ₜ[k] b j, rfl⟩
  have hstable (f : Module.Dual K (K ⊗[k] B)) :
      ∀ t : K ⊗[k] V, rightAct f (incl t) ∈ W := by
    intro t
    induction t using TensorProduct.inductionOn with
    | tmul c v =>
      rw [← b.sum_repr v, TensorProduct.tmul_sum, map_sum, map_sum]
      apply W.sum_mem
      intro j _
      rw [TensorProduct.tmul_smul, LinearMap.map_smul_of_tower,
        LinearMap.map_smul_of_tower]
      apply W.smul_of_tower_mem
      rw [show incl (c ⊗ₜ[k] b j) = c • incl ((1 : K) ⊗ₜ[k] b j) by
        rw [hincl, hincl, TensorProduct.smul_tmul', smul_eq_mul, mul_one]]
      rw [map_smul, hincl, rightAct_one_tmul_basis K V b hV]
      apply W.smul_mem
      exact W.sum_mem fun i _ => W.smul_mem _ (hbmem i)
    | add x y hx hy =>
      rw [map_add, map_add]
      exact W.add_mem hx hy
  obtain ⟨l, hl⟩ := Module.Projective.exists_dual_eq_one k (one_ne_zero : (1 : K) ≠ 0)
  let π : (K ⊗[k] B) →ₗ[k] B := TensorProduct.lid k B ∘ₗ l.rTensor B
  have hπ (c : K) (v : B) : π (c ⊗ₜ[k] v) = l c • v := by simp [π]
  have hπmem : ∀ t : K ⊗[k] V, π (incl t) ∈ V := by
    intro t
    induction t using TensorProduct.inductionOn with
    | tmul c v => rw [hincl, hπ]; exact V.smul_mem _ v.2
    | add x y hx hy => rw [map_add, map_add]; exact V.add_mem hx hy
  have hW0 : W ≠ ⊥ := by
    obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hV0
    intro hW
    have hm : (1 : K) ⊗ₜ[k] v ∈ W := ⟨1 ⊗ₜ[k] (⟨v, hv⟩ : V), rfl⟩
    rw [hW, Submodule.mem_bot] at hm
    have hz := congrArg π hm
    rw [hπ, hl, one_smul, map_zero] at hz
    exact hv0 hz
  have h1 : (1 : K ⊗[k] B) ∈ W :=
    hB W inferInstance (by rintro f _ ⟨t, rfl⟩; exact hstable f t) hW0
  obtain ⟨t, ht⟩ := h1
  have h := hπmem t
  rw [ht, Algebra.TensorProduct.one_def, hπ, hl, one_smul] at h
  exact h

end CoordinateReflection

/-- Unipotence of an affine group scheme descends along a field extension. -/
theorem _root_.Langlands.GroupScheme.IsUnipotent.of_baseChange
    {k K : Type u} [Field k] [Field K] [Algebra k K]
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
    (hG : IsUnipotent ((GroupScheme.baseChange
      (Spec.map (CommRingCat.ofHom (algebraMap k K)))).obj G)) :
    IsUnipotent G := by
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  let C := AffineCoordinates.coordinateCogroup G
  let C' := ((commHopfAlgCatEquivCogrpCommAlgCat (CommRingCat.of K)).functor.obj
    (HopfCoordinates.scalarExtension k K C.X.unop)).unop
  let e :=
    (GroupScheme.baseChange _).mapIso (AffineCoordinates.hopfSpecIso G).symm ≪≫
      HopfCoordinates.baseChangeSpecIso k K C.X.unop
  have hC' : OneMemStable K (K ⊗[k] C.X.unop) :=
    oneMemStable_of_isUnipotent_cogroup C' (IsUnipotent.of_iso e.symm hG)
  have hC : OneMemStable k C.X.unop := hC'.of_baseChange K
  exact IsUnipotent.of_iso (AffineCoordinates.coordinateCogroupIso G).symm
    (isUnipotent_cogroup_of_oneMemStable C hC)

/-- Proof of the published unipotence field-reflection proposition. -/
theorem _root_.Langlands.GroupScheme.unipotentFieldReflection :
    UnipotentFieldReflectionStatement.{u} := by
  intro k K _ _ _ G _ hG
  exact hG.of_baseChange

end Langlands.GroupScheme.Unipotent
