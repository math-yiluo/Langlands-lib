import Langlands.GroupScheme.KostantRosenlicht.Points
import Langlands.GroupScheme.Chevalley.SubspaceMatrix
import Langlands.GroupScheme.UnipotentMatrixCriterion.Coordinates

/-! # Right translations on the coordinate algebra of a unipotent group -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped TensorProduct

namespace Langlands.GroupScheme.KostantRosenlicht

open AffineLinearEmbedding
open Algebra.TensorProduct (productMap)

variable {k : Type u} [Field k] {F : CommAlgCat.{u} (CommRingCat.of k) ⥤ GrpCat.{u}}
  {B : CommAlgCat.{u} (CommRingCat.of k)} (e : (F ⋙ forget GrpCat).CorepresentableBy B)

/-- Right translation by the `k`-point `g` classified by `v`: the coordinate map of `u ↦ u * g`,
i.e. `b ↦ ∑ v (b₂) • b₁` for `comul b = ∑ b₁ ⊗ b₂`. -/
def charTranslate (v : B →ₐ[CommRingCat.of k] CommRingCat.of k) :
    B →ₐ[CommRingCat.of k] B :=
  (productMap (AlgHom.id _ B) ((Algebra.ofId _ B).comp v)).comp (comul e)

/-- On points, precomposition with a right translation is right multiplication. -/
theorem pt_comp_charTranslate {A : CommAlgCat.{u} (CommRingCat.of k)}
    (a : B →ₐ[CommRingCat.of k] A) (v : B →ₐ[CommRingCat.of k] CommRingCat.of k) :
    pt e (a.comp (charTranslate e v)) = pt e a * pt e ((Algebra.ofId _ A).comp v) := by
  rw [← pt_productMap_comp_comul, charTranslate, ← AlgHom.comp_assoc]
  congr 2
  ext x <;> simp

/-- The character classifying the inverse of the `k`-point classified by `v`. -/
def charInv (v : B →ₐ[CommRingCat.of k] CommRingCat.of k) :
    B →ₐ[CommRingCat.of k] CommRingCat.of k :=
  (e.homEquiv.symm (pt e (A := CommAlgCat.of _ (CommRingCat.of k)) v)⁻¹).hom

theorem charTranslate_charTranslate_charInv (v : B →ₐ[CommRingCat.of k] CommRingCat.of k)
    (b : B) : charTranslate e v (charTranslate e (charInv e v) b) = b := by
  have h := pt_comp_charTranslate e (charTranslate e v) (charInv e v)
  have h1 := pt_comp_charTranslate e (AlgHom.id _ B) v
  rw [AlgHom.id_comp] at h1
  have h2 : pt e (A := B) ((Algebra.ofId _ B).comp v) *
      pt e (A := B) ((Algebra.ofId _ B).comp (charInv e v)) = 1 := by
    rw [pt_comp e (A := CommAlgCat.of _ (CommRingCat.of k)) v,
      pt_comp e (A := CommAlgCat.of _ (CommRingCat.of k)) (charInv e v), charInv,
      pt_homEquiv_symm, map_inv, mul_inv_cancel]
  rw [h1, mul_assoc, h2, mul_one] at h
  exact congrArg (fun f : B →ₐ[CommRingCat.of k] B => f b) (pt_injective e h)

/-- The right translation by `v` is the right action of `v` viewed as a functional. -/
theorem charTranslate_eq_rightAct (v : B →ₐ[CommRingCat.of k] CommRingCat.of k) (b : B) :
    letI := (bialgebra e).toCoalgebra
    charTranslate e v b = rightAct v.toLinearMap b := by
  let := (bialgebra e).toCoalgebra
  rw [rightAct_apply, charTranslate, AlgHom.comp_apply]
  change productMap _ _ (comul e b) =
    TensorProduct.rid _ _ (v.toLinearMap.lTensor B (comul e b))
  induction comul e b using TensorProduct.inductionOn with
  | tmul x y => simp [Algebra.smul_def, mul_comm]
  | add x y hx hy => simp only [map_add, hx, hy]

section Unipotent

variable [IsAlgClosed k] [Algebra.FiniteType (CommRingCat.of k) B] [IsReduced B]

/-- Every right translate of `w` by a functional lies in the span of its translates by
`k`-points (the `k`-points are dense in the reduced group). -/
theorem rightAct_mem_span_charTranslate (m : Module.Dual (CommRingCat.of k) B) (w : B) :
    letI := (bialgebra e).toCoalgebra
    rightAct m w ∈
      Submodule.span (CommRingCat.of k) (Set.range fun v => charTranslate e v w) := by
  let := (bialgebra e).toCoalgebra
  by_contra h
  obtain ⟨φ, hφ, hle⟩ := Submodule.exists_le_ker_of_notMem h
  apply hφ
  have h0 : leftAct φ w = 0 := by
    refine eq_zero_of_forall_algHom (k := CommRingCat.of k) fun χ => ?_
    have h1 := apply_leftAct χ.toLinearMap φ w
    rw [AlgHom.toLinearMap_apply] at h1
    rw [h1, ← charTranslate_eq_rightAct]
    exact LinearMap.mem_ker.mp (hle (Submodule.subset_span ⟨χ, rfl⟩))
  rw [← apply_leftAct, h0, map_zero]

/-- A subspace stable under right translation by `k`-points is stable under all right
translations by functionals. -/
theorem rightAct_mem_of_charTranslate_mem {W : Submodule (CommRingCat.of k) B}
    (hW : ∀ v, ∀ w ∈ W, charTranslate e v w ∈ W) (m : Module.Dual (CommRingCat.of k) B)
    {w : B} (hw : w ∈ W) :
    letI := (bialgebra e).toCoalgebra
    rightAct m w ∈ W :=
  Submodule.span_le.mpr (Set.range_subset_iff.mpr fun v => hW v w hw)
    (rightAct_mem_span_charTranslate e m w)

omit [IsAlgClosed k] [Algebra.FiniteType (CommRingCat.of k) B] [IsReduced B] in
/-- For a unipotent group, a nonzero subspace stable under all right translations contains the
constant function `1`. -/
theorem one_mem_of_rightAct_mem (hU : IsUnipotent (Corepresented.groupScheme F e))
    {W : Submodule (CommRingCat.of k) B}
    (hW : letI := (bialgebra e).toCoalgebra
      ∀ (m : Module.Dual (CommRingCat.of k) B), ∀ w ∈ W, rightAct m w ∈ W)
    (hne : W ≠ ⊥) : (1 : B) ∈ W := by
  let := (bialgebra e).toCoalgebra
  obtain ⟨f, hfW, hf0⟩ := W.ne_bot_iff.mp hne
  obtain ⟨U₀, hU₀fg, hU₀⟩ := exists_fg_rightAct (K := CommRingCat.of k) f
  set V := Submodule.span (CommRingCat.of k)
    (Set.range fun m : Module.Dual (CommRingCat.of k) B => rightAct m f) with hVdef
  have hVU₀ : V ≤ U₀ := Submodule.span_le.mpr (Set.range_subset_iff.mpr hU₀)
  have hVW : V ≤ W := Submodule.span_le.mpr (Set.range_subset_iff.mpr fun m => hW m f hfW)
  have hV : ∀ (g : Module.Dual (CommRingCat.of k) B) (x : B), x ∈ V → rightAct g x ∈ V := by
    intro g x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨m, rfl⟩ := hx
      rw [rightAct_rightAct]
      exact Submodule.subset_span ⟨_, rfl⟩
    | zero => simp
    | add x y _ _ hx hy => rw [map_add]; exact V.add_mem hx hy
    | smul c x _ hx => rw [map_smul]; exact V.smul_mem c hx
  have hfV : f ∈ V := by
    rw [← rightAct_counit (K := CommRingCat.of k) f]
    exact Submodule.subset_span ⟨_, rfl⟩
  have : FiniteDimensional (CommRingCat.of k) U₀ := Module.Finite.iff_fg.mpr hU₀fg
  have : FiniteDimensional (CommRingCat.of k) V := Submodule.finiteDimensional_of_le hVU₀
  let b := Module.finBasis (CommRingCat.of k) V
  set N := Module.finrank (CommRingCat.of k) V
  have hN : 0 < N := Module.finrank_pos_iff_exists_ne_zero.mpr
    ⟨⟨f, hfV⟩, fun h => hf0 (congrArg Subtype.val h)⟩
  have : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  set M := Chevalley.subspaceMatrix V b
  let ρ : MatrixRepresentation (Corepresented.groupScheme F e) (Fin N) :=
    toGLHom e M (Chevalley.comul_subspaceMatrix V b hV) (Chevalley.counit_subspaceMatrix V b)
  obtain ⟨c, hc0, hcfix⟩ := hU (Fin N) ρ
  have hM : UnipotentMatrixCriterion.coefficientMatrix e ρ = M := by
    refine (UnipotentMatrixCriterion.coefficientMatrix_groupSchemeMap e
      (toGL e M (Chevalley.comul_subspaceMatrix V b hV) (Chevalley.counit_subspaceMatrix V b))).trans
      ?_
    ext i j
    change (e.homEquiv.symm (e.homEquiv (𝟙 B))).hom (M i j) = M i j
    rw [Equiv.symm_apply_apply]
    rfl
  have hfix := (UnipotentMatrixCriterion.isFixedVector_iff e ρ c).mp hcfix
  rw [hM] at hfix
  set ε := Coalgebra.counit (R := CommRingCat.of k) (A := B)
  have hleft : ∀ j, leftAct ε (b j : B) = ∑ i, ε (b i : B) • M i j := by
    intro j
    rw [leftAct_apply, Chevalley.comul_basis V b hV j, map_sum, map_sum]
    simp [M]
  set x : B := ∑ i, c i • (b i : B)
  have hx : x = ε x • (1 : B) := by
    calc x = leftAct ε x := (leftAct_counit x).symm
      _ = ∑ j, c j • ∑ i, ε (b i : B) • M i j := by
        simp only [x, map_sum, map_smul, hleft]
      _ = ∑ i, ε (b i : B) • ∑ j, c j • M i j := by
        simp only [Finset.smul_sum, smul_smul, mul_comm]
        exact Finset.sum_comm
      _ = ∑ i, ε (b i : B) • c i • (1 : B) := by simp only [hfix]
      _ = ε x • (1 : B) := by
        simp only [x, map_sum, map_smul, Finset.sum_smul, smul_smul, smul_eq_mul, mul_comm]
  have hx0 : x ≠ 0 := by
    intro h
    apply hc0
    have h' : ∑ i, c i • b i = 0 := Subtype.ext (by simpa [x] using h)
    funext i
    exact Fintype.linearIndependent_iff.mp b.linearIndependent c h' i
  have hε : ε x ≠ 0 := fun h => hx0 (by rw [hx, h, zero_smul])
  have hxV : x ∈ V := V.sum_mem fun i _ => V.smul_mem _ (b i).2
  have h1 : (ε x)⁻¹ • x = (1 : B) := by
    calc (ε x)⁻¹ • x = (ε x)⁻¹ • ε x • (1 : B) := congrArg ((ε x)⁻¹ • ·) hx
      _ = 1 := by rw [smul_smul, inv_mul_cancel₀ hε, one_smul]
  exact hVW (h1 ▸ V.smul_mem _ hxV)

end Unipotent

end Langlands.GroupScheme.KostantRosenlicht
