import Langlands.GroupScheme.Lie.TorusCentralizerSlice

/-! # Lie containment in a torus-centralizer slice after field extension -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped Matrix TensorProduct

namespace Langlands.GroupScheme.Lie

set_option backward.isDefEq.respectTransparency false

variable {k K : Type u} [Field k] [Field K] [Algebra k K]
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom] {d : ℕ}
  (c : FiniteCoordinates G d)

local notation "G_K" => Functor.obj (GroupScheme.baseChange (algebraBaseMap k K)) G

local instance torusCentralizerSliceBaseChangeAffine : IsAffineHom (G_K).X.hom := by
  change IsAffineHom (CategoryTheory.Limits.pullback.snd G.X.hom (algebraBaseMap k K))
  infer_instance

/-- The linear kernel comparison is the multiplicative one on `Additive` vectors. -/
theorem kernelBaseChangeLinearEquiv_ofMul {A : Type u} [CommRing A] [Algebra k A]
    [Algebra K A] [IsScalarTower k K A] (x : lieKernel G_K A) :
    kernelBaseChangeLinearEquiv k K G A (Additive.ofMul x) =
      Additive.ofMul (kernelBaseChangeEquiv k K G A x) :=
  rfl

/-- The pulled-back finite coordinates of a Lie vector of `G_K` are the original coordinates
of its image under the pullback comparison. -/
theorem FiniteCoordinates.baseChange_equiv_apply {A : Type u} [CommRing A] [Algebra k A]
    [Algebra K A] [IsScalarTower k K A] (x : Additive (lieKernel G_K A)) :
    (c.baseChange k K).equiv (.of (CommRingCat.of K) A) x =
      c.equiv (.of (CommRingCat.of k) A) (kernelBaseChangeLinearEquiv k K G A x) := by
  have hA : ‹Algebra k A› = Algebra.compHom A (algebraMap k K) := by
    apply Algebra.algebra_ext
    intro r
    exact congrArg (fun f : k →+* A => f r) (IsScalarTower.algebraMap_eq k K A)
  cases hA
  rfl

variable {T₀ : CommGroupScheme (Spec (CommRingCat.of k))} (j₀ : T₀.toGrp ⟶ G)

/-- If the Lie algebra of `T₀` centralizes every column of `B`, then each adjoint matrix
`ad(j₀ Y)` kills `B`. -/
theorem tangentMatrix_targetMap_mul_eq_zero {r : ℕ} (B : Matrix (Fin d) (Fin r) k)
    (hB : ∀ j (Y : lieKernel T₀.toGrp (CommRingCat.of k)), Additive.ofMul (targetMap j₀ _ Y) ∈
      elementCentralizerLie G ((c.equiv (.of (CommRingCat.of k) k)).symm (fun i => B i j)).toMul)
    (Y : lieKernel T₀.toGrp (CommRingCat.of k)) :
    (adjointRepresentation c).tangentMatrix k (targetMap j₀ _ Y) * B = 0 := by
  ext i j
  have h := hB j Y
  rw [mem_elementCentralizerLie_iff_adjointDifferential c] at h
  change adjointDifferentialFamily c (Additive.ofMul (targetMap j₀ _ Y))
    (c.equiv (.of (CommRingCat.of k) k) ((c.equiv (.of (CommRingCat.of k) k)).symm
      (fun i => B i j))) = 0 at h
  rw [LinearEquiv.apply_symm_apply, adjointDifferentialFamily_apply, Matrix.toLin'_apply] at h
  simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct] using congrFun h i

variable [IsAffineHom T₀.toGrp.X.hom] [LocallyOfFiniteType T₀.toGrp.X.hom]

local notation "T_K" => Functor.obj (GroupScheme.baseChange (algebraBaseMap k K)) T₀.toGrp

local instance torusCentralizerSliceBaseChangeTorusAffine : IsAffineHom (T_K).X.hom := by
  change IsAffineHom (CategoryTheory.Limits.pullback.snd T₀.toGrp.X.hom (algebraBaseMap k K))
  infer_instance

/-- For a coordinate vector `v` over `K`, the `K`-linear map sending a Lie element `t` of the
base change of `T₀` to `ad(j₀ t) v`, computed with the adjoint matrix of `G_K` in the pulled-back
finite coordinates. -/
def targetMapAdjointApplyBaseChange (v : Fin d → K) :
    Additive (lieKernel (T_K) K) →ₗ[K] (Fin d → K) :=
  (LinearMap.applyₗ v).comp
    ((Matrix.toLin'.toLinearMap.comp
      ((adjointRepresentation (c.baseChange k K)).kernelDifferential K)).comp
      (targetMapLinear ((GroupScheme.baseChange (algebraBaseMap k K)).map j₀) K))

omit [LocallyOfFiniteType T₀.toGrp.X.hom] in
/-- Evaluation of `targetMapAdjointApplyBaseChange` as a matrix-vector product. -/
theorem targetMapAdjointApplyBaseChange_apply (v : Fin d → K) (t : lieKernel (T_K) K) :
    targetMapAdjointApplyBaseChange c j₀ v (Additive.ofMul t) =
      (adjointRepresentation (c.baseChange k K)).tangentMatrix K
        (targetMap ((GroupScheme.baseChange (algebraBaseMap k K)).map j₀) K t) *ᵥ v := by
  rw [targetMapAdjointApplyBaseChange, LinearMap.comp_apply, LinearMap.applyₗ_apply_apply,
    LinearMap.comp_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
    MatrixRepresentation.kernelDifferential_apply, Matrix.toLin'_apply]
  rfl

/-- If the Lie algebra of `T₀` centralizes every column of `B` over `k`, then over a field
extension `K`, each adjoint matrix `ad(j₀ t)` for a Lie element `t` of the base change of `T₀`
kills every vector in the `K`-column space of `B`. -/
theorem tangentMatrix_targetMap_baseChange_mulVec_eq_zero {r : ℕ} (B : Matrix (Fin d) (Fin r) k)
    (hB : ∀ j (Y : lieKernel T₀.toGrp (CommRingCat.of k)), Additive.ofMul (targetMap j₀ _ Y) ∈
      elementCentralizerLie G ((c.equiv (.of (CommRingCat.of k) k)).symm (fun i => B i j)).toMul)
    (s : Fin r → K) (t : lieKernel (T_K) K) :
    (adjointRepresentation (c.baseChange k K)).tangentMatrix K
        (targetMap ((GroupScheme.baseChange (algebraBaseMap k K)).map j₀) K t) *ᵥ
      (B.map (algebraMap k K) *ᵥ s) = 0 := by
  let L := targetMapAdjointApplyBaseChange c j₀ (B.map (algebraMap k K) *ᵥ s)
  have hgen : ∀ Y : lieKernel T₀.toGrp (CommRingCat.of k),
      L (Additive.ofMul (kernelFieldExtension (K := K) T₀.toGrp Y)) = 0 := by
    intro Y
    rw [targetMapAdjointApplyBaseChange_apply, tangentMatrix_targetMap_kernelFieldExtension,
      Matrix.mulVec_mulVec,
      ← Matrix.map_mul, tangentMatrix_targetMap_mul_eq_zero c j₀ B hB Y]
    simp
  have hL : ∀ x, L x = 0 := by
    intro x
    obtain ⟨w, rfl⟩ := (schemeScalarExtension (K := K) T₀.toGrp).surjective x
    induction w using TensorProduct.inductionOn with
    | tmul a y =>
      have hy : a ⊗ₜ[k] y = a • ((1 : K) ⊗ₜ[k] y) := by
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      rw [hy, map_smul, schemeScalarExtension_one_tmul, map_smul, hgen, smul_zero]
    | add x y hx hy => rw [map_add, map_add, hx, hy, add_zero]
  rw [← targetMapAdjointApplyBaseChange_apply]
  exact hL (Additive.ofMul t)

/-- **Slice Lie containment after field extension.** Suppose the Lie algebra of `T₀`
centralizes every column of `B` over `k`. Then over a field extension `K` of `k`, the Lie
algebra of the base change of `T₀` centralizes every Lie element of `G_K` whose coordinates
lie in the `K`-column space of `B`. -/
theorem targetMap_mem_elementCentralizerLie_baseChange_of_mulVec {r : ℕ}
    (B : Matrix (Fin d) (Fin r) k)
    (hB : ∀ j (Y : lieKernel T₀.toGrp (CommRingCat.of k)), Additive.ofMul (targetMap j₀ _ Y) ∈
      elementCentralizerLie G ((c.equiv (.of (CommRingCat.of k) k)).symm (fun i => B i j)).toMul)
    (Z : lieKernel G K)
    (hZ : c.equiv (.of (CommRingCat.of k) K) (Additive.ofMul Z) ∈
      Set.range (B.map (algebraMap k K)).mulVec)
    (t : lieKernel (T_K) (CommRingCat.of K)) :
    Additive.ofMul (targetMap ((GroupScheme.baseChange (algebraBaseMap k K)).map j₀) _ t) ∈
      elementCentralizerLie (G_K) ((kernelBaseChangeEquiv k K G K).symm Z) := by
  obtain ⟨s, hs⟩ := hZ
  rw [mem_elementCentralizerLie_iff_adjointDifferential (c.baseChange k K)]
  have hc : (c.baseChange k K).equiv (.of (CommRingCat.of K) K)
      (Additive.ofMul ((kernelBaseChangeEquiv k K G K).symm Z)) =
        c.equiv (.of (CommRingCat.of k) K) (Additive.ofMul Z) := by
    rw [FiniteCoordinates.baseChange_equiv_apply, kernelBaseChangeLinearEquiv_ofMul,
      MulEquiv.apply_symm_apply]
  rw [hc, ← hs, adjointDifferentialFamily_apply, Matrix.toLin'_apply]
  exact tangentMatrix_targetMap_baseChange_mulVec_eq_zero c j₀ B hB s t

end Langlands.GroupScheme.Lie
