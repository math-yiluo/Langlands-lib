import Langlands.GroupScheme.Lie.AdjointDominance
import Langlands.GroupScheme.Lie.TorusCentralizer
import Langlands.GroupScheme.Torus.WeightDecomposition
import Mathlib.Algebra.Module.Submodule.Union

/-! # Regular elements in the Lie algebra of a split torus -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.Lie

set_option backward.isDefEq.respectTransparency false

section LinearAlgebra

variable {K V L κ : Type*} [Field K] [AddCommGroup V] [Module K V] [AddCommGroup L]
  [Module K L]

/-- **A generic element of a diagonalizable family.** Let `A` be a linear family of
endomorphisms of `V`, parametrized by `L`, such that `V` is spanned by finitely many nonzero
subspaces `W χ` on each of which every `A y` acts by a scalar. Over an infinite field there is
a parameter `y` such that the range of `A y` and the common kernel of all `A y'` span `V`. -/
theorem exists_range_add_commonKernel [Infinite K] (A : L →ₗ[K] Module.End K V)
    (W : κ → Submodule K V) (hW : ⨆ χ, W χ = ⊤) (hfin : {χ | W χ ≠ ⊥}.Finite)
    (heig : ∀ χ y, ∃ a : K, ∀ w ∈ W χ, A y w = a • w) :
    ∃ y : L, ∀ v : V, ∃ u z : V, (∀ y', A y' z = 0) ∧ A y u + z = v := by
  classical
  let P : κ → Submodule K L := fun χ => ⨅ w : W χ, LinearMap.ker (A.flip w)
  have hP : ∀ χ y, y ∈ P χ ↔ ∀ w ∈ W χ, A y w = 0 := by
    intro χ y
    simp only [P, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.flip_apply, Subtype.forall]
  let J := {χ | W χ ≠ ⊥ ∧ P χ ≠ ⊤}
  have : Finite J := (hfin.subset fun χ hχ => hχ.1).to_subtype
  obtain ⟨y, hy⟩ := Submodule.exists_forall_notMem_of_forall_ne_top
    (fun χ : J => P χ) (fun χ => χ.2.2)
  let Z : Submodule K V := ⨅ y' : L, LinearMap.ker (A y')
  have hle : ∀ χ, W χ ≤ LinearMap.range (A y) ⊔ Z := by
    intro χ
    by_cases hPχ : P χ = ⊤
    · intro w hw
      apply Submodule.mem_sup_right
      simp only [Z, Submodule.mem_iInf, LinearMap.mem_ker]
      intro y'
      exact (hP χ y').mp (hPχ.ge Submodule.mem_top) w hw
    · by_cases hWχ : W χ = ⊥
      · rw [hWχ]
        exact bot_le
      · obtain ⟨a, ha⟩ := heig χ y
        have hyχ : y ∉ P χ := hy ⟨χ, hWχ, hPχ⟩
        rw [hP] at hyχ
        push Not at hyχ
        obtain ⟨w₀, hw₀, hne⟩ := hyχ
        have ha0 : a ≠ 0 := by
          rintro rfl
          rw [ha w₀ hw₀, zero_smul] at hne
          exact hne rfl
        intro w hw
        apply Submodule.mem_sup_left
        refine ⟨a⁻¹ • w, ?_⟩
        rw [map_smul, ha w hw, smul_smul, inv_mul_cancel₀ ha0, one_smul]
  refine ⟨y, fun v => ?_⟩
  have hv : v ∈ LinearMap.range (A y) ⊔ Z :=
    (hW.symm.le.trans (iSup_le hle)) Submodule.mem_top
  obtain ⟨_, ⟨u, rfl⟩, z, hz, hsum⟩ := Submodule.mem_sup.mp hv
  refine ⟨u, z, fun y' => ?_, hsum⟩
  simp only [Z, Submodule.mem_iInf, LinearMap.mem_ker] at hz
  exact hz y'

end LinearAlgebra

section Weights

variable {R : CommRingCat.{u}} {G : GroupScheme (Spec R)} [IsAffineHom G.X.hom] {d : ℕ}
  (c : FiniteCoordinates G d) {T : CommGroupScheme (Spec R)} (i : T.toGrp ⟶ G)

/-- **Weight vectors are eigenvectors of the torus Lie algebra.** If `X` lies in the weight
space of a character `χ` of `T`, then for every Lie element `Y` of `T` the adjoint differential
of `i(Y)` multiplies the coordinates of `X` by the epsilon part of `χ(Y)`. -/
theorem adjointDifferentialFamily_targetMap_of_mem_weightSpace {χ : characterLattice T}
    {X : Additive (lieKernel G R)} (hX : X ∈ weightSpace i χ) (Y : lieKernel T.toGrp R) :
    adjointDifferentialFamily c (Additive.ofMul (targetMap i R Y)) (c.equiv (.of R R) X) =
      (characterValue χ Y.val : DualNumber R).snd • c.equiv (.of R R) X := by
  have h := congrArg (c.equiv (.of R (DualNumber R))) (hX (DualNumber R) Y.val)
  change c.equiv (.of R (DualNumber R)) (adjoint G (DualNumber R) (targetMap i R Y).val
      (lieKernelMapLinear G (Algebra.ofId R (DualNumber R)) (Additive.ofMul X.toMul))) = _ at h
  rw [equiv_adjoint_constant, LinearEquiv.map_smul, ofMul_toMul,
    equiv_lieKernelMapLinear_ofId] at h
  funext j
  have hj := congrArg (fun w : Fin d → DualNumber R => (w j).snd) h
  simpa [TrivSqZeroExt.snd_mul, mul_comm] using hj

/-- The image of a Lie element of the commutative group `T` has weight zero. -/
theorem targetMap_mem_weightSpace_zero (Y : lieKernel T.toGrp R) :
    Additive.ofMul (targetMap i R Y) ∈ weightSpace i 0 := by
  intro A _ _ t
  rw [characterValue_zero, Units.val_one, one_smul]
  apply Additive.toMul.injective
  change lieKernelConjugation G (t ≫ i.hom.hom)
      (lieKernelMap G (Algebra.ofId R A) (targetMap i R Y)) =
    lieKernelMap G (Algebra.ofId R A) (targetMap i R Y)
  rw [lieKernelMap_target, ← targetMap_conjugation]
  congr 1
  apply Subtype.ext
  rw [lieKernelConjugation_val, mul_comm (constant T.toGrp t), mul_inv_cancel_right]

/-- The adjoint differentials of torus Lie elements annihilate the images of torus Lie
elements. -/
theorem adjointDifferentialFamily_targetMap_targetMap (Y Y' : lieKernel T.toGrp R) :
    adjointDifferentialFamily c (Additive.ofMul (targetMap i R Y'))
      (c.equiv (.of R R) (Additive.ofMul (targetMap i R Y))) = 0 := by
  rw [adjointDifferentialFamily_targetMap_of_mem_weightSpace c i
    (targetMap_mem_weightSpace_zero i Y) Y', characterValue_zero, Units.val_one,
    TrivSqZeroExt.snd_one, zero_smul]

end Weights

section Regular

variable {K : Type u} [Field K] {H : GroupScheme (Spec (CommRingCat.of K))}
  [IsAffineHom H.X.hom] [LocallyOfFiniteType H.X.hom] {d : ℕ} (cH : FiniteCoordinates H d)
  {S : CommGroupScheme (Spec (CommRingCat.of K))} [IsAffineHom S.toGrp.X.hom]
  (i : S.toGrp ⟶ H)

/-- The weight space of `χ`, in the finite Lie coordinates `cH` of `H`. -/
def weightCoordinates (χ : characterLattice S) : Submodule K (Fin d → K) :=
  (weightSpace i χ).map (cH.equiv (.of (CommRingCat.of K) K)).toLinearMap

/-- The Lie algebra of the torus acting on finite Lie coordinates through the adjoint
differential. -/
abbrev torusAdjointFamily :
    Additive (lieKernel S.toGrp (CommRingCat.of K)) →ₗ[K] Module.End K (Fin d → K) :=
  adjointDifferentialFamily cH ∘ₗ targetMapLinear i (CommRingCat.of K)

omit [IsAffineHom S.toGrp.X.hom] in
theorem iSup_weightCoordinates (hS : IsSplitTorus S.toGrp) :
    ⨆ χ, weightCoordinates cH i χ = ⊤ := by
  classical
  have hint := isInternal_weightSpace_of_isSplitTorus K H S hS i
  change ⨆ χ, (weightSpace i χ).map (cH.equiv (.of (CommRingCat.of K) K)).toLinearMap = ⊤
  rw [← Submodule.map_iSup, hint.submodule_iSup_eq_top, Submodule.map_top, LinearEquiv.range]

omit [IsAffineHom S.toGrp.X.hom] in
theorem finite_weightCoordinates_ne_bot (hS : IsSplitTorus S.toGrp) :
    {χ | weightCoordinates cH i χ ≠ ⊥}.Finite := by
  classical
  have hint := isInternal_weightSpace_of_isSplitTorus K H S hS i
  have hind : iSupIndep (weightCoordinates cH i) :=
    hint.submodule_iSupIndep.map_orderIso
      (Submodule.orderIsoMapComap (cH.equiv (.of (CommRingCat.of K) K)))
  exact Submodule.finite_ne_bot_of_iSupIndep hind

omit [LocallyOfFiniteType H.X.hom] in
theorem torusAdjointFamily_eigen (χ : characterLattice S)
    (y : Additive (lieKernel S.toGrp (CommRingCat.of K))) :
    ∃ a : K, ∀ w ∈ weightCoordinates cH i χ, torusAdjointFamily cH i y w = a • w := by
  refine ⟨(characterValue χ y.toMul.val : DualNumber (CommRingCat.of K)).snd, ?_⟩
  rintro _ ⟨X, hX, rfl⟩
  exact adjointDifferentialFamily_targetMap_of_mem_weightSpace cH i hX y.toMul

/-- **A regular element of the Lie algebra of a split torus.** Let `S` be a split torus over
an infinite field `K` with a homomorphism `i : S ⟶ H` to an affine algebraic group. There is a
Lie element `Y` of `S` such that every vector of `Lie(H)` (in finite coordinates) is the sum of
`ad(X)(i Y)` for some `X ∈ Lie(H)` and a vector annihilated by `ad(i Y')` for every Lie
element `Y'` of `S`. Moreover `ad(i Y')(i Y) = 0` for every such `Y'`. -/
theorem exists_regular_targetMap [Infinite K] (hS : IsSplitTorus S.toGrp) :
    ∃ Y : lieKernel S.toGrp (CommRingCat.of K),
      (∀ Y' : lieKernel S.toGrp (CommRingCat.of K),
        adjointDifferentialFamily cH (Additive.ofMul (targetMap i _ Y'))
          (cH.equiv (.of (CommRingCat.of K) K) (Additive.ofMul (targetMap i _ Y))) = 0) ∧
      ∀ v : Fin d → K, ∃ (X : lieKernel H (CommRingCat.of K)) (z : Fin d → K),
        (∀ Y' : lieKernel S.toGrp (CommRingCat.of K),
          adjointDifferentialFamily cH (Additive.ofMul (targetMap i _ Y')) z = 0) ∧
        adjointDifferentialFamily cH (Additive.ofMul X)
          (cH.equiv (.of (CommRingCat.of K) K) (Additive.ofMul (targetMap i _ Y))) + z = v := by
  obtain ⟨y, hy⟩ := exists_range_add_commonKernel (torusAdjointFamily cH i)
    (weightCoordinates cH i) (iSup_weightCoordinates cH i hS)
    (finite_weightCoordinates_ne_bot cH i hS) (torusAdjointFamily_eigen cH i)
  refine ⟨y.toMul, fun Y' => adjointDifferentialFamily_targetMap_targetMap cH i y.toMul Y',
    fun v => ?_⟩
  obtain ⟨u, z, hz, huz⟩ := hy v
  refine ⟨((cH.equiv (.of (CommRingCat.of K) K)).symm (-u)).toMul, z,
    fun Y' => hz (Additive.ofMul Y'), ?_⟩
  rw [← huz, adjointDifferentialFamily_antisymm cH, ofMul_toMul, LinearEquiv.apply_symm_apply,
    map_neg, neg_neg]
  rfl

end Regular

end Langlands.GroupScheme.Lie
