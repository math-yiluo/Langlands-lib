import Langlands.GroupScheme.Derived.CentralIntersection.Unipotence
import Langlands.GroupScheme.Absolute.LieKolchinRationalTriangularization

/-! # Unipotence from unipotent rational points of a solvable group

A smooth connected affine group scheme over an algebraically closed field, whose rational
points form a solvable group and act by unipotent matrices in a closed embedding into `GL_N`,
is unipotent. -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Matrix commutatorElement

namespace Langlands.GroupScheme.RadicalFieldExtension

open CentralIntersection RationalZariski MatrixRepresentation

variable {K : Type u} [Field K] [IsAlgClosed K] {H : GroupScheme (Spec (CommRingCat.of K))}

omit [IsAlgClosed K] in
/-- Linear conditions on the linear maps of the rational points of a representation, with an
arbitrary finite coordinate index, define closed sets of rational points. -/
theorem isClosed_toLin'_linear {n : Type} [Fintype n] [DecidableEq n]
    (σ : MatrixRepresentation H n) (Λ : Module.End K (n → K) →ₗ[K] K) (c : K) :
    @IsClosed _ (topology H)
      {x | Λ (Matrix.toLin' (σ.rationalMatrix x : Matrix n n K)) = c} := by
  let Λ' : Matrix n n K →ₗ[K] K :=
    Λ ∘ₗ (Matrix.toLin' : Matrix n n K ≃ₗ[K] Module.End K (n → K)).toLinearMap
  let s : n → n → Γ(H.X.left, ⊤) := fun i j =>
    σ.hom.hom.left.appTop (GeneralLinear.entrySection n _ i j)
  let t : Γ(H.X.left, ⊤) :=
    ∑ i, ∑ j, s i j * const H (Λ' (Matrix.single i j 1)) - const H c
  have hset : {x | Λ (Matrix.toLin' (σ.rationalMatrix x : Matrix n n K)) = c} =
      {x | evaluation H x t = 0} := by
    ext x
    simp only [Set.mem_ofPred_eq]
    have hΛ : Λ (Matrix.toLin' (σ.rationalMatrix x : Matrix n n K)) =
        ∑ i, ∑ j, (σ.rationalMatrix x : Matrix n n K) i j * Λ' (Matrix.single i j 1) := by
      change Λ' (σ.rationalMatrix x : Matrix n n K) = _
      conv_lhs => rw [Matrix.matrix_eq_sum_single (σ.rationalMatrix x : Matrix n n K)]
      simp only [map_sum]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      rw [← smul_eq_mul, ← map_smul, Matrix.smul_single, smul_eq_mul, mul_one]
    have hentry : ∀ i j, evaluation H x (s i j) = (σ.rationalMatrix x : Matrix n n K) i j := by
      intro i j
      rw [rationalMatrix_apply_apply]
      rfl
    have hev : evaluation H x t = Λ (Matrix.toLin' (σ.rationalMatrix x : Matrix n n K)) - c := by
      simp only [t, map_sub, map_sum, map_mul, evaluation_const, hentry, hΛ]
    rw [hev, sub_eq_zero]
  rw [hset]
  exact isClosed_evaluation_eq_zero t

/-- **Unipotence criterion.** Let `H` be a smooth connected affine group scheme over an
algebraically closed field whose rational points form a solvable group. If `ρ` is a closed
embedding into `GL_N` and every rational point acts by a unipotent matrix in `ρ`, then `H` is
unipotent. -/
theorem isUnipotent_of_isNilpotent_rationalMatrix [Smooth H.X.hom] [IsAffineHom H.X.hom]
    [ConnectedSpace H.X.left] {N : Type} [Fintype N] [DecidableEq N]
    (ρ : MatrixRepresentation H N) [IsClosedImmersion ρ.hom.hom.left]
    (hsolv : Group.IsSolvable (Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ H.X))
    (hunip : ∀ h : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ H.X,
      IsNilpotent ((ρ.rationalMatrix h : Matrix N N K) - 1)) :
    IsUnipotent H := by
  have : IsAffine H.X.left := isAffine_of_isAffineHom H.X.hom
  have : IsReduced H.X.left :=
    Langlands.AlgebraicGeometry.SmoothReducedProof.isReduced_of_smooth_over_field
      K H.X.left H.X.hom
  -- Every rational point acts unipotently in every representation.
  have hnil : ∀ (n : Type) [Fintype n] [DecidableEq n] (σ : MatrixRepresentation H n)
      (h : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ H.X),
      IsNilpotent ((σ.rationalMatrix h : Matrix n n K) - 1) := by
    intro n _ _ σ h
    have hρ : ∀ h' : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ H.X,
        IsNilpotent ((GroupScheme.scalarMap H.X).mapMatrix
          (ρ.rationalMatrix h' : Matrix N N K) - 1) := by
      intro h'
      have := (hunip h').map (GroupScheme.scalarMap H.X).mapMatrix
      rwa [map_sub, map_one] at this
    have hL : ∀ f, f ∈ locallyUnipotent (translationMap h) :=
      mem_of_isClosedImmersion ρ (locallyUnipotent (translationMap h))
        (fun c => mem_locallyUnipotent_of_fixed _ (translationMap_scalarMap h c))
        (mem_locallyUnipotent_of_mapMatrix_eq_mul _ _ _ (translationMap_mapMatrix_scalarMap h _)
          (translationMap_mapMatrix_pointMatrix ρ h) (hρ h))
        (mem_locallyUnipotent_of_mapMatrix_eq_mul_left _ _ _
          (translationMap_mapMatrix_scalarMap h _)
          (translationMap_mapMatrix_pointMatrix_inv ρ h) (hρ h⁻¹))
    have hB := isNilpotent_sub_one_of_mapMatrix_eq_mul (translationMap h) _ _
      (σ.pointMatrix H.X (𝟙 H.X)).isUnit (translationMap_mapMatrix_scalarMap h _)
      (translationMap_mapMatrix_pointMatrix σ h) (fun _ _ => hL _)
    have := hB.map
      (CentralIntersection.evalPoint (1 : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ H.X)).mapMatrix
    rwa [map_sub, map_one, CentralIntersection.evalPoint_mapMatrix_scalarMap] at this
  -- Lie–Kolchin on the topological group of rational points gives a common eigenvector.
  let _ := topology H
  have : PreconnectedSpace (Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ H.X) :=
    preconnectedSpace (H := H)
  have hmul : ∀ a : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ H.X,
      Continuous fun x => a * x := by
    intro a
    obtain ⟨φ, hφ⟩ := exists_comp_eq_mul_left a
    have : (fun x => a * x) = fun y => y ≫ φ := funext fun y => (hφ y).symm
    rw [this]
    exact continuous_comp φ
  have hinv : Continuous fun x : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ H.X => x⁻¹ := by
    have : (fun x : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ H.X => x⁻¹) =
        fun y => y ≫ (𝟙 H.X)⁻¹ := by
      funext y
      rw [GrpObj.comp_inv, Category.comp_id]
    rw [this]
    exact continuous_comp _
  have hcomm : ∀ a : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ H.X,
      Continuous fun x : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ H.X => ⁅a, x⁆ := by
    intro a
    obtain ⟨φ, hφ⟩ := exists_comp_eq_commutator_left a
    have : (fun x : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ H.X => ⁅a, x⁆) =
        fun y => y ≫ φ :=
      funext fun y => (hφ y).symm
    rw [this]
    exact continuous_comp φ
  intro n _ _ _ σ
  let r : (Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ H.X) →* Module.End K (n → K) :=
    (Matrix.toLinAlgEquiv' : Matrix n n K ≃ₐ[K] Module.End K (n → K)).toMonoidHom.comp
      ((Units.coeHom _).comp σ.rationalMatrix)
  obtain ⟨v, hv0, hv⟩ := Langlands.LieKolchin.exists_common_eigenvector_of_isSolvable
    hmul hinv hcomm r (fun Λ c => isClosed_toLin'_linear σ Λ c)
  -- The eigenvalues are `1` by unipotence, so `v` is fixed by every rational point.
  have hfix : ∀ h : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ H.X,
      (σ.rationalMatrix h : Matrix n n K) *ᵥ v = v := by
    intro h
    obtain ⟨c, hc⟩ := hv h
    have hc' : (σ.rationalMatrix h : Matrix n n K) *ᵥ v = c • v := hc
    obtain ⟨m, hm⟩ := hnil n σ h
    have hA : ((σ.rationalMatrix h : Matrix n n K) - 1) *ᵥ v = (c - 1) • v := by
      rw [Matrix.sub_mulVec, Matrix.one_mulVec, hc', sub_smul, one_smul]
    have hpow : ∀ l : ℕ,
        ((σ.rationalMatrix h : Matrix n n K) - 1) ^ l *ᵥ v = (c - 1) ^ l • v := by
      intro l
      induction l with
      | zero => simp
      | succ l ih =>
        rw [pow_succ, ← Matrix.mulVec_mulVec, hA, Matrix.mulVec_smul, ih, smul_smul, ← pow_succ']
    have h0 : (c - 1) ^ m • v = 0 := by
      rw [← hpow, hm, Matrix.zero_mulVec]
    have hc1 : c = 1 := by
      rcases smul_eq_zero.1 h0 with h | h
      · exact sub_eq_zero.1 (IsNilpotent.eq_zero ⟨m, h⟩)
      · exact absurd h hv0
    rw [hc', hc1, one_smul]
  refine ⟨v, hv0, (σ.isFixedVector_iff_universal v).2 ?_⟩
  funext i
  rw [← sub_eq_zero]
  refine eq_zero_of_forall_evalPoint_eq_zero _ fun h => ?_
  have hv' : (CentralIntersection.evalPoint h ∘ fun j => GroupScheme.scalarMap H.X (v j)) = v :=
    funext fun j => CentralIntersection.evalPoint_scalarMap h (v j)
  rw [map_sub, RingHom.map_mulVec, CentralIntersection.evalPoint_mapMatrix_pointMatrix, hv', hfix,
    CentralIntersection.evalPoint_scalarMap, sub_self]

end Langlands.GroupScheme.RadicalFieldExtension
