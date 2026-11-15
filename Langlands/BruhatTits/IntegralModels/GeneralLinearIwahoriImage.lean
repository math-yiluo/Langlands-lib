import Langlands.BruhatTits.IntegralModels.GeneralLinearIwahoriKernel
import Langlands.BruhatTits.IntegralModels.SpecialFibre
import Langlands.BruhatTits.IntegralModels.ReductionPreimage
import Langlands.GroupScheme.IntegralModel.UnramifiedSpecialFibreImage
import Langlands.GroupScheme.SchematicImageComparison
import Langlands.GroupScheme.Absolute.DynamicParabolicRecognition
import Langlands.GroupScheme.Absolute.GeneralLinearBorelProof
import Langlands.GroupScheme.Absolute.BorelTransport
import Langlands.GroupScheme.Rational.ParabolicAmbientTransport
import Langlands.BruhatTits.IntegralModels.DepthZeroInduction

/-! # The special-fibre image from the Iwahori model to the hyperspecial model of `GL_N`

The special-fibre map of the homomorphism from the Iwahori model of `GL_N` to the hyperspecial
model `GL_N(𝒪[F])` has image the upper triangular Borel subgroup, and the reduction preimage of
its rational points is the Iwahori subgroup. See the paired Markdown file.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped TensorProduct ValuativeRel CategoryTheory.MonObj

namespace Langlands.BruhatTits.IntegralModels

open GroupScheme GroupScheme.FiniteFreeAlgebraUnits

variable (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] (N : ℕ)

/-! ### An algebra section of the upper triangular reduction -/

theorem kernelBasis_inl_equivFin (p : UpperPosition N) :
    kernelBasis F N (Sum.inl (Fintype.equivFin (UpperPosition N) p)) =
      1 ⊗ₜ iwahoriUnit F N p.1 := by
  rw [kernelBasis_apply, upperLowerEquiv_symm_inl, Equiv.symm_apply_apply]

theorem iwahoriUnit_mul_upper (p q : UpperPosition N) :
    iwahoriUnit F N p.1 * iwahoriUnit F N q.1 =
      if p.1.2 = q.1.1 then iwahoriUnit F N (p.1.1, q.1.2) else 0 := by
  apply Subtype.ext
  rw [iwahoriUnit_mul_coe]
  split_ifs with h
  · rw [iwahoriUnit_coe]
    simp only [unitScale, not_lt.mpr p.2, not_lt.mpr q.2, not_lt.mpr (p.2.trans (h.le.trans q.2)),
      ↓reduceIte, mul_one]
  · rfl

/-- The linear section of the upper triangular reduction: the matrix unit at a position on or
above the diagonal goes to the corresponding matrix unit of `𝓀[F] ⊗ Λ`. -/
def upperSectionLinear :
    upperTriangular F N →ₗ[CommRingCat.of 𝓀[F]] SpecialAlgebra F N :=
  (upperBasis F N).constr (CommRingCat.of 𝓀[F]) (fun i => kernelBasis F N (Sum.inl i))

theorem upperSectionLinear_upperBasis (i : Fin (upperCount N)) :
    upperSectionLinear F N (upperBasis F N i) = kernelBasis F N (Sum.inl i) :=
  (upperBasis F N).constr_basis _ _ _

theorem specialUpper_upperSectionLinear (x : upperTriangular F N) :
    specialUpper F N (upperSectionLinear F N x) = x := by
  have h : (specialUpper F N).toLinearMap ∘ₗ upperSectionLinear F N = LinearMap.id := by
    apply (upperBasis F N).ext
    intro i
    rw [LinearMap.comp_apply, upperSectionLinear_upperBasis, AlgHom.toLinearMap_apply,
      specialUpper_kernelBasis_inl, LinearMap.id_apply]
  exact LinearMap.congr_fun h x

theorem kernelBasis_inl_mul_mem (i j : Fin (upperCount N)) :
    kernelBasis F N (Sum.inl i) * kernelBasis F N (Sum.inl j) ∈
      LinearMap.range (upperSectionLinear F N) := by
  rw [kernelBasis_apply, kernelBasis_apply, upperLowerEquiv_symm_inl, upperLowerEquiv_symm_inl,
    Algebra.TensorProduct.tmul_mul_tmul, mul_one,
    iwahoriUnit_mul_upper F N ((Fintype.equivFin (UpperPosition N)).symm i)
      ((Fintype.equivFin (UpperPosition N)).symm j)]
  split_ifs with h
  · let r : UpperPosition N := ⟨(((Fintype.equivFin (UpperPosition N)).symm i).1.1,
      ((Fintype.equivFin (UpperPosition N)).symm j).1.2),
      ((Fintype.equivFin (UpperPosition N)).symm i).2.trans
        (h.le.trans ((Fintype.equivFin (UpperPosition N)).symm j).2)⟩
    rw [show iwahoriUnit F N (((Fintype.equivFin (UpperPosition N)).symm i).1.1,
        ((Fintype.equivFin (UpperPosition N)).symm j).1.2) = iwahoriUnit F N r.1 from rfl,
      ← kernelBasis_inl_equivFin F N r, ← upperSectionLinear_upperBasis]
    exact LinearMap.mem_range_self _ _
  · rw [TensorProduct.tmul_zero]
    exact zero_mem _

theorem upperSectionLinear_mul_mem (x y : upperTriangular F N) :
    upperSectionLinear F N x * upperSectionLinear F N y ∈
      LinearMap.range (upperSectionLinear F N) := by
  rw [← (upperBasis F N).sum_repr x, ← (upperBasis F N).sum_repr y, map_sum, map_sum,
    Finset.sum_mul]
  refine Submodule.sum_mem _ fun i _ => ?_
  rw [Finset.mul_sum]
  refine Submodule.sum_mem _ fun j _ => ?_
  rw [map_smul, map_smul, smul_mul_smul_comm, upperSectionLinear_upperBasis,
    upperSectionLinear_upperBasis]
  exact Submodule.smul_mem _ _ (kernelBasis_inl_mul_mem F N i j)

theorem one_mem_range_upperSectionLinear :
    (1 : SpecialAlgebra F N) ∈ LinearMap.range (upperSectionLinear F N) := by
  rw [Algebra.TensorProduct.one_def, ← sum_iwahoriUnit_diag, TensorProduct.tmul_sum]
  refine Submodule.sum_mem _ fun i _ => ?_
  rw [show iwahoriUnit F N (i, i) = iwahoriUnit F N (⟨(i, i), le_rfl⟩ : UpperPosition N).1 from rfl,
    ← kernelBasis_inl_equivFin, ← upperSectionLinear_upperBasis]
  exact LinearMap.mem_range_self _ _

theorem upperSectionLinear_specialUpper_of_mem {z : SpecialAlgebra F N}
    (hz : z ∈ LinearMap.range (upperSectionLinear F N)) :
    upperSectionLinear F N (specialUpper F N z) = z := by
  obtain ⟨y, rfl⟩ := hz
  rw [specialUpper_upperSectionLinear]

/-- The algebra section of the upper triangular reduction `𝓀[F] ⊗ Λ → B(𝓀[F])`. -/
def upperSection : upperTriangular F N →ₐ[CommRingCat.of 𝓀[F]] SpecialAlgebra F N :=
  AlgHom.ofLinearMap (upperSectionLinear F N)
    (by
      have h := upperSectionLinear_specialUpper_of_mem F N (one_mem_range_upperSectionLinear F N)
      rwa [map_one] at h)
    (fun x y => by
      have h := upperSectionLinear_specialUpper_of_mem F N (upperSectionLinear_mul_mem F N x y)
      rwa [map_mul, specialUpper_upperSectionLinear, specialUpper_upperSectionLinear] at h)

theorem specialUpper_comp_upperSection :
    (specialUpper F N).comp (upperSection F N) = AlgHom.id _ _ :=
  AlgHom.ext (specialUpper_upperSectionLinear F N)

/-! ### The unit group of the upper triangular matrices -/

/-- The unit group of the upper triangular matrices over the residue field. -/
abbrev upperUnits : GroupScheme (Spec (CommRingCat.of 𝓀[F])) :=
  FiniteFreeAlgebraUnits.groupScheme (upperBasis F N)

/-- The unit map of the upper triangular reduction `𝓀[F] ⊗ Λ → B(𝓀[F])`. -/
abbrev upperUnitMap :
    FiniteFreeAlgebraUnits.groupScheme (UnipotentPart.flatBasis (kernelBasis F N)) ⟶
      upperUnits F N :=
  UnipotentPart.unitMap (specialUpper F N) (kernelBasis F N) (upperBasis F N)

/-- The unit map of the algebra section. -/
def upperSectionMap :
    upperUnits F N ⟶ FiniteFreeAlgebraUnits.groupScheme (UnipotentPart.flatBasis (kernelBasis F N)) :=
  map (upperBasis F N) (UnipotentPart.flatBasis (kernelBasis F N)) (upperSection F N)

@[reassoc]
theorem upperSectionMap_comp_upperUnitMap : upperSectionMap F N ≫ upperUnitMap F N = 𝟙 _ := by
  change map _ _ _ ≫ map _ _ _ = _
  rw [map_comp, specialUpper_comp_upperSection, map_id]

/-- The unit map of the upper triangular reduction has a section, so it is schematically
dominant. -/
theorem upperUnitMap_dominant :
    IsSchemeTheoreticallyDominant (upperUnitMap F N).hom.hom.left := by
  have h : (upperSectionMap F N).hom.hom.left ≫ (upperUnitMap F N).hom.hom.left = 𝟙 _ := by
    rw [← Over.comp_left, ← Grp.comp_hom_hom, upperSectionMap_comp_upperUnitMap]
    rfl
  rw [isSchemeTheoreticallyDominant_iff]
  refine le_bot_iff.mp ((Scheme.Hom.le_ker_comp (upperSectionMap F N).hom.hom.left
    (upperUnitMap F N).hom.hom.left).trans ?_)
  rw [h]
  exact (Scheme.Hom.ker_eq_bot (𝟙 _)).le

/-! ### The upper triangular Borel subgroup of `GL_N` over the residue field -/

/-- The weights `-i`. They strictly decrease, so their block parabolic subgroup of `GL_N` is the
upper triangular Borel subgroup. -/
def upperWeight (i : Fin N) : ℤ := -((i : ℕ) : ℤ)

theorem upperWeight_strictAnti : StrictAnti (upperWeight N) :=
  fun _ _ hij => neg_lt_neg (Nat.cast_lt.mpr hij)

theorem upperWeight_lt_iff {i j : Fin N} : upperWeight N i < upperWeight N j ↔ j < i :=
  (upperWeight_strictAnti N).lt_iff_gt

section UpperMatrix

variable (S : Type u) [CommRing S] [Algebra (CommRingCat.of 𝓀[F]) S]

/-- The matrix over `S` of an element of `S ⊗ B(𝓀[F])`. -/
def upperMatrix :
    S ⊗[CommRingCat.of 𝓀[F]] upperTriangular F N →ₐ[CommRingCat.of 𝓀[F]]
      Matrix (Fin N) (Fin N) S :=
  (matrixEquivTensor (Fin N) (CommRingCat.of 𝓀[F]) S).symm.toAlgHom.comp
    (Algebra.TensorProduct.map (AlgHom.id (CommRingCat.of 𝓀[F]) S)
      ((upperTriangular F N).val : upperTriangular F N →ₐ[CommRingCat.of 𝓀[F]]
        Matrix (Fin N) (Fin N) (CommRingCat.of 𝓀[F])))

theorem upperMatrix_tmul (s : S) (M : upperTriangular F N) :
    upperMatrix F N S (s ⊗ₜ M) =
      s • (M : Matrix (Fin N) (Fin N) (CommRingCat.of 𝓀[F])).map
        (algebraMap (CommRingCat.of 𝓀[F]) S) :=
  rfl

theorem upperMatrix_apply_of_lt (w : S ⊗[CommRingCat.of 𝓀[F]] upperTriangular F N)
    {i j : Fin N} (hij : j < i) : upperMatrix F N S w i j = 0 := by
  induction w using TensorProduct.inductionOn with
  | tmul s M =>
    rw [upperMatrix_tmul, Matrix.smul_apply, Matrix.map_apply,
      show (M : Matrix (Fin N) (Fin N) (CommRingCat.of 𝓀[F])) i j = 0 from M.2 hij, map_zero,
      smul_zero]
  | add w w' hw hw' => rw [map_add, Matrix.add_apply, hw, hw', add_zero]

/-- The matrix unit at a position on or above the diagonal, as an upper triangular matrix. -/
def upperUnitMatrix (p : UpperPosition N) : upperTriangular F N :=
  ⟨Matrix.single p.1.1 p.1.2 1, Matrix.blockTriangular_single p.2 1⟩

theorem upperUnitMatrix_val (p : UpperPosition N) :
    (upperUnitMatrix F N p : Matrix (Fin N) (Fin N) (CommRingCat.of 𝓀[F])) =
      Matrix.single p.1.1 p.1.2 1 :=
  rfl

theorem upperMatrix_tmul_upperUnitMatrix_apply (s : S) (p : UpperPosition N) (i j : Fin N) :
    upperMatrix F N S (s ⊗ₜ upperUnitMatrix F N p) i j =
      if p.1.1 = i ∧ p.1.2 = j then s else 0 := by
  rw [upperMatrix_tmul, Matrix.smul_apply, Matrix.map_apply, upperUnitMatrix_val,
    Matrix.single_apply]
  split_ifs <;> simp

/-- Every upper triangular matrix over `S` comes from `S ⊗ B(𝓀[F])`. -/
theorem upperMatrix_sum (g : Matrix (Fin N) (Fin N) S) (hg : ∀ i j, j < i → g i j = 0) :
    upperMatrix F N S (∑ p : UpperPosition N, g p.1.1 p.1.2 ⊗ₜ upperUnitMatrix F N p) = g := by
  ext i j
  rw [map_sum, Matrix.sum_apply]
  rw [Finset.sum_congr rfl fun p _ => upperMatrix_tmul_upperUnitMatrix_apply F N S _ p i j]
  by_cases h : i ≤ j
  · rw [Fintype.sum_eq_single ⟨(i, j), h⟩]
    · simp
    · intro p hp
      have hne : ¬ (p.1.1 = i ∧ p.1.2 = j) := fun h' => hp (Subtype.ext (Prod.ext h'.1 h'.2))
      simp only [hne, ↓reduceIte]
  · rw [hg i j (not_le.mp h)]
    refine Finset.sum_eq_zero fun p _ => ?_
    have hne : ¬ (p.1.1 = i ∧ p.1.2 = j) := fun h' => h (h'.1 ▸ h'.2 ▸ p.2)
    simp only [hne, ↓reduceIte]

end UpperMatrix

theorem upperPart_val (M : upperTriangular F N) :
    upperPart F N (M : Matrix (Fin N) (Fin N) 𝓀[F]) = M := by
  apply Subtype.ext
  ext i j
  change (if i ≤ j then M.1 i j else 0) = M.1 i j
  split_ifs with h
  · rfl
  · exact (M.2 (not_le.mp h)).symm

theorem upperMatrix_injective (S : Type u) [CommRing S] [Algebra (CommRingCat.of 𝓀[F]) S] :
    Function.Injective (upperMatrix F N S) := by
  intro w w' h
  have hret : ∀ w : S ⊗[CommRingCat.of 𝓀[F]] upperTriangular F N,
      LinearMap.lTensor S (upperPart F N) (Algebra.TensorProduct.map
        (AlgHom.id (CommRingCat.of 𝓀[F]) S) ((upperTriangular F N).val :
          upperTriangular F N →ₐ[CommRingCat.of 𝓀[F]]
            Matrix (Fin N) (Fin N) (CommRingCat.of 𝓀[F])) w) = w := by
    intro w
    induction w using TensorProduct.inductionOn with
    | tmul s a =>
      simp only [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, LinearMap.lTensor_tmul]
      exact congrArg (s ⊗ₜ[CommRingCat.of 𝓀[F]] ·) (upperPart_val F N a)
    | add w w' hw hw' => rw [map_add, map_add, hw, hw']
  rw [← hret w, ← hret w']
  exact congrArg _ ((matrixEquivTensor (Fin N) (CommRingCat.of 𝓀[F]) S).symm.injective h)

/-- The inclusion of the upper triangular units into `GL_N` over the residue field. -/
def upperGLMap :
    upperUnits F N ⟶ GeneralLinear.groupScheme (Fin N) (CommRingCat.of 𝓀[F]) :=
  map (upperBasis F N) (matrixBasis (CommRingCat.of 𝓀[F]) N)
      ((upperTriangular F N).val : upperTriangular F N →ₐ[CommRingCat.of 𝓀[F]]
        Matrix (Fin N) (Fin N) (CommRingCat.of 𝓀[F])) ≫
    (generalLinearIso (CommRingCat.of 𝓀[F]) N).hom

theorem upperGLMap_points (T : Over (Spec (CommRingCat.of 𝓀[F])))
    (x : T ⟶ (upperUnits F N).X) :
    (GeneralLinear.pointsEquiv (Fin N) (CommRingCat.of 𝓀[F]) T
        (x ≫ (upperGLMap F N).hom.hom)).val =
      upperMatrix F N ((algΓ (CommRingCat.of 𝓀[F])).obj T).unop
        (pointsEquiv (upperBasis F N) T x).val := by
  have e : x ≫ (upperGLMap F N).hom.hom =
      (x ≫ (map (upperBasis F N) (matrixBasis (CommRingCat.of 𝓀[F]) N)
        ((upperTriangular F N).val : upperTriangular F N →ₐ[CommRingCat.of 𝓀[F]]
          Matrix (Fin N) (Fin N) (CommRingCat.of 𝓀[F]))).hom.hom) ≫
        (generalLinearIso (CommRingCat.of 𝓀[F]) N).hom.hom.hom := by
    rw [Category.assoc]
    rfl
  have h2 := congrArg Units.val (pointsEquiv_map (upperBasis F N)
    (matrixBasis (CommRingCat.of 𝓀[F]) N)
    ((upperTriangular F N).val : upperTriangular F N →ₐ[CommRingCat.of 𝓀[F]]
      Matrix (Fin N) (Fin N) (CommRingCat.of 𝓀[F])) T x)
  rw [e, generalLinearIso_hom_points (CommRingCat.of 𝓀[F]) N T]
  change (matrixEquivTensor (Fin N) (CommRingCat.of 𝓀[F])
      ((algΓ (CommRingCat.of 𝓀[F])).obj T).unop).symm
    (pointsEquiv (matrixBasis (CommRingCat.of 𝓀[F]) N) T _).val = _
  rw [h2]
  rfl

theorem range_upperGLMap :
    SubgroupFunctor.range (upperGLMap F N) =
      GeneralLinear.blockParabolic (Fin N) (CommRingCat.of 𝓀[F]) (upperWeight N) := by
  ext T x
  rw [SubgroupFunctor.mem_range, GeneralLinear.mem_blockParabolic]
  constructor
  · rintro ⟨y, rfl⟩ i j hij
    have h := upperMatrix_apply_of_lt F N ((algΓ (CommRingCat.of 𝓀[F])).obj T).unop
      (pointsEquiv (upperBasis F N) T y).val ((upperWeight_lt_iff N).mp hij)
    rw [← upperGLMap_points] at h
    exact h
  · intro hx
    set g := GeneralLinear.pointsEquiv (Fin N) (CommRingCat.of 𝓀[F]) T x with hgdef
    have hmem : g ∈ GeneralLinear.blockParabolicSubgroup Γ(T.left, ⊤) (upperWeight N) := hx
    have hg : ∀ i j, j < i → g.val i j = 0 :=
      fun i j h => hx i j ((upperWeight_lt_iff N).mpr h)
    have hg' : ∀ i j, j < i → g⁻¹.val i j = 0 :=
      fun i j h => (GeneralLinear.mem_blockParabolicSubgroup _ _).1 (inv_mem hmem) i j
        ((upperWeight_lt_iff N).mpr h)
    let w : ((algΓ (CommRingCat.of 𝓀[F])).obj T).unop ⊗[CommRingCat.of 𝓀[F]]
        upperTriangular F N :=
      ∑ p : UpperPosition N, g.val p.1.1 p.1.2 ⊗ₜ upperUnitMatrix F N p
    let w' : ((algΓ (CommRingCat.of 𝓀[F])).obj T).unop ⊗[CommRingCat.of 𝓀[F]]
        upperTriangular F N :=
      ∑ p : UpperPosition N, g⁻¹.val p.1.1 p.1.2 ⊗ₜ upperUnitMatrix F N p
    have hw : upperMatrix F N ((algΓ (CommRingCat.of 𝓀[F])).obj T).unop w = g.val :=
      upperMatrix_sum F N ((algΓ (CommRingCat.of 𝓀[F])).obj T).unop g.val hg
    have hw' : upperMatrix F N ((algΓ (CommRingCat.of 𝓀[F])).obj T).unop w' = g⁻¹.val :=
      upperMatrix_sum F N ((algΓ (CommRingCat.of 𝓀[F])).obj T).unop g⁻¹.val hg'
    have h1 : w * w' = 1 := upperMatrix_injective F N _ (by
      rw [map_mul, hw, hw', map_one]
      exact congrArg Units.val (mul_inv_cancel g))
    have h2 : w' * w = 1 := upperMatrix_injective F N _ (by
      rw [map_mul, hw, hw', map_one]
      exact congrArg Units.val (inv_mul_cancel g))
    refine ⟨(pointsEquiv (upperBasis F N) T).symm ⟨w, w', h1, h2⟩, ?_⟩
    apply (GeneralLinear.pointsEquiv (Fin N) (CommRingCat.of 𝓀[F]) T).injective
    apply Units.ext
    rw [upperGLMap_points, MulEquiv.apply_symm_apply]
    exact hw

theorem mono_upperGLMap : Mono (upperGLMap F N).hom.hom := by
  have := mono_map (upperBasis F N) (matrixBasis (CommRingCat.of 𝓀[F]) N)
    ((upperTriangular F N).val : upperTriangular F N →ₐ[CommRingCat.of 𝓀[F]]
      Matrix (Fin N) (Fin N) (CommRingCat.of 𝓀[F])) (upperPart F N) (upperPart_val F N)
  rw [upperGLMap, Grp.comp_hom_hom]
  infer_instance

theorem isRepresentedBy_upperGLMap :
    (GeneralLinear.blockParabolic (Fin N) (CommRingCat.of 𝓀[F]) (upperWeight N)).IsRepresentedBy
      (upperGLMap F N) :=
  ⟨mono_upperGLMap F N, range_upperGLMap F N⟩

/-- The upper triangular units are the block parabolic subgroup scheme of `GL_N` for the
weights `-i`. -/
def upperBorelIso :
    upperUnits F N ≅
      GeneralLinear.blockParabolicScheme (Fin N) (CommRingCat.of 𝓀[F]) (upperWeight N) :=
  SubgroupFunctor.IsRepresentedBy.isoOfIsRepresentedBy (isRepresentedBy_upperGLMap F N)
    (GeneralLinear.isRepresentedBy_blockParabolic (Fin N) _ (upperWeight N))

theorem upperBorelIso_hom_comp :
    (upperBorelIso F N).hom ≫
        GeneralLinear.blockParabolicHom (Fin N) (CommRingCat.of 𝓀[F]) (upperWeight N) =
      upperGLMap F N :=
  SubgroupFunctor.IsRepresentedBy.isoOfIsRepresentedBy_hom_comp _ _

theorem isClosedSubgroup_upperGLMap : IsClosedSubgroup (upperGLMap F N) := by
  rw [← upperBorelIso_hom_comp]
  exact IsClosedSubgroup.iso_comp _ (GeneralLinear.isClosedSubgroup_blockParabolicHom _ _ _)

theorem isParabolicSubgroup_upperGLMap : IsParabolicSubgroup (upperGLMap F N) :=
  isParabolicSubgroup_of_range_eq_dynamicParabolic
    (isConnectedReductive_generalLinear 𝓀[F] (Fin N)) _ (isClosedSubgroup_upperGLMap F N)
    (GeneralLinear.diagonalCocharacter (Fin N) (CommRingCat.of 𝓀[F]) (upperWeight N))
    ((range_upperGLMap F N).trans
      (GeneralLinear.parabolic_diagonalCocharacter (Fin N) (CommRingCat.of 𝓀[F])
        (upperWeight N)).symm)

theorem isBorelSubgroup_upperGLMap : IsBorelSubgroup (upperGLMap F N) := by
  rw [← upperBorelIso_hom_comp]
  exact (GeneralLinear.UpperTriangular.isBorelSubgroup_blockParabolicHom 𝓀[F]
    (upperWeight_strictAnti N)).iso_comp _

/-! ### The special-fibre image -/

/-- The unit map of the inclusion of the upper triangular matrices into `𝓀[F] ⊗ M_N(𝒪[F])`. -/
abbrev upperFibreInclusion :
    upperUnits F N ⟶ FiniteFreeAlgebraUnits.groupScheme (specialMatrixBasis F N) :=
  map (upperBasis F N) (specialMatrixBasis F N) (upperInclusion F N)

/-- The unit group of `𝓀[F] ⊗ M_N(𝒪[F])` is `GL_N` over the residue field. -/
def glFibreIso :
    FiniteFreeAlgebraUnits.groupScheme (specialMatrixBasis F N) ≅
      GeneralLinear.groupScheme (Fin N) (CommRingCat.of 𝓀[F]) :=
  congrIso (specialMatrixBasis F N) (matrixBasis (CommRingCat.of 𝓀[F]) N)
      (specialMatrixEquiv F N) ≪≫
    generalLinearIso (CommRingCat.of 𝓀[F]) N

theorem specialMatrixEquiv_comp_upperInclusion :
    (specialMatrixEquiv F N).toAlgHom.comp (upperInclusion F N) =
      ((upperTriangular F N).val : upperTriangular F N →ₐ[CommRingCat.of 𝓀[F]]
        Matrix (Fin N) (Fin N) (CommRingCat.of 𝓀[F])) := by
  apply AlgHom.ext
  intro M
  change specialMatrixEquiv F N ((specialMatrixEquiv F N).symm M.1) = M.1
  exact AlgEquiv.apply_symm_apply _ _

theorem upperFibreInclusion_comp_glFibreIso :
    upperFibreInclusion F N ≫ (glFibreIso F N).hom = upperGLMap F N := by
  rw [glFibreIso, Iso.trans_hom, congrIso_hom_eq_map, ← Category.assoc, map_comp,
    specialMatrixEquiv_comp_upperInclusion, upperGLMap]

theorem isClosedSubgroup_upperFibreInclusion : IsClosedSubgroup (upperFibreInclusion F N) := by
  rw [← IsClosedSubgroup.comp_iso_iff _ (glFibreIso F N), upperFibreInclusion_comp_glFibreIso]
  exact isClosedSubgroup_upperGLMap F N

section Image

local instance integralModel_specialFibre_affine {G : GroupScheme (Spec (CommRingCat.of F))}
    (M : IntegralModel 𝒪[F] F G) : IsAffineHom M.specialFibre.X.hom := by
  change IsAffineHom (CategoryTheory.Limits.pullback.snd M.group.X.hom
    (IntegralModel.residueBaseMap 𝒪[F]))
  infer_instance

local instance kernelUnits_affine :
    IsAffineHom (FiniteFreeAlgebraUnits.groupScheme
      (UnipotentPart.flatBasis (kernelBasis F N))).X.hom :=
  groupScheme_isAffineHom _

local instance specialMatrixUnits_affine :
    IsAffineHom (FiniteFreeAlgebraUnits.groupScheme (specialMatrixBasis F N)).X.hom :=
  groupScheme_isAffineHom _

attribute [local instance] upperUnitMap_dominant

/-- The special-fibre image of the Iwahori-to-hyperspecial homomorphism, identified with the
image of its unit-group presentation `𝓀[F] ⊗ Λ → 𝓀[F] ⊗ M_N(𝒪[F])`. -/
def specialFibreImageUnitIso :
    SchematicImage.image (iwahoriMatrixHom F N).specialFibreMap ≅
      SchematicImage.image (kernelFibreMap F N) :=
  SchematicImage.isoOfIsoSquare _ _ (kernelFibreIso F N) (matrixFibreIso F N)
    (kernelFibre_square F N).symm

@[reassoc]
theorem specialFibreImageUnitIso_hom_comp :
    (specialFibreImageUnitIso F N).hom ≫ SchematicImage.inclusion (kernelFibreMap F N) =
      SchematicImage.inclusion (iwahoriMatrixHom F N).specialFibreMap ≫
        (matrixFibreIso F N).hom :=
  SchematicImage.isoOfIsoSquare_hom_comp _ _ _ _ _

/-- The image of the unit-group presentation is the upper triangular unit group: the map
factors as the split surjection onto the upper triangular units followed by a closed
immersion. -/
def kernelFibreImageIso :
    SchematicImage.image (kernelFibreMap F N) ≅ upperUnits F N :=
  SchematicImage.isoOfDominantFactorizations (SchematicImage.projection (kernelFibreMap F N))
    (upperUnitMap F N) (SchematicImage.inclusion (kernelFibreMap F N))
    (upperFibreInclusion F N)
    (inferInstanceAs
      (IsClosedImmersion (SchematicImage.inclusion (kernelFibreMap F N)).hom.hom.left))
    (isClosedSubgroup_upperFibreInclusion F N)
    (SchematicImage.projection_inclusion _)

@[reassoc]
theorem kernelFibreImageIso_hom_comp :
    (kernelFibreImageIso F N).hom ≫ upperFibreInclusion F N =
      SchematicImage.inclusion (kernelFibreMap F N) :=
  SchematicImage.isoOfDominantFactorizations_hom_comp _ _ _ _ _ _ _


/-- The special-fibre image of the Iwahori-to-hyperspecial homomorphism as the upper triangular
unit group over the residue field. -/
def specialFibreImageUpperIso :
    SchematicImage.image (iwahoriMatrixHom F N).specialFibreMap ≅ upperUnits F N :=
  specialFibreImageUnitIso F N ≪≫ kernelFibreImageIso F N

theorem specialFibreImageUpperIso_hom_comp :
    (specialFibreImageUpperIso F N).hom ≫ upperGLMap F N =
      SchematicImage.inclusion (iwahoriMatrixHom F N).specialFibreMap ≫
        (matrixFibreIso F N ≪≫ glFibreIso F N).hom := by
  rw [specialFibreImageUpperIso, ← upperFibreInclusion_comp_glFibreIso]
  simp only [Iso.trans_hom, Category.assoc]
  rw [kernelFibreImageIso_hom_comp_assoc, specialFibreImageUnitIso_hom_comp_assoc]

/-- The special-fibre image of the homomorphism from the Iwahori model of `GL_N` to the
hyperspecial model `GL_N(𝒪[F])` is the block parabolic subgroup scheme of `GL_N` over the
residue field for the strictly decreasing weights `-i`, the upper triangular Borel subgroup. -/
def specialFibreImageIso :
    SchematicImage.image (iwahoriMatrixHom F N).specialFibreMap ≅
      GeneralLinear.blockParabolicScheme (Fin N) (CommRingCat.of 𝓀[F]) (upperWeight N) :=
  specialFibreImageUpperIso F N ≪≫ upperBorelIso F N

/-- Under `specialFibreImageIso`, the inclusion of the image corresponds to the block parabolic
inclusion, after identifying the special fibre of `GL_N(𝒪[F])` with `GL_N` over the residue
field. -/
theorem specialFibreImageIso_hom_comp :
    (specialFibreImageIso F N).hom ≫
        GeneralLinear.blockParabolicHom (Fin N) (CommRingCat.of 𝓀[F]) (upperWeight N) =
      SchematicImage.inclusion (iwahoriMatrixHom F N).specialFibreMap ≫
        (matrixFibreIso F N ≪≫ glFibreIso F N).hom := by
  rw [specialFibreImageIso, Iso.trans_hom, Category.assoc, upperBorelIso_hom_comp,
    specialFibreImageUpperIso_hom_comp]

theorem isParabolicSubgroup_specialFibreImage :
    IsParabolicSubgroup (SchematicImage.inclusion (iwahoriMatrixHom F N).specialFibreMap) := by
  have h := (isParabolicSubgroup_upperGLMap F N).iso_comp (specialFibreImageUpperIso F N)
  rw [specialFibreImageUpperIso_hom_comp] at h
  exact (IsParabolicSubgroup.comp_iso_iff _ _).mp h

theorem isBorelSubgroup_specialFibreImage :
    IsBorelSubgroup (SchematicImage.inclusion (iwahoriMatrixHom F N).specialFibreMap) := by
  have h := ((isBorelSubgroup_upperGLMap F N).iso_comp (specialFibreImageUpperIso F N)).comp_iso
    (matrixFibreIso F N ≪≫ glFibreIso F N).symm
  rwa [specialFibreImageUpperIso_hom_comp, Category.assoc, Iso.symm_hom, Iso.hom_inv_id,
    Category.comp_id] at h

/-! ### Rational surjectivity onto the special-fibre image -/

@[reassoc]
theorem kernelFibreIso_inv_comp :
    (kernelFibreIso F N).inv ≫ (iwahoriMatrixHom F N).specialFibreMap =
      kernelFibreMap F N ≫ (matrixFibreIso F N).inv := by
  rw [Iso.inv_comp_eq, ← Category.assoc, kernelFibre_square, Category.assoc, Iso.hom_inv_id,
    Category.comp_id]

theorem kernelFibreMap_eq : kernelFibreMap F N = upperUnitMap F N ≫ upperFibreInclusion F N :=
  rfl

/-- A section of the projection of the special fibre of the Iwahori model onto the special-fibre
image, through the upper triangular units. -/
def specialFibreImageSection :
    SchematicImage.image (iwahoriMatrixHom F N).specialFibreMap ⟶
      (iwahoriModel F N).specialFibre :=
  (specialFibreImageUpperIso F N).hom ≫ upperSectionMap F N ≫ (kernelFibreIso F N).inv

theorem specialFibreImageSection_comp :
    specialFibreImageSection F N ≫ (iwahoriMatrixHom F N).specialFibreMap =
      SchematicImage.inclusion (iwahoriMatrixHom F N).specialFibreMap := by
  have h1 : upperSectionMap F N ≫ (kernelFibreIso F N).inv ≫
        (iwahoriMatrixHom F N).specialFibreMap =
      upperFibreInclusion F N ≫ (matrixFibreIso F N).inv := by
    rw [kernelFibreIso_inv_comp, kernelFibreMap_eq, Category.assoc,
      upperSectionMap_comp_upperUnitMap_assoc]
  have h2 : (kernelFibreImageIso F N).hom ≫ upperFibreInclusion F N ≫ (matrixFibreIso F N).inv =
      SchematicImage.inclusion (kernelFibreMap F N) ≫ (matrixFibreIso F N).inv :=
    kernelFibreImageIso_hom_comp_assoc F N _
  have h3 : (specialFibreImageUnitIso F N).hom ≫ SchematicImage.inclusion (kernelFibreMap F N) ≫
        (matrixFibreIso F N).inv =
      SchematicImage.inclusion (iwahoriMatrixHom F N).specialFibreMap := by
    rw [specialFibreImageUnitIso_hom_comp_assoc, Iso.hom_inv_id, Category.comp_id]
  calc specialFibreImageSection F N ≫ (iwahoriMatrixHom F N).specialFibreMap
      = (specialFibreImageUnitIso F N).hom ≫ (kernelFibreImageIso F N).hom ≫
          upperSectionMap F N ≫ (kernelFibreIso F N).inv ≫
            (iwahoriMatrixHom F N).specialFibreMap := by
        simp only [specialFibreImageSection, specialFibreImageUpperIso, Iso.trans_hom,
          Category.assoc]
    _ = (specialFibreImageUnitIso F N).hom ≫ (kernelFibreImageIso F N).hom ≫
          upperFibreInclusion F N ≫ (matrixFibreIso F N).inv :=
        congrArg (fun t => (specialFibreImageUnitIso F N).hom ≫ (kernelFibreImageIso F N).hom ≫ t)
          h1
    _ = (specialFibreImageUnitIso F N).hom ≫ SchematicImage.inclusion (kernelFibreMap F N) ≫
          (matrixFibreIso F N).inv :=
        congrArg (fun t => (specialFibreImageUnitIso F N).hom ≫ t) h2
    _ = _ := h3

/-- Every residue-field point of the special-fibre image lifts to the special fibre of the
Iwahori model. -/
theorem specialFibreImage_projection_surjective :
    Function.Surjective (rationalPoints.map
      (SchematicImage.projection (iwahoriMatrixHom F N).specialFibreMap)) := by
  intro y
  refine ⟨rationalPoints.map (specialFibreImageSection F N) y, ?_⟩
  have : Mono (SchematicImage.inclusion (iwahoriMatrixHom F N).specialFibreMap).hom.hom :=
    inferInstanceAs (Mono (SchematicImage.inclusionOver (iwahoriMatrixHom F N).specialFibreMap))
  rw [rationalPoints.map_apply, rationalPoints.map_apply]
  refine (cancel_mono
    (SchematicImage.inclusion (iwahoriMatrixHom F N).specialFibreMap).hom.hom).mp ?_
  rw [Category.assoc, Category.assoc, ← Grp.comp_hom_hom, ← Grp.comp_hom_hom,
    SchematicImage.projection_inclusion, specialFibreImageSection_comp]

/-! ### The congruence subgroup of `GL_N(𝒪[F])` lies in the Iwahori subgroup -/

/-- The hyperspecial model `GL_N(𝒪[F])` as relative-component model data, with equal full and
neutral models. -/
def matrixOrderModelData :
    RelativeComponentModelData 𝒪[F] F (GeneralLinear.groupScheme (Fin N) (CommRingCat.of F)) :=
  orderModelData 𝒪[F] F N (matrixInclusion F N) (matrixBasis (CommRingCat.of 𝒪[F]) N)
    (matrixInclusion_injective F N) (matrixInclusion_spans F N)

/-- The unit of `M_N(𝒪[F])` attached to an integral section of the hyperspecial model. -/
abbrev matrixSectionUnit (x : (matrixOrderModelData F N).neutral.integralSections) :
    (Matrix (Fin N) (Fin N) 𝒪[F])ˣ :=
  sectionUnitsEquiv (R := CommRingCat.of 𝒪[F]) (matrixBasis (CommRingCat.of 𝒪[F]) N) x

/-- An integral section of the hyperspecial model with trivial reduction has unit congruent to
`1` modulo the maximal ideal. -/
theorem matrixSectionUnit_residue_of_reduction_eq_one
    (x : (matrixOrderModelData F N).neutral.integralSections)
    (hx : (matrixOrderModelData F N).neutral.reduction x = 1) :
    ((matrixSectionUnit F N x : Matrix (Fin N) (Fin N) 𝒪[F])).map
      (IsLocalRing.residue 𝒪[F]) = 1 := by
  have key := baseChange_congr_map_eq_one_iff (matrixBasis (CommRingCat.of 𝒪[F]) N)
    (CommRingCat.of 𝓀[F]) (matrixBasis (CommRingCat.of 𝓀[F]) N) (specialMatrixEquiv F N)
    (matrixBasis (CommRingCat.of 𝓀[F]) N) (AlgHom.id _ _) x
  rw [AlgHom.id_apply, specialMatrixEquiv_one_tmul] at key
  refine key.mp ?_
  have h1 : baseChangeSectionHom (WeilGm.baseMap (CommRingCat.of 𝒪[F]) (CommRingCat.of 𝓀[F]))
      (FiniteFreeAlgebraUnits.groupScheme (matrixBasis (CommRingCat.of 𝒪[F]) N)) x = 1 := hx
  rw [h1, MonObj.one_comp, MonObj.one_comp, MonObj.one_comp]

/-- The matrix of the generic point of an integral section of the hyperspecial model is its
unit, with entries mapped to `F`. -/
theorem matrixIntegralPointMap_matrix (x : (matrixOrderModelData F N).neutral.integralSections) :
    (GeneralLinear.rationalPointsEquiv N (CommRingCat.of F)
        ((matrixOrderModelData F N).neutral.integralPointMap x) : Matrix (Fin N) (Fin N) F) =
      ((matrixSectionUnit F N x : Matrix (Fin N) (Fin N) 𝒪[F])).map (algebraMap 𝒪[F] F) := by
  delta matrixOrderModelData
  refine orderModelData_integralPointMap_of_eq x ?_
  rfl

/-- Points of `GL_N(𝒪[F])` reducing to `1` lie in the Iwahori subgroup. -/
theorem matrixCongruenceSubgroup_le :
    (matrixOrderModelData F N).neutral.congruenceSubgroup ≤
      (iwahoriModelData F N).neutral.integralPoints := by
  rintro g ⟨x, hx, rfl⟩
  have hu := matrixSectionUnit_residue_of_reduction_eq_one F N x
    (((matrixOrderModelData F N).neutral.mem_congruenceKernel x).mp hx)
  change _ ∈ (iwahoriModel F N).integralPoints
  rw [iwahoriModel_integralPoints, mem_generalLinearIwahoriPoints]
  refine ⟨matrixSectionUnit F N x, fun i j hij => ?_, ?_⟩
  · rw [← IsLocalRing.residue_eq_zero_iff]
    have h := congrFun (congrFun hu i) j
    rw [Matrix.map_apply, Matrix.one_apply_ne hij.ne'] at h
    exact h
  · apply Units.ext
    exact matrixIntegralPointMap_matrix F N x

/-! ### KP Theorem 8.4.19(1)–(3) for the Iwahori model of `GL_N` -/

/-- The inclusion of the Iwahori order into `M_N(𝒪[F])` as a homomorphism of relative-component
model data, from the Iwahori model data to the hyperspecial model data. -/
def iwahoriMatrixModelHom :
    RelativeComponentModelHom (iwahoriModelData F N) (matrixOrderModelData F N) where
  full := iwahoriMatrixHom F N
  neutral := iwahoriMatrixHom F N
  component_comm := (Category.comp_id _).trans (Category.id_comp _).symm

/-- KP Axiom 4.1.22(1) and Theorem 8.4.19(1), first clause, for `GL_N` at an alcove. -/
theorem iwahoriMatrixModelHom_hasSmoothConnectedUnipotentKernel :
    (iwahoriMatrixModelHom F N).HasSmoothConnectedUnipotentKernel :=
  iwahoriMatrixHom_specialFibreKernel_properties F N

/-- KP Axiom 4.1.22(2) and Theorem 8.4.19(2) for `GL_N` at an alcove: the special-fibre image
is parabolic. -/
theorem iwahoriMatrixModelHom_hasParabolicSpecialFibreImage :
    (iwahoriMatrixModelHom F N).HasParabolicSpecialFibreImage :=
  isParabolicSubgroup_specialFibreImage F N

/-- The special-fibre image at an alcove is a Borel subgroup. -/
theorem iwahoriMatrixModelHom_isBorelSubgroup_specialFibreImage :
    IsBorelSubgroup (iwahoriMatrixModelHom F N).specialFibreImageInclusion :=
  isBorelSubgroup_specialFibreImage F N

/-- KP Axiom 4.1.22(4) and Theorem 8.4.19(3) for `GL_N` at an alcove: the reduction preimage of
the residue-field points of the special-fibre image is the Iwahori image. -/
theorem iwahoriMatrixModelHom_hasParabolicReductionPreimage :
    (iwahoriMatrixModelHom F N).HasParabolicReductionPreimage := by
  let : HenselianLocalRing 𝒪[F] := henselianLocalRing_integer
  rw [(iwahoriMatrixModelHom F N).hasParabolicReductionPreimage_iff (iwahoriModel_isSmooth F N)
    (specialFibreImage_projection_surjective F N),
    (iwahoriMatrixModelHom F N).congruenceKernel_le_sectionRange_iff]
  exact matrixCongruenceSubgroup_le F N

end Image

end Langlands.BruhatTits.IntegralModels
