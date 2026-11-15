import Langlands.BruhatTits.IntegralModels.GeneralLinearIwahoriQuotient
import Langlands.GroupScheme.SimplyConnected.SpinCoverFundamentalWeightTransport
import Langlands.GroupScheme.KernelSquareTransport
import Langlands.AbelianScheme.KernelBaseChange

/-! # The special-fibre kernel from the Iwahori model to the hyperspecial model of `GL_N`

The inclusion of the Iwahori order into `M_N(𝒪[F])` extends the identity of `GL_N` to a
homomorphism from the Iwahori model to the hyperspecial model. The kernel of its special-fibre
map is the strictly lower unipotent group `1 + J_-`, so it is smooth, connected and unipotent.
See the paired Markdown file.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped TensorProduct ValuativeRel CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace FiniteFreeAlgebraUnits

section General

variable {R : CommRingCat.{u}} {A : Type u} [Ring A] [Algebra R A]
  {A' : Type u} [Ring A'] [Algebra R A'] {n m : ℕ}
  (b : Module.Basis (Fin n) R A) (b' : Module.Basis (Fin m) R A')

/-- The isomorphism of unit group schemes induced by an algebra isomorphism is its unit map. -/
theorem congrIso_hom_eq_map (e : A ≃ₐ[R] A') : (congrIso b b' e).hom = map b b' e.toAlgHom := by
  apply hom_ext_points
  intro T x
  apply (pointsEquiv b' T).injective
  rw [congrIso_hom_points, pointsEquiv_map]
  apply Units.ext
  rfl

/-- The unit map of an algebra map with a linear retraction is a monomorphism. -/
theorem mono_map (f : A →ₐ[R] A') (r : A' →ₗ[R] A) (hr : ∀ a, r (f a) = a) :
    Mono (map b b' f).hom.hom := by
  constructor
  intro T g g' hg
  apply (pointsEquiv b T).injective
  apply Units.ext
  have h := congrArg (fun y => ((pointsEquiv b' T y : _ˣ) : ((algΓ R).obj T).unop ⊗[R] A')) hg
  simp only [pointsEquiv_map, Units.coe_map] at h
  have hret : ∀ w : ((algΓ R).obj T).unop ⊗[R] A,
      LinearMap.lTensor _ r (Algebra.TensorProduct.map (AlgHom.id R _) f w) = w := by
    intro w
    induction w using TensorProduct.inductionOn with
    | tmul s a => simp [hr]
    | add w w' hw hw' => rw [map_add, map_add, hw, hw']
  rw [← hret (pointsEquiv b T g : _), ← hret (pointsEquiv b T g' : _)]
  exact congrArg _ h

end General

section BaseChange

variable {R : CommRingCat.{u}} {A : Type u} [Ring A] [Algebra R A]
  {A' : Type u} [Ring A'] [Algebra R A'] {n m : ℕ}
  (b : Module.Basis (Fin n) R A) (b' : Module.Basis (Fin m) R A')
  (R' : CommRingCat.{u}) [Algebra R R']

/-- The base-change tensor isomorphism is natural in the algebra. -/
theorem baseChangeTensorEquiv_map (S : Type u) [CommRing S] [Algebra R S] [Algebra R' S]
    [IsScalarTower R R' S] (f : A →ₐ[R] A') (w : S ⊗[R] A) :
    baseChangeTensorEquiv A' R' S (Algebra.TensorProduct.map (AlgHom.id R S) f w) =
      Algebra.TensorProduct.map (AlgHom.id R' S) (Algebra.TensorProduct.map (AlgHom.id R' R') f)
        (baseChangeTensorEquiv A R' S w) := by
  induction w using TensorProduct.inductionOn with
  | tmul s a => simp
  | add w w' hw hw' => simp only [map_add, hw, hw']

/-- Base change of the unit map of `f` is the unit map of the base change of `f`. -/
theorem baseChange_map_comp_baseChangeIso (f : A →ₐ[R] A') :
    (GroupScheme.baseChange (WeilGm.baseMap R R')).map (map b b' f) ≫ (baseChangeIso b' R').hom =
      (baseChangeIso b R').hom ≫
        map (b.baseChange R') (b'.baseChange R')
          (Algebra.TensorProduct.map (AlgHom.id R' R') f) := by
  apply hom_ext_points
  intro T x
  apply (pointsEquiv (b'.baseChange R') T).injective
  rw [Grp.comp_hom_hom, Grp.comp_hom_hom, ← Category.assoc, ← Category.assoc,
    baseChangeIso_hom_points, pointsEquiv_map, baseChangeIso_hom_points, basePointsEquiv_apply,
    basePointsEquiv_apply, baseChangePointsEquiv_comp, pointsEquiv_map]
  apply Units.ext
  simp only [Units.coe_map]
  exact baseChangeTensorEquiv_map R' _ f _

end BaseChange

/-! ### Homomorphisms of unit models -/

section UnitModelHom

variable (R K : Type u) [CommRing R] [IsDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
  {A : Type u} [Ring A] [Algebra R A] {A' : Type u} [Ring A'] [Algebra R A'] {n m : ℕ}
  (b : Module.Basis (Fin n) (CommRingCat.of R) A) (b' : Module.Basis (Fin m) (CommRingCat.of R) A')
  (N : ℕ) (e : K ⊗[R] A ≃ₐ[K] Matrix (Fin N) (Fin N) K)
  (e' : K ⊗[R] A' ≃ₐ[K] Matrix (Fin N) (Fin N) K)
  (f : A →ₐ[R] A') (hf : ∀ a, e' (1 ⊗ₜ f a) = e (1 ⊗ₜ a))

omit [IsDomain R] [IsFractionRing R K] in
include hf in
theorem unitModel_algHom_comp :
    (e'.toAlgHom.comp (Algebra.TensorProduct.map (AlgHom.id (CommRingCat.of K) (CommRingCat.of K))
      (f : A →ₐ[CommRingCat.of R] A')) : (CommRingCat.of K) ⊗[CommRingCat.of R] A →ₐ[CommRingCat.of K]
        Matrix (Fin N) (Fin N) K) = e.toAlgHom := by
  apply AlgHom.ext
  intro w
  induction w using TensorProduct.inductionOn with
  | tmul k a =>
    have h1 : (k ⊗ₜ[R] a : K ⊗[R] A) = k • (1 ⊗ₜ[R] a) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    have h2 : (k ⊗ₜ[R] f a : K ⊗[R] A') = k • (1 ⊗ₜ[R] f a) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    change e' (k ⊗ₜ[R] f a) = e (k ⊗ₜ[R] a)
    rw [h1, h2, map_smul, map_smul, hf]
  | add w w' hw hw' => rw [map_add, map_add, hw, hw']

/-- An algebra map of orders compatible with the generic identifications extends the identity
of `GL_N` to a homomorphism of unit models. -/
def unitModelHom : (unitModel R K b N e).Hom (unitModel R K b' N e') (𝟙 _) where
  hom := map b b' f
  generic_comm := by
    change (GroupScheme.baseChange (WeilGm.baseMap (CommRingCat.of R) (CommRingCat.of K))).map
        (map b b' f) ≫ ((baseChangeIso b' (CommRingCat.of K)).hom ≫
          ((congrIso _ _ e').hom ≫ (generalLinearIso (CommRingCat.of K) N).hom)) =
      ((baseChangeIso b (CommRingCat.of K)).hom ≫ ((congrIso _ _ e).hom ≫
        (generalLinearIso (CommRingCat.of K) N).hom)) ≫ 𝟙 _
    rw [Category.comp_id, ← Category.assoc, baseChange_map_comp_baseChangeIso, Category.assoc,
      ← Category.assoc (map _ _ _), congrIso_hom_eq_map, congrIso_hom_eq_map, map_comp,
      unitModel_algHom_comp R K N e e' f hf]

end UnitModelHom

end FiniteFreeAlgebraUnits

end Langlands.GroupScheme

/-! ### The hyperspecial order model and the Iwahori-to-hyperspecial homomorphism -/

namespace Langlands.BruhatTits.IntegralModels

open GroupScheme GroupScheme.FiniteFreeAlgebraUnits

variable (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] (N : ℕ)

/-- The inclusion `M_N(𝒪[F]) → M_N(F)`. -/
abbrev matrixInclusion : Matrix (Fin N) (Fin N) 𝒪[F] →ₐ[𝒪[F]] Matrix (Fin N) (Fin N) F :=
  (Algebra.ofId 𝒪[F] F).mapMatrix

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
theorem matrixInclusion_injective : Function.Injective (matrixInclusion F N) := by
  intro a a' h
  apply Matrix.ext
  intro i j
  exact IsFractionRing.injective 𝒪[F] F (congrFun (congrFun h i) j)

theorem matrixInclusion_spans (M : Matrix (Fin N) (Fin N) F) :
    ∃ a : Matrix (Fin N) (Fin N) 𝒪[F], ∃ c ∈ nonZeroDivisors 𝒪[F],
      c • M = matrixInclusion F N a := by
  obtain ⟨a, c, hc, h⟩ := iwahoriInclusion_spans F N M
  exact ⟨a.val, c, hc, h⟩

/-- The hyperspecial model: the unit group scheme of the order `M_N(𝒪[F])`. -/
def matrixOrderModel :
    IntegralModel 𝒪[F] F (GeneralLinear.groupScheme (Fin N) (CommRingCat.of F)) :=
  orderModel 𝒪[F] F N (matrixInclusion F N) (matrixBasis (CommRingCat.of 𝒪[F]) N)
    (matrixInclusion_injective F N) (matrixInclusion_spans F N)

/-- The inclusion of the Iwahori order into `M_N(𝒪[F])` extends the identity of `GL_N` to a
homomorphism from the Iwahori model to the hyperspecial model. -/
def iwahoriMatrixHom : (iwahoriModel F N).Hom (matrixOrderModel F N) (𝟙 _) :=
  unitModelHom 𝒪[F] F (iwahoriBasis F N) (matrixBasis (CommRingCat.of 𝒪[F]) N) N _ _
    (iwahoriOrder F N).val (fun _ => rfl)

theorem iwahoriMatrixHom_hom :
    (iwahoriMatrixHom F N).hom =
      map (iwahoriBasis F N) (matrixBasis (CommRingCat.of 𝒪[F]) N) (iwahoriOrder F N).val :=
  rfl

/-! ### Upper and strictly lower positions -/

/-- Positions on or above the diagonal. -/
abbrev UpperPosition : Type := {p : Fin N × Fin N // p.1 ≤ p.2}

/-- Positions strictly below the diagonal. -/
abbrev StrictLowerPosition : Type := {p : Fin N × Fin N // ¬ p.1 ≤ p.2}

/-- The number of positions on or above the diagonal. -/
abbrev upperCount : ℕ := Fintype.card (UpperPosition N)

/-- The number of positions strictly below the diagonal. -/
abbrev strictLowerCount : ℕ := Fintype.card (StrictLowerPosition N)

/-- Positions split into those on or above the diagonal and those strictly below it. -/
def upperLowerEquiv : Fin N × Fin N ≃ Fin (upperCount N) ⊕ Fin (strictLowerCount N) :=
  (Equiv.sumCompl (fun p : Fin N × Fin N => p.1 ≤ p.2)).symm.trans
    (Equiv.sumCongr (Fintype.equivFin _) (Fintype.equivFin _))

theorem upperLowerEquiv_symm_inl (i : Fin (upperCount N)) :
    (upperLowerEquiv N).symm (Sum.inl i) = ((Fintype.equivFin (UpperPosition N)).symm i).1 :=
  rfl

theorem upperLowerEquiv_symm_inr (j : Fin (strictLowerCount N)) :
    (upperLowerEquiv N).symm (Sum.inr j) =
      ((Fintype.equivFin (StrictLowerPosition N)).symm j).1 :=
  rfl

/-! ### The special fibre of the matrix order and the upper triangular reduction -/

/-- The identification `𝓀[F] ⊗ M_N(𝒪[F]) ≃ M_N(𝓀[F])`. -/
def specialMatrixEquiv :
    (CommRingCat.of 𝓀[F]) ⊗[CommRingCat.of 𝒪[F]] Matrix (Fin N) (Fin N) 𝒪[F] ≃ₐ[CommRingCat.of 𝓀[F]]
      Matrix (Fin N) (Fin N) 𝓀[F] :=
  AlgEquiv.ofRingEquiv (f := (matrixEquivTensor (Fin N) 𝒪[F] 𝓀[F]).symm.toRingEquiv) (by
    intro c
    change (matrixEquivTensor (Fin N) 𝒪[F] 𝓀[F]).symm (c ⊗ₜ 1) = algebraMap 𝓀[F] _ c
    rw [matrixEquivTensor_apply_symm, Matrix.map_one _ (map_zero _) (map_one _),
      Algebra.algebraMap_eq_smul_one])

theorem specialMatrixEquiv_one_tmul (M : Matrix (Fin N) (Fin N) 𝒪[F]) :
    specialMatrixEquiv F N (1 ⊗ₜ M) = M.map (IsLocalRing.residue 𝒪[F]) := by
  change (matrixEquivTensor (Fin N) 𝒪[F] 𝓀[F]).symm (1 ⊗ₜ M) = _
  rw [matrixEquivTensor_apply_symm, one_smul]
  rfl

/-- The base change to the residue field of the inclusion of the Iwahori order into `M_N(𝒪[F])`. -/
abbrev specialInclusion : SpecialAlgebra F N →ₐ[CommRingCat.of 𝓀[F]]
    (CommRingCat.of 𝓀[F]) ⊗[CommRingCat.of 𝒪[F]] Matrix (Fin N) (Fin N) 𝒪[F] :=
  Algebra.TensorProduct.map (AlgHom.id (CommRingCat.of 𝓀[F]) (CommRingCat.of 𝓀[F]))
    ((iwahoriOrder F N).val :
      iwahoriOrder F N →ₐ[CommRingCat.of 𝒪[F]] Matrix (Fin N) (Fin N) 𝒪[F])

/-- The upper triangular matrices over the residue field. -/
abbrev upperTriangular : Subalgebra (CommRingCat.of 𝓀[F]) (Matrix (Fin N) (Fin N) 𝓀[F]) :=
  Matrix.blockTriangularSubalgebra (CommRingCat.of 𝓀[F]) 𝓀[F] (id : Fin N → Fin N)

theorem specialMatrix_mem_upperTriangular (x : SpecialAlgebra F N) :
    specialMatrixEquiv F N (specialInclusion F N x) ∈ upperTriangular F N := by
  induction x using TensorProduct.inductionOn with
  | tmul c a =>
    have h : (c ⊗ₜ[CommRingCat.of 𝒪[F]] a : SpecialAlgebra F N) = c • (1 ⊗ₜ a) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [h, map_smul, map_smul]
    refine Subalgebra.smul_mem _ ?_ c
    rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, specialMatrixEquiv_one_tmul]
    intro i j hij
    exact (IsLocalRing.residue_eq_zero_iff _).mpr (a.2 i j hij)
  | add x y hx hy =>
    rw [map_add, map_add]
    exact add_mem hx hy

/-- The reduction of the special-fibre algebra `𝓀[F] ⊗ Λ` to the upper triangular matrices. -/
def specialUpper : SpecialAlgebra F N →ₐ[CommRingCat.of 𝓀[F]] upperTriangular F N :=
  ((specialMatrixEquiv F N).toAlgHom.comp (specialInclusion F N)).codRestrict _
    (specialMatrix_mem_upperTriangular F N)

/-- The inclusion of the upper triangular matrices into `𝓀[F] ⊗ M_N(𝒪[F])`. -/
def upperInclusion : upperTriangular F N →ₐ[CommRingCat.of 𝓀[F]]
    (CommRingCat.of 𝓀[F]) ⊗[CommRingCat.of 𝒪[F]] Matrix (Fin N) (Fin N) 𝒪[F] :=
  (specialMatrixEquiv F N).symm.toAlgHom.comp (upperTriangular F N).val

theorem upperInclusion_comp_specialUpper :
    (upperInclusion F N).comp (specialUpper F N) = specialInclusion F N := by
  apply AlgHom.ext
  intro x
  change (specialMatrixEquiv F N).symm (specialMatrixEquiv F N (specialInclusion F N x)) = _
  exact AlgEquiv.symm_apply_apply _ _

/-- The upper triangular part of a matrix over the residue field. -/
def upperPart : Matrix (Fin N) (Fin N) 𝓀[F] →ₗ[CommRingCat.of 𝓀[F]] upperTriangular F N where
  toFun M := ⟨Matrix.of fun i j => if i ≤ j then M i j else 0, fun i j hij => by
    change (if i ≤ j then M i j else 0) = 0
    simp only [not_le.mpr (show j < i from hij), ↓reduceIte]⟩
  map_add' M M' := by
    apply Subtype.ext
    ext i j
    change (if i ≤ j then M i j + M' i j else 0) =
      (if i ≤ j then M i j else 0) + (if i ≤ j then M' i j else 0)
    split_ifs <;> simp
  map_smul' c M := by
    apply Subtype.ext
    ext i j
    change (if i ≤ j then c * M i j else 0) = c * (if i ≤ j then M i j else 0)
    split_ifs <;> simp

/-- A linear retraction of the inclusion of the upper triangular matrices. -/
def upperRetraction : (CommRingCat.of 𝓀[F]) ⊗[CommRingCat.of 𝒪[F]] Matrix (Fin N) (Fin N) 𝒪[F]
    →ₗ[CommRingCat.of 𝓀[F]] upperTriangular F N :=
  (upperPart F N).comp (specialMatrixEquiv F N).toLinearMap

theorem upperRetraction_upperInclusion (M : upperTriangular F N) :
    upperRetraction F N (upperInclusion F N M) = M := by
  change upperPart F N (specialMatrixEquiv F N ((specialMatrixEquiv F N).symm M.1)) = M
  rw [AlgEquiv.apply_symm_apply]
  apply Subtype.ext
  ext i j
  change (if i ≤ j then M.1 i j else 0) = M.1 i j
  split_ifs with h
  · rfl
  · exact (M.2 (not_le.mp h)).symm

/-! ### Adapted bases and the unipotent kernel -/

/-- The basis of `𝓀[F] ⊗ Λ` by scaled matrix units, with the positions on or above the diagonal
first. -/
def kernelBasis :
    Module.Basis (Fin (upperCount N) ⊕ Fin (strictLowerCount N)) (CommRingCat.of 𝓀[F])
      (SpecialAlgebra F N) :=
  ((iwahoriUnitBasisCat F N).baseChange (CommRingCat.of 𝓀[F])).reindex (upperLowerEquiv N)

theorem kernelBasis_apply (x : Fin (upperCount N) ⊕ Fin (strictLowerCount N)) :
    kernelBasis F N x = 1 ⊗ₜ iwahoriUnit F N ((upperLowerEquiv N).symm x) := by
  simp [kernelBasis, iwahoriUnitBasisCat, iwahoriUnitBasis_apply]

theorem kernelBasis_repr_mul (x y z : Fin (upperCount N) ⊕ Fin (strictLowerCount N)) :
    (kernelBasis F N).repr (kernelBasis F N x * kernelBasis F N y) z =
      IsLocalRing.residue 𝒪[F] ((iwahoriUnitBasis F N).repr
        (iwahoriUnit F N ((upperLowerEquiv N).symm x) *
          iwahoriUnit F N ((upperLowerEquiv N).symm y))
        ((upperLowerEquiv N).symm z)) := by
  rw [kernelBasis_apply, kernelBasis_apply, Algebra.TensorProduct.tmul_mul_tmul, mul_one]
  rw [kernelBasis, Module.Basis.repr_reindex_apply, Module.Basis.baseChange_repr_tmul,
    Algebra.smul_def, mul_one]
  rfl

/-- The entries of an upper triangular matrix at the positions on or above the diagonal. -/
def upperCoords : upperTriangular F N ≃ₗ[CommRingCat.of 𝓀[F]]
    (UpperPosition N → CommRingCat.of 𝓀[F]) where
  toFun M p := (M : Matrix (Fin N) (Fin N) 𝓀[F]) p.1.1 p.1.2
  invFun c := ⟨Matrix.of fun i j => if h : i ≤ j then c ⟨(i, j), h⟩ else 0, fun i j hij => by
    change (if h : i ≤ j then c ⟨(i, j), h⟩ else 0) = 0
    simp only [not_le.mpr (show j < i from hij), ↓reduceDIte]⟩
  map_add' M M' := rfl
  map_smul' c M := rfl
  left_inv M := by
    apply Subtype.ext
    ext i j
    change (if h : i ≤ j then M.1 i j else 0) = M.1 i j
    split_ifs with h
    · rfl
    · exact (M.2 (not_le.mp h)).symm
  right_inv c := by
    funext p
    change (if h : p.1.1 ≤ p.1.2 then c ⟨(p.1.1, p.1.2), h⟩ else 0) = c p
    simp only [p.2, ↓reduceDIte]

/-- The basis of the upper triangular matrices by matrix units. -/
def upperBasis :
    Module.Basis (Fin (upperCount N)) (CommRingCat.of 𝓀[F]) (upperTriangular F N) :=
  (Module.Basis.ofEquivFun (upperCoords F N)).reindex (Fintype.equivFin (UpperPosition N))

theorem upperCoords_symm_apply_val (c : UpperPosition N → CommRingCat.of 𝓀[F]) (a b : Fin N) :
    (((upperCoords F N).symm c : upperTriangular F N) : Matrix (Fin N) (Fin N) 𝓀[F]) a b =
      if h : a ≤ b then c ⟨(a, b), h⟩ else 0 :=
  rfl

theorem upperBasis_apply_val (i : Fin (upperCount N)) (a b : Fin N) :
    ((upperBasis F N i : upperTriangular F N) : Matrix (Fin N) (Fin N) 𝓀[F]) a b =
      if (a, b) = ((Fintype.equivFin (UpperPosition N)).symm i).1 then 1 else 0 := by
  rw [upperBasis, Module.Basis.reindex_apply, Module.Basis.coe_ofEquivFun,
    upperCoords_symm_apply_val]
  have hq := ((Fintype.equivFin (UpperPosition N)).symm i).2
  by_cases h : a ≤ b
  · simp only [h, ↓reduceDIte, Pi.single_apply, Subtype.ext_iff]
  · have h' : (a, b) ≠ ((Fintype.equivFin (UpperPosition N)).symm i).1 := by
      intro h'
      rw [← h'] at hq
      exact h hq
    simp only [h, ↓reduceDIte, h']
    rfl

theorem specialUpper_one_tmul_val (x : iwahoriOrder F N) :
    ((specialUpper F N (1 ⊗ₜ x) : upperTriangular F N) : Matrix (Fin N) (Fin N) 𝓀[F]) =
      (x : Matrix (Fin N) (Fin N) 𝒪[F]).map (IsLocalRing.residue 𝒪[F]) := by
  change specialMatrixEquiv F N (specialInclusion F N (1 ⊗ₜ x)) = _
  rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, specialMatrixEquiv_one_tmul]
  rfl

theorem specialUpper_kernelBasis (x : Fin (upperCount N) ⊕ Fin (strictLowerCount N))
    (a b : Fin N) :
    ((specialUpper F N (kernelBasis F N x) : upperTriangular F N) :
        Matrix (Fin N) (Fin N) 𝓀[F]) a b =
      if (a, b) = (upperLowerEquiv N).symm x then
        IsLocalRing.residue 𝒪[F] (unitScale F N ((upperLowerEquiv N).symm x)) else 0 := by
  rw [kernelBasis_apply, specialUpper_one_tmul_val, Matrix.map_apply, iwahoriUnit_coe]
  by_cases h : (a, b) = (upperLowerEquiv N).symm x
  · simp only [h, ↓reduceIte]
    rw [← h]
    simp only [Matrix.single_apply_same]
  · simp only [h, ↓reduceIte]
    rw [Matrix.single_apply_of_ne (h := fun h' => h (Prod.ext h'.1.symm h'.2.symm)), map_zero]

theorem specialUpper_kernelBasis_inl (i : Fin (upperCount N)) :
    specialUpper F N (kernelBasis F N (Sum.inl i)) = upperBasis F N i := by
  apply Subtype.ext
  ext a b
  rw [specialUpper_kernelBasis, upperBasis_apply_val, upperLowerEquiv_symm_inl]
  have hq := ((Fintype.equivFin (UpperPosition N)).symm i).2
  simp only [unitScale, not_lt.mpr hq, ↓reduceIte, map_one]

theorem residue_iwahoriUniformizer : IsLocalRing.residue 𝒪[F] (iwahoriUniformizer F) = 0 :=
  (IsLocalRing.residue_eq_zero_iff _).mpr
    ((IsLocalRing.mem_maximalIdeal _).mpr (iwahoriUniformizer_irreducible F).not_isUnit)

theorem specialUpper_kernelBasis_inr (j : Fin (strictLowerCount N)) :
    specialUpper F N (kernelBasis F N (Sum.inr j)) = 0 := by
  apply Subtype.ext
  ext a b
  rw [specialUpper_kernelBasis, upperLowerEquiv_symm_inr]
  have hq := ((Fintype.equivFin (StrictLowerPosition N)).symm j).2
  simp only [unitScale, not_le.mp hq, ↓reduceIte, residue_iwahoriUniformizer, ite_self]
  rfl

/-- Products of two strictly lower scaled matrix units have no strictly lower coordinate in the
special fibre: such a coordinate would need two uniformizers to equal one. -/
theorem kernelBasis_structureConst (a a' m : Fin (strictLowerCount N)) :
    UnipotentPart.structureConst (kernelBasis F N) a a' m = 0 := by
  by_contra h
  unfold UnipotentPart.structureConst at h
  rw [kernelBasis_repr_mul] at h
  obtain ⟨-, -, h3⟩ := isUnit_repr_iwahoriUnit_mul F N _ _ _
    ((IsLocalRing.residue_ne_zero_iff_isUnit _).mp h)
  have hp := ((Fintype.equivFin (StrictLowerPosition N)).symm a).2
  have hq := ((Fintype.equivFin (StrictLowerPosition N)).symm a').2
  have hm := ((Fintype.equivFin (StrictLowerPosition N)).symm m).2
  rw [upperLowerEquiv_symm_inr, upperLowerEquiv_symm_inr, upperLowerEquiv_symm_inr] at h3
  simp only [not_le.mp hp, not_le.mp hq, not_le.mp hm, ↓reduceIte] at h3
  omega

/-- The universal radical element of the strictly lower part is nilpotent. -/
theorem kernelRadical_nilpotent :
    IsNilpotent (UnipotentPart.universalRadical (kernelBasis F N)) :=
  UnipotentPart.isNilpotent_universalRadical_of_weights (specialUpper F N) (kernelBasis F N)
    (upperBasis F N) (fun _ => 1) (specialUpper_kernelBasis_inl F N)
    (specialUpper_kernelBasis_inr F N) (fun _ => le_rfl)
    (fun a a' m h => absurd (kernelBasis_structureConst F N a a' m) h)

/-- The unipotent group scheme of the kernel of the upper triangular reduction of `𝓀[F] ⊗ Λ`;
its points are `1 + J_-` for the strictly lower part `J_-`. -/
abbrev strictLowerKernel : GroupScheme (Spec (CommRingCat.of 𝓀[F])) :=
  UnipotentPart.groupScheme (specialUpper F N) (kernelBasis F N) (kernelRadical_nilpotent F N)
    (specialUpper_kernelBasis_inr F N) (upperBasis F N) (specialUpper_kernelBasis_inl F N)

theorem strictLowerKernel_properties :
    Smooth (strictLowerKernel F N).X.hom ∧ ConnectedSpace (strictLowerKernel F N).X.left ∧
      IsUnipotent (strictLowerKernel F N) :=
  ⟨UnipotentPart.smooth _ _ _ _ _ _, UnipotentPart.connectedSpace _ _ _ _ _ _,
    UnipotentPart.isUnipotent _ _ _ _ _ _ (fun _ => 1)
      (fun a a' m h => absurd (kernelBasis_structureConst F N a a' m) h) (fun _ => le_rfl)⟩

/-! ### The special-fibre kernel of the Iwahori-to-hyperspecial homomorphism -/

/-- The basis of `𝓀[F] ⊗ M_N(𝒪[F])` obtained by base change of the matrix-unit basis. -/
abbrev specialMatrixBasis :
    Module.Basis (Fin (N * N)) (CommRingCat.of 𝓀[F])
      ((CommRingCat.of 𝓀[F]) ⊗[CommRingCat.of 𝒪[F]] Matrix (Fin N) (Fin N) 𝒪[F]) :=
  (matrixBasis (CommRingCat.of 𝒪[F]) N).baseChange (CommRingCat.of 𝓀[F])

/-- The special fibre of the Iwahori model as the unit group of `𝓀[F] ⊗ Λ`, with the basis adapted
to the upper triangular reduction. -/
def kernelFibreIso :
    (iwahoriModel F N).specialFibre ≅
      FiniteFreeAlgebraUnits.groupScheme (UnipotentPart.flatBasis (kernelBasis F N)) :=
  baseChangeIso (iwahoriBasis F N) (CommRingCat.of 𝓀[F]) ≪≫
    congrIso ((iwahoriBasis F N).baseChange (CommRingCat.of 𝓀[F]))
      (UnipotentPart.flatBasis (kernelBasis F N)) AlgEquiv.refl

/-- The special fibre of the hyperspecial model as the unit group of `𝓀[F] ⊗ M_N(𝒪[F])`. -/
def matrixFibreIso :
    (matrixOrderModel F N).specialFibre ≅
      FiniteFreeAlgebraUnits.groupScheme (specialMatrixBasis F N) :=
  baseChangeIso (matrixBasis (CommRingCat.of 𝒪[F]) N) (CommRingCat.of 𝓀[F])

/-- The unit map of `𝓀[F] ⊗ Λ → 𝓀[F] ⊗ M_N(𝒪[F])`, factored through the unit group of the upper
triangular matrices. -/
abbrev kernelFibreMap :
    FiniteFreeAlgebraUnits.groupScheme (UnipotentPart.flatBasis (kernelBasis F N)) ⟶
      FiniteFreeAlgebraUnits.groupScheme (specialMatrixBasis F N) :=
  UnipotentPart.unitMap (specialUpper F N) (kernelBasis F N) (upperBasis F N) ≫
    map (upperBasis F N) (specialMatrixBasis F N) (upperInclusion F N)

theorem kernelFibre_square_aux :
    ((baseChangeIso (iwahoriBasis F N) (CommRingCat.of 𝓀[F])).hom ≫
        (congrIso ((iwahoriBasis F N).baseChange (CommRingCat.of 𝓀[F]))
          (UnipotentPart.flatBasis (kernelBasis F N)) AlgEquiv.refl).hom) ≫
        (map (UnipotentPart.flatBasis (kernelBasis F N)) (upperBasis F N) (specialUpper F N) ≫
          map (upperBasis F N) (specialMatrixBasis F N) (upperInclusion F N)) =
      (GroupScheme.baseChange (WeilGm.baseMap (CommRingCat.of 𝒪[F]) (CommRingCat.of 𝓀[F]))).map
          (map (iwahoriBasis F N) (matrixBasis (CommRingCat.of 𝒪[F]) N) (iwahoriOrder F N).val) ≫
        (baseChangeIso (matrixBasis (CommRingCat.of 𝒪[F]) N) (CommRingCat.of 𝓀[F])).hom := by
  rw [Category.assoc, baseChange_map_comp_baseChangeIso, map_comp, upperInclusion_comp_specialUpper,
    congrIso_hom_eq_map, map_comp]
  congr 2

theorem kernelFibre_square :
    (kernelFibreIso F N).hom ≫ kernelFibreMap F N =
      (iwahoriMatrixHom F N).specialFibreMap ≫ (matrixFibreIso F N).hom :=
  kernelFibre_square_aux F N

/-- The special-fibre kernel of the Iwahori-to-hyperspecial homomorphism is the strictly lower
unipotent group `1 + J_-`. -/
def specialFibreKernelIso :
    kernel (iwahoriMatrixHom F N).specialFibreMap ≅ strictLowerKernel F N :=
  haveI := mono_map (upperBasis F N) (specialMatrixBasis F N) (upperInclusion F N)
    (upperRetraction F N) (upperRetraction_upperInclusion F N)
  kernelSquareIso _ _ (kernelFibreIso F N) (matrixFibreIso F N) (kernelFibre_square F N) ≪≫
    kernelPostcompIso (UnipotentPart.unitMap (specialUpper F N) (kernelBasis F N) (upperBasis F N))
      (map (upperBasis F N) (specialMatrixBasis F N) (upperInclusion F N)) ≪≫
    (UnipotentPart.kernelIso _ _ _ _ _ _).symm

/-- The first clause of KP 8.4.15 and 8.4.19(1) for `GL_N` at an alcove (no root-group product):
the kernel of the special-fibre map from the Iwahori
model to the hyperspecial model `GL_N(𝒪[F])` is smooth, connected and unipotent. -/
theorem iwahoriMatrixHom_specialFibreKernel_properties :
    Smooth (kernel (iwahoriMatrixHom F N).specialFibreMap).X.hom ∧
      ConnectedSpace (kernel (iwahoriMatrixHom F N).specialFibreMap).X.left ∧
        IsUnipotent (kernel (iwahoriMatrixHom F N).specialFibreMap) :=
  smooth_connected_unipotent_of_groupIso (specialFibreKernelIso F N)
    (strictLowerKernel_properties F N)

end Langlands.BruhatTits.IntegralModels
