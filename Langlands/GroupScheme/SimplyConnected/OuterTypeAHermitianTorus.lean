import Langlands.GroupScheme.SimplyConnected.OuterTypeAHermitianDescent

/-!
# The split torus in the descended Hermitian presentation

In the setting of `OuterTypeAHermitianDescent`, suppose that on every cover point the
local isomorphism `E` carries the diagonal matrix with entries `χ i (s)` to the torus point
`s`. Then the descended presentation sends every torus point `s`, on every test scheme, to
the diagonal matrix with entries `1 ⊗ χ i (s)`. The proof first shows that these units
satisfy `∏ χ i (s) = 1`, and `χ i (s) χ j (s) = 1` whenever the `(i, j)` entry of `H` is
nonzero. It uses one automorphism of `M` moving `L` and descends along `T ×_K Spec M → T`.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj TensorProduct Matrix

namespace Langlands.GroupScheme.OuterTypeAHermitian

open SpecialLinearTitsCocycle SU3Root HermitianMatrix

section Cancel

variable (K M : Type u) [Field K] [Field M] [Algebra K M]

/-- Morphisms out of a test scheme are determined after pulling back to `T ×_K Spec M`. -/
theorem cancel_fst {T X : Over (Spec (CommRingCat.of K))} {v w : T ⟶ X}
    (h : fst T (cover K M) ≫ v = fst T (cover K M) ≫ w) : v = w := by
  have : Surjective (cover K M).hom := (fieldExtension_fpqc K M).1
  have : Flat (cover K M).hom := (fieldExtension_fpqc K M).2.1
  have : QuasiCompact (cover K M).hom := (fieldExtension_fpqc K M).2.2
  have : EffectiveEpi (fst T (cover K M)).left := by
    change EffectiveEpi (CategoryTheory.Limits.pullback.fst T.hom (cover K M).hom)
    infer_instance
  apply Over.OverMorphism.ext
  apply (cancel_epi (fst T (cover K M)).left).mp
  exact congrArg (fun q => q.left) h

/-- Pulling units back to `T ×_K Spec M` is injective. -/
theorem unitsMap_fst_injective (T : Over (Spec (CommRingCat.of K))) :
    Function.Injective
      (Units.map (fst T (cover K M)).left.appTop.hom.toMonoidHom) := by
  intro x y h
  apply (Gm.pointsEquiv _ T).symm.injective
  apply cancel_fst K M
  apply (Gm.pointsEquiv _ (T ⊗ cover K M)).injective
  rw [Gm.pointsEquiv_naturality, Gm.pointsEquiv_naturality, MulEquiv.apply_symm_apply,
    MulEquiv.apply_symm_apply, h]

end Cancel

section Torus

variable {K : Type u} (L : Type u) {M : Type u} [Field K] [Field L] [Field M] [Algebra K L]
  [Algebra K M] [Algebra L M] [IsScalarTower K L M]
  [Algebra.IsQuadraticExtension K L] [Algebra.IsSeparable K L]
  {n : ℕ} (H : Form (fieldInvolution K L) (Fin (n + 1)))
  {G : GroupScheme (Spec (CommRingCat.of K))}
  (E : LocalGroupIso (SpecialLinear.groupScheme (Fin (n + 1)) (CommRingCat.of K)) G
    (cover K M))
  {Y : Over (Spec (CommRingCat.of K))} (incl : Y ⟶ G.X)
  (ch : Fin (n + 1) → (Y ⟶ (Gm (Spec (CommRingCat.of K))).X))

/-- On every cover point, `E` carries the diagonal matrix with entries `ch i (s)` to the
point `s ≫ incl`. -/
def TorusDiagonal : Prop :=
  ∀ (Z : Over (Spec (CommRingCat.of K))) (a : Z ⟶ cover K M) (s : Z ⟶ Y),
    (SpecialLinear.pointsEquiv (Fin (n + 1)) (CommRingCat.of K) Z
        ((E.toFun a).symm (s ≫ incl)) : Matrix (Fin (n + 1)) (Fin (n + 1)) Γ(Z.left, ⊤)) =
      Matrix.diagonal fun i =>
        ((Gm.pointsEquiv _ Z (s ≫ ch i) : Γ(Z.left, ⊤)ˣ) : Γ(Z.left, ⊤))

variable {L} {E incl ch}

/-- At a cover point, the torus units have product one. -/
theorem prod_cover (ht : TorusDiagonal E incl ch) {Z : Over (Spec (CommRingCat.of K))}
    (a : Z ⟶ cover K M) (s : Z ⟶ Y) :
    ∏ i, Gm.pointsEquiv _ Z (s ≫ ch i) = 1 := by
  apply Units.ext
  have h := congrArg Matrix.det (ht Z a s)
  rw [Matrix.SpecialLinearGroup.det_coe, Matrix.det_diagonal] at h
  rw [Units.coe_prod, Units.val_one]
  exact h.symm

variable (L M) in
/-- Some automorphism of `M` over `K` moves `L`. -/
theorem exists_moves [IsGalois K M] :
    ∃ σ : M ≃ₐ[K] M, ∃ y : L, σ (algebraMap L M y) ≠ algebraMap L M y := by
  have hne : ¬ ∀ y : L, conjugation K L y = y :=
    fun h => conjugation_ne_one K L (AlgEquiv.ext h)
  obtain ⟨y, hy⟩ := not_forall.mp hne
  refine ⟨(conjugation K L).liftNormal M, y, ?_⟩
  rw [AlgEquiv.liftNormal_commutes]
  exact fun h => hy ((algebraMap L M).injective h)

/-- At a cover point, the torus units at `i` and `j` are mutually inverse whenever the
`(i, j)` entry of `H` is nonzero. -/
theorem mul_cover [IsGalois K M] (hout : OuterHermitian L H E) (ht : TorusDiagonal E incl ch)
    {Z : Over (Spec (CommRingCat.of K))} (a : Z ⟶ cover K M) (s : Z ⟶ Y) {i j : Fin (n + 1)}
    (hij : (H.gram : Matrix (Fin (n + 1)) (Fin (n + 1)) L) i j ≠ 0) :
    Gm.pointsEquiv _ Z (s ≫ ch i) * Gm.pointsEquiv _ Z (s ≫ ch j) = 1 := by
  obtain ⟨σ, hσ⟩ := exists_moves (K := K) L M
  let u : Fin (n + 1) → Γ(Z.left, ⊤)ˣ := fun k => Gm.pointsEquiv _ Z (s ≫ ch k)
  let g := SpecialLinear.pointsEquiv (Fin (n + 1)) (CommRingCat.of K) Z
    ((E.toFun a).symm (s ≫ incl))
  have hg : (g : Matrix (Fin (n + 1)) (Fin (n + 1)) Γ(Z.left, ⊤)) =
      Matrix.diagonal fun k => (u k : Γ(Z.left, ⊤)) := ht Z a s
  have h2 : (E.toFun (a ≫ coverAut K M σ)).symm (s ≫ incl) = (E.toFun a).symm (s ≫ incl) := by
    apply (SpecialLinear.pointsEquiv (Fin (n + 1)) (CommRingCat.of K) Z).injective
    apply Subtype.ext
    rw [ht Z (a ≫ coverAut K M σ) s, ht Z a s]
  have hdisc : discrepancy E σ a g = g := by
    simp only [discrepancy, g, MulEquiv.symm_apply_apply]
    rw [← h2, MulEquiv.apply_symm_apply, h2]
  have hmat := hout σ hσ Z a g
  rw [hdisc] at hmat
  have hDD : (Matrix.diagonal fun k => (u k : Γ(Z.left, ⊤))) *
      (Matrix.diagonal fun k => ((u k)⁻¹ : Γ(Z.left, ⊤)ˣ).val) = 1 := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext k
    exact (u k).mul_inv
  have hginv : ((g⁻¹ : Matrix.SpecialLinearGroup (Fin (n + 1)) Γ(Z.left, ⊤)) :
      Matrix (Fin (n + 1)) (Fin (n + 1)) Γ(Z.left, ⊤)) =
      Matrix.diagonal fun k => ((u k)⁻¹ : Γ(Z.left, ⊤)ˣ).val := by
    have h1 : ((g⁻¹ : Matrix.SpecialLinearGroup (Fin (n + 1)) Γ(Z.left, ⊤)) :
        Matrix (Fin (n + 1)) (Fin (n + 1)) Γ(Z.left, ⊤)) *
          (g : Matrix (Fin (n + 1)) (Fin (n + 1)) Γ(Z.left, ⊤)) = 1 := by
      rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
        Matrix.SpecialLinearGroup.coe_one]
    rw [hg] at h1
    calc _ = ((g⁻¹ : Matrix.SpecialLinearGroup (Fin (n + 1)) Γ(Z.left, ⊤)) :
          Matrix (Fin (n + 1)) (Fin (n + 1)) Γ(Z.left, ⊤)) *
          ((Matrix.diagonal fun k => (u k : Γ(Z.left, ⊤))) *
            (Matrix.diagonal fun k => ((u k)⁻¹ : Γ(Z.left, ⊤)ˣ).val)) := by
            rw [hDD, Matrix.mul_one]
      _ = _ := by rw [← Matrix.mul_assoc, h1, Matrix.one_mul]
  rw [hginv, Matrix.diagonal_transpose, hg] at hmat
  set X := Matrix.GeneralLinearGroup.map (coefficients a)
    (Matrix.GeneralLinearGroup.map (algebraMap L M) H.gram⁻¹) with hX
  have hX' : (Matrix.GeneralLinearGroup.map (coefficients a)
      (Matrix.GeneralLinearGroup.map (algebraMap L M) H.gram⁻¹)⁻¹ :
        Matrix (Fin (n + 1)) (Fin (n + 1)) Γ(Z.left, ⊤)) =
      ((X⁻¹ : Matrix.GeneralLinearGroup (Fin (n + 1)) Γ(Z.left, ⊤)) :
        Matrix (Fin (n + 1)) (Fin (n + 1)) Γ(Z.left, ⊤)) := by
    rw [hX, map_inv]
  rw [hX'] at hmat
  have hXX : ((X⁻¹ : Matrix.GeneralLinearGroup (Fin (n + 1)) Γ(Z.left, ⊤)) :
      Matrix (Fin (n + 1)) (Fin (n + 1)) Γ(Z.left, ⊤)) *
        (X : Matrix (Fin (n + 1)) (Fin (n + 1)) Γ(Z.left, ⊤)) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hcomm : ((X⁻¹ : Matrix.GeneralLinearGroup (Fin (n + 1)) Γ(Z.left, ⊤)) :
      Matrix (Fin (n + 1)) (Fin (n + 1)) Γ(Z.left, ⊤)) *
        (Matrix.diagonal fun k => (u k : Γ(Z.left, ⊤))) =
      (Matrix.diagonal fun k => ((u k)⁻¹ : Γ(Z.left, ⊤)ˣ).val) *
        ((X⁻¹ : Matrix.GeneralLinearGroup (Fin (n + 1)) Γ(Z.left, ⊤)) :
          Matrix (Fin (n + 1)) (Fin (n + 1)) Γ(Z.left, ⊤)) := by
    conv_lhs => rw [hmat]
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hXX, Matrix.one_mul]
  have hentry := congrFun (congrFun hcomm i) j
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul] at hentry
  have hc : ((X⁻¹ : Matrix.GeneralLinearGroup (Fin (n + 1)) Γ(Z.left, ⊤)) :
      Matrix (Fin (n + 1)) (Fin (n + 1)) Γ(Z.left, ⊤)) i j =
      ((coefficients a).comp (algebraMap L M))
        ((H.gram : Matrix (Fin (n + 1)) (Fin (n + 1)) L) i j) := by
    rw [hX, ← map_inv, ← map_inv, inv_inv, Matrix.GeneralLinearGroup.map_apply,
      Matrix.GeneralLinearGroup.map_apply]
    rfl
  rw [hc] at hentry
  have hunit : IsUnit (((coefficients a).comp (algebraMap L M))
      ((H.gram : Matrix (Fin (n + 1)) (Fin (n + 1)) L) i j)) :=
    (isUnit_iff_ne_zero.mpr hij).map _
  apply Units.ext
  rw [Units.val_mul, Units.val_one]
  apply hunit.mul_left_cancel
  rw [mul_one]
  calc _ = (u i : Γ(Z.left, ⊤)) * ((((coefficients a).comp (algebraMap L M))
        ((H.gram : Matrix (Fin (n + 1)) (Fin (n + 1)) L) i j)) * (u j : Γ(Z.left, ⊤))) := by
        ring
    _ = (u i : Γ(Z.left, ⊤)) * (((u i)⁻¹ : Γ(Z.left, ⊤)ˣ).val *
        ((coefficients a).comp (algebraMap L M))
          ((H.gram : Matrix (Fin (n + 1)) (Fin (n + 1)) L) i j)) := by rw [hentry]
    _ = _ := by rw [← mul_assoc, Units.mul_inv, one_mul]

end Torus

section Transfer

variable {K : Type u} (L : Type u) {M : Type u} [Field K] [Field L] [Field M] [Algebra K L]
  [Algebra K M] [Algebra L M] [IsScalarTower K L M]
  [Algebra.IsQuadraticExtension K L] [Algebra.IsSeparable K L]
  {n : ℕ} (H : Form (fieldInvolution K L) (Fin (n + 1)))
  {G : GroupScheme (Spec (CommRingCat.of K))}
  (E : LocalGroupIso (SpecialLinear.groupScheme (Fin (n + 1)) (CommRingCat.of K)) G
    (cover K M))
  {Y : Over (Spec (CommRingCat.of K))} (incl : Y ⟶ G.X)
  (ch : Fin (n + 1) → (Y ⟶ (Gm (Spec (CommRingCat.of K))).X))

omit [Field L] [Algebra K L] [Algebra L M] [IsScalarTower K L M]
  [Algebra.IsQuadraticExtension K L] [Algebra.IsSeparable K L] in
theorem unitsMap_fst_pointsEquiv (T : Over (Spec (CommRingCat.of K))) (s : T ⟶ Y)
    (i : Fin (n + 1)) :
    Units.map (fst T (cover K M)).left.appTop.hom.toMonoidHom (Gm.pointsEquiv _ T (s ≫ ch i)) =
      Gm.pointsEquiv _ (T ⊗ cover K M) ((fst T (cover K M) ≫ s) ≫ ch i) := by
  rw [Category.assoc, Gm.pointsEquiv_naturality _ (fst T (cover K M)) (s ≫ ch i)]

variable {L H E incl ch}

/-- On every test scheme, the torus units have product one. -/
theorem prod_eq_one (ht : TorusDiagonal E incl ch) (T : Over (Spec (CommRingCat.of K)))
    (s : T ⟶ Y) : ∏ i, Gm.pointsEquiv _ T (s ≫ ch i) = 1 := by
  apply unitsMap_fst_injective K M T
  rw [map_prod, map_one]
  simp only [unitsMap_fst_pointsEquiv]
  exact prod_cover ht (snd T (cover K M)) (fst T (cover K M) ≫ s)

/-- On every test scheme, the torus units at `i` and `j` are mutually inverse whenever the
`(i, j)` entry of `H` is nonzero. -/
theorem mul_eq_one [IsGalois K M] (hout : OuterHermitian L H E) (ht : TorusDiagonal E incl ch)
    (T : Over (Spec (CommRingCat.of K))) (s : T ⟶ Y) {i j : Fin (n + 1)}
    (hij : (H.gram : Matrix (Fin (n + 1)) (Fin (n + 1)) L) i j ≠ 0) :
    Gm.pointsEquiv _ T (s ≫ ch i) * Gm.pointsEquiv _ T (s ≫ ch j) = 1 := by
  apply unitsMap_fst_injective K M T
  rw [map_mul, map_one, unitsMap_fst_pointsEquiv, unitsMap_fst_pointsEquiv]
  exact mul_cover H hout ht (snd T (cover K M)) (fst T (cover K M) ≫ s) hij

variable (L) in
/-- The scalar inclusion `r ↦ 1 ⊗ r` of the sections into the tensor coefficients. -/
def scalarSections (T : Over (Spec (CommRingCat.of K))) :
    Γ(T.left, ⊤) →+* SpecialLinear.WeilRoot.tensorAlgebra K L T :=
  (Algebra.TensorProduct.includeRight :
    SpecialLinear.WeilRoot.sectionAlgebra K T →ₐ[K]
      L ⊗[K] SpecialLinear.WeilRoot.sectionAlgebra K T).toRingHom

omit [Field M] [Algebra K M] [Algebra L M] [IsScalarTower K L M] in
theorem scalarSections_bar (T : Over (Spec (CommRingCat.of K))) (r : Γ(T.left, ⊤)) :
    (SU3Root.SchemeModel.coefficientInvolution K L T).bar (scalarSections L T r) =
      scalarSections L T r := by
  have h : ∀ x : SpecialLinear.WeilRoot.sectionAlgebra K T,
      QuasiSplitUnitary.scalarConjugation _ (conjugation K L) ((1 : L) ⊗ₜ[K] x) =
        (1 : L) ⊗ₜ[K] x := by
    intro x
    rw [QuasiSplitUnitary.scalarConjugation_tmul, map_one]
  exact h r

omit [Algebra.IsQuadraticExtension K L] [Algebra.IsSeparable K L] in
theorem firstCoord_scalarSections {Z : Over (Spec (CommRingCat.of K))} (a : Z ⟶ cover K M)
    (r : Γ(Z.left, ⊤)) : firstCoord L a (scalarSections L Z r) = r := by
  have h : ∀ x : SpecialLinear.WeilRoot.sectionAlgebra K Z,
      tensorProj K L (fieldPoint L a) ((1 : L) ⊗ₜ[K] x) = x := by
    intro x
    rw [tensorProj_tmul, map_one, one_mul]
  exact h r

omit [Field M] [Algebra K M] [Algebra L M] [IsScalarTower K L M]
  [Algebra.IsQuadraticExtension K L] [Algebra.IsSeparable K L] in
theorem tensorMap_scalarSections {T T' : Over (Spec (CommRingCat.of K))} (t : T' ⟶ T)
    (r : Γ(T.left, ⊤)) :
    SpecialLinear.WeilRoot.tensorMap K L t (scalarSections L T r) =
      scalarSections L T' (t.left.appTop.hom r) := rfl

variable (L ch) in
/-- The diagonal tensor matrix with entries `1 ⊗ ch i (s)`. -/
def torusMatrix (T : Over (Spec (CommRingCat.of K))) (s : T ⟶ Y) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) (SpecialLinear.WeilRoot.tensorAlgebra K L T) :=
  Matrix.diagonal fun i => scalarSections L T (Gm.pointsEquiv _ T (s ≫ ch i) : Γ(T.left, ⊤))

omit [Algebra L M] [IsScalarTower K L M] [Algebra.IsQuadraticExtension K L]
  [Algebra.IsSeparable K L] in
theorem torusMatrix_det (ht : TorusDiagonal E incl ch) (T : Over (Spec (CommRingCat.of K)))
    (s : T ⟶ Y) : (torusMatrix L ch T s).det = 1 := by
  have h := congrArg (fun u : Γ(T.left, ⊤)ˣ => scalarSections L T (u : Γ(T.left, ⊤)))
    (prod_eq_one ht T s)
  simp only [Units.coe_prod, map_prod, Units.val_one, map_one] at h
  rw [torusMatrix, Matrix.det_diagonal]
  exact h

theorem torusMatrix_preserves [IsGalois K M] (hout : OuterHermitian L H E)
    (ht : TorusDiagonal E incl ch) (T : Over (Spec (CommRingCat.of K))) (s : T ⟶ Y) :
    Preserves (SchemeModel.tensorForm K L H T) (torusMatrix L ch T s) := by
  have hadj : HermitianMatrix.adjoint (SU3Root.SchemeModel.coefficientInvolution K L T)
      (torusMatrix L ch T s) = torusMatrix L ch T s := by
    rw [HermitianMatrix.adjoint, torusMatrix, Matrix.diagonal_map (map_zero _), Matrix.diagonal_transpose]
    congr 1
    funext i
    exact scalarSections_bar T _
  unfold Preserves
  rw [hadj]
  ext i j
  rw [torusMatrix, Matrix.mul_diagonal, Matrix.diagonal_mul, SchemeModel.tensorForm_gram,
    Matrix.map_apply]
  by_cases hij : (H.gram : Matrix (Fin (n + 1)) (Fin (n + 1)) L) i j = 0
  · rw [hij, map_zero, mul_zero, zero_mul]
  · have h1 := mul_eq_one hout ht T s hij
    calc _ = algebraMap L (SpecialLinear.WeilRoot.tensorAlgebra K L T)
          ((H.gram : Matrix (Fin (n + 1)) (Fin (n + 1)) L) i j) *
            scalarSections L T ((Gm.pointsEquiv _ T (s ≫ ch i) *
              Gm.pointsEquiv _ T (s ≫ ch j) : Γ(T.left, ⊤)ˣ) : Γ(T.left, ⊤)) := by
          rw [Units.val_mul, map_mul]
          ring
      _ = _ := by rw [h1, Units.val_one, map_one, mul_one]

/-- The torus matrix as a determinant-one isometry of the extended form. -/
def torusTensorPoint [IsGalois K M] (hout : OuterHermitian L H E)
    (ht : TorusDiagonal E incl ch) (T : Over (Spec (CommRingCat.of K))) (s : T ⟶ Y) :
    SchemeModel.tensorPoints K L H T :=
  ⟨Matrix.SpecialLinearGroup.toGL ⟨torusMatrix L ch T s, torusMatrix_det ht T s⟩,
    Subgroup.mem_inf.mpr ⟨torusMatrix_preserves hout ht T s, by
      rw [MonoidHom.mem_ker]
      exact Units.ext (torusMatrix_det ht T s)⟩⟩

/-- The descended presentation sends every torus point to its diagonal torus matrix. -/
theorem matrixPoints_torus [IsGalois K M] [IsAffineHom G.X.hom] (hin : InnerTrivial L E)
    (hout : OuterHermitian L H E) (ht : TorusDiagonal E incl ch)
    (T : Over (Spec (CommRingCat.of K))) (s : T ⟶ Y) :
    (matrixPoints K L H (descendedIso L H E hin hout) T (s ≫ incl) :
        Matrix (Fin (n + 1)) (Fin (n + 1)) (SpecialLinear.WeilRoot.tensorAlgebra K L T)) =
      torusMatrix L ch T s := by
  have key : s ≫ incl = (GroupModel.pointsEquiv K L H T).symm (torusTensorPoint hout ht T s) ≫
      (descendedIso L H E hin hout).hom.hom.hom := by
    apply cancel_fst K M
    rw [← Category.assoc, ← Category.assoc,
      comp_descendedIso_hom L H E hin hout (snd T (cover K M)), localEquiv_apply]
    have hsplit : splitAt L H (snd T (cover K M)) (GroupModel.pointsEquiv K L H _
        (fst T (cover K M) ≫ (GroupModel.pointsEquiv K L H T).symm
          (torusTensorPoint hout ht T s))) =
        SpecialLinear.pointsEquiv (Fin (n + 1)) (CommRingCat.of K) (T ⊗ cover K M)
          ((E.toFun (snd T (cover K M))).symm ((fst T (cover K M) ≫ s) ≫ incl)) := by
      apply Subtype.ext
      rw [coe_splitAt, GroupModel.pointsEquiv_naturality, MulEquiv.apply_symm_apply, ht]
      change ((torusMatrix L ch T s).map
        (SpecialLinear.WeilRoot.tensorMap K L (fst T (cover K M)))).map
          (firstCoord L (snd T (cover K M))) = _
      rw [torusMatrix, Matrix.diagonal_map (map_zero _), Matrix.diagonal_map (map_zero _)]
      congr 1
      funext i
      exact (firstCoord_scalarSections (snd T (cover K M))
        ((fst T (cover K M)).left.appTop.hom
          ((Gm.pointsEquiv _ T (s ≫ ch i) : Γ(T.left, ⊤)ˣ) : Γ(T.left, ⊤)))).trans
        (congrArg Units.val (unitsMap_fst_pointsEquiv (M := M) ch T s i))
    rw [hsplit, MulEquiv.symm_apply_apply, MulEquiv.apply_symm_apply]
  rw [key, matrixPoints_comp_hom, MulEquiv.apply_symm_apply]
  rfl

/-- The all-test Hermitian presentation of `G` produced by the descent, in the form of the
clauses of `OuterTypeAHermitianPresentationStatement` about `ρ`. -/
theorem exists_hermitianPresentation [IsGalois K M] [IsAffineHom G.X.hom]
    (hin : InnerTrivial L E) (hout : OuterHermitian L H E) (ht : TorusDiagonal E incl ch) :
    ∃ ρ : ∀ T : Over (Spec (CommRingCat.of K)),
        (T ⟶ G.X) →* Matrix.GeneralLinearGroup (Fin (n + 1))
          (SpecialLinear.WeilRoot.tensorAlgebra K L T),
      (∀ T, Function.Injective (ρ T)) ∧
      (∀ (T : Over (Spec (CommRingCat.of K)))
          (g : Matrix.GeneralLinearGroup (Fin (n + 1))
            (SpecialLinear.WeilRoot.tensorAlgebra K L T)),
        g ∈ (ρ T).range ↔
          (((g : Matrix (Fin (n + 1)) (Fin (n + 1))
                (SpecialLinear.WeilRoot.tensorAlgebra K L T)).map
              (SU3Root.SchemeModel.coefficientInvolution K L T).bar).transpose *
              (H.gram : Matrix (Fin (n + 1)) (Fin (n + 1)) L).map
                (algebraMap L (SpecialLinear.WeilRoot.tensorAlgebra K L T)) *
              (g : Matrix (Fin (n + 1)) (Fin (n + 1))
                (SpecialLinear.WeilRoot.tensorAlgebra K L T)) =
            (H.gram : Matrix (Fin (n + 1)) (Fin (n + 1)) L).map
              (algebraMap L (SpecialLinear.WeilRoot.tensorAlgebra K L T)) ∧
          Matrix.GeneralLinearGroup.det g = 1)) ∧
      (∀ {T T' : Over (Spec (CommRingCat.of K))} (a : T' ⟶ T) (x : T ⟶ G.X),
        (ρ T' (a ≫ x) : Matrix (Fin (n + 1)) (Fin (n + 1))
            (SpecialLinear.WeilRoot.tensorAlgebra K L T')) =
          (ρ T x : Matrix (Fin (n + 1)) (Fin (n + 1))
            (SpecialLinear.WeilRoot.tensorAlgebra K L T)).map
              (SpecialLinear.WeilRoot.tensorMap K L a)) ∧
      (∀ (T : Over (Spec (CommRingCat.of K))) (s : T ⟶ Y),
        (ρ T (s ≫ incl) : Matrix (Fin (n + 1)) (Fin (n + 1))
            (SpecialLinear.WeilRoot.tensorAlgebra K L T)) =
          Matrix.diagonal fun i =>
            (show SpecialLinear.WeilRoot.tensorAlgebra K L T from
              Algebra.TensorProduct.includeRight (R := K) (A := L)
                (B := SpecialLinear.WeilRoot.sectionAlgebra K T)
                (show SpecialLinear.WeilRoot.sectionAlgebra K T from
                  ((Gm.pointsEquiv _ T (s ≫ ch i) : Γ(T.left, ⊤)ˣ) : Γ(T.left, ⊤))))) :=
  ⟨matrixPoints K L H (descendedIso L H E hin hout),
    matrixPoints_injective K L H _,
    mem_range_matrixPoints K L H _,
    fun a x => matrixPoints_naturality K L H _ a x,
    matrixPoints_torus hin hout ht⟩

end Transfer

end Langlands.GroupScheme.OuterTypeAHermitian
