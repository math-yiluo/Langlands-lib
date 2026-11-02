import Langlands.GroupScheme.Examples.QuasiSplitUnitaryLevi
import Langlands.GroupScheme.CorepresentedClosedSubgroup

/-! # The unitary Levi homomorphism is a closed immersion -/

noncomputable section
universe u
open CategoryTheory AlgebraicGeometry Algebra
open scoped TensorProduct CategoryTheory.MonObj

namespace Langlands.GroupScheme.QuasiSplitUnitary

variable {F E : Type u} [Field F] [Field E] [Algebra F E]
  [IsQuadraticExtension F E]

section Matrices
variable (R : Type u) [CommRing R] [Algebra F R]
attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-- A unitary matrix with vanishing off-diagonal entries is a Levi point: its first diagonal
entry is a unit `a`, and the unitary equation forces the second one to be `c_R(a)⁻¹`. -/
theorem exists_leviDiagonalUnitary (c : E ≃ₐ[F] E) (g : matrixPoints R c)
    (h01 : (g.val : Matrix (Fin 2) (Fin 2) (E ⊗[F] R)) 0 1 = 0)
    (h10 : (g.val : Matrix (Fin 2) (Fin 2) (E ⊗[F] R)) 1 0 = 0) :
    ∃ a, leviDiagonalUnitary R c a = g := by
  obtain ⟨⟨M, N, hMN, hNM⟩, hg⟩ := g
  change M 0 1 = 0 at h01
  change M 1 0 = 0 at h10
  have h00 : M 0 0 * N 0 0 = 1 := by
    have h := congrFun (congrFun hMN 0) 0
    simpa [Matrix.mul_apply, Fin.sum_univ_two, h01] using h
  have hU : M * adjoint (scalarConjugation R c) M = 1 := by
    rw [matrixPoints, Langlands.Shimura.AlgebraInvolution.mem_unitary_iff] at hg
    exact hg
  have h11 : M 1 1 * scalarConjugation R c (M 0 0) = 1 := by
    have h := congrFun (congrFun hU 1) 1
    simpa [adjoint, Matrix.mul_apply, Fin.sum_univ_two, h10] using h
  refine ⟨⟨M 0 0, N 0 0, h00, by rw [mul_comm]; exact h00⟩, ?_⟩
  apply Subtype.ext
  apply Units.ext
  rw [leviDiagonalUnitary_val]
  ext i j
  fin_cases i <;> fin_cases j
  · rfl
  · exact h01.symm
  · exact h10.symm
  · change scalarConjugation R c (N 0 0) = M 1 1
    calc scalarConjugation R c (N 0 0)
        = M 1 1 * scalarConjugation R c (M 0 0) * scalarConjugation R c (N 0 0) := by
          rw [h11, one_mul]
      _ = M 1 1 := by rw [mul_assoc, ← map_mul, h00, map_one, mul_one]

end Matrices

section Coefficients
variable (l : Module.Dual F E) (A : Type u) [CommRing A] [Algebra F A]

/-- The `A`-coefficient of an element of `E ⊗[F] A` along a linear functional on `E`. -/
def rightCoefficient : E ⊗[F] A →ₗ[F] A :=
  (TensorProduct.lid F A).toLinearMap ∘ₗ LinearMap.rTensor A l

omit [IsQuadraticExtension F E] in
@[simp] theorem rightCoefficient_tmul (e : E) (a : A) :
    rightCoefficient l A (e ⊗ₜ[F] a) = l e • a := by
  simp [rightCoefficient]

omit [IsQuadraticExtension F E] in
/-- Coefficients commute with every change of the right tensor factor. -/
theorem rightCoefficient_tensorCoefficientMap {A' : Type u} [CommRing A'] [Algebra F A']
    (f : A →ₐ[F] A') (y : E ⊗[F] A) :
    rightCoefficient l A' (tensorCoefficientMap f y) = f (rightCoefficient l A y) := by
  induction y using TensorProduct.inductionOn with
  | tmul e a => simp
  | add x y hx hy => simp only [map_add, hx, hy]

variable {A} in
/-- An element of `E ⊗[F] A` all of whose coefficients vanish is zero. -/
theorem eq_zero_of_rightCoefficient (y : E ⊗[F] A)
    (h : ∀ l : Module.Dual F E, rightCoefficient l A y = 0) : y = 0 := by
  classical
  let eb := Module.Free.chooseBasis F E
  have key : ∀ y : E ⊗[F] A, ∑ i, eb i ⊗ₜ[F] rightCoefficient (eb.coord i) A y = y := by
    intro y
    induction y using TensorProduct.inductionOn with
    | tmul e a =>
      simp only [rightCoefficient_tmul, Module.Basis.coord_apply, ← TensorProduct.smul_tmul,
        ← TensorProduct.sum_tmul, eb.sum_repr]
    | add x y hx hy =>
      simp only [map_add, TensorProduct.tmul_add, Finset.sum_add_distrib, hx, hy]
  rw [← key y]
  simp [h]

end Coefficients

section Closed
attribute [local instance] Algebra.TensorProduct.rightAlgebra

open Langlands.Shimura Langlands.Shimura.AlgebraInvolution MvPolynomial

variable {κ : Type u} [Fintype κ] (b : Module.Basis κ F (Matrix (Fin 2) (Fin 2) E))
  (c : E ≃ₐ[F] E)

/-- The matrix of the underlying unit of a similitude. -/
def similitudeMatrix (A : Type u) [CommRing A] [Algebra F A] :
    ((involution c).baseChange A).similitudes →* GL (Fin 2) (E ⊗[F] A) :=
  (Units.map (tensorMatrixEquiv (F := F) (E := E) A).toRingEquiv.toMonoidHom).comp
    ((involution c).baseChange A).underlyingUnit

theorem similitudeMatrix_val (A : Type u) [CommRing A] [Algebra F A]
    (x : ((involution c).baseChange A).similitudes) :
    ((similitudeMatrix c A x : GL (Fin 2) (E ⊗[F] A)) : Matrix (Fin 2) (Fin 2) (E ⊗[F] A)) =
      tensorMatrixEquiv A (x.1.1 : A ⊗[F] Matrix (Fin 2) (Fin 2) E) := rfl

/-- Similitudes with multiplier one whose matrices are diagonal. -/
def diagonalSimilitudes (A : Type u) [CommRing A] [Algebra F A] :
    Subgroup ((involution c).baseChange A).similitudes :=
  ((involution c).baseChange A).multiplier.ker ⊓
    (GeneralLinear.blockLeviSubgroup (E ⊗[F] A) (weights 1)).comap (similitudeMatrix c A)

theorem mem_diagonalSimilitudes (A : Type u) [CommRing A] [Algebra F A]
    (x : ((involution c).baseChange A).similitudes) :
    x ∈ diagonalSimilitudes c A ↔ ((x.1.2 : Aˣ) : A) = 1 ∧
      tensorMatrixEquiv A (x.1.1 : A ⊗[F] Matrix (Fin 2) (Fin 2) E) 0 1 = 0 ∧
      tensorMatrixEquiv A (x.1.1 : A ⊗[F] Matrix (Fin 2) (Fin 2) E) 1 0 = 0 := by
  change (x.1.2 = 1 ∧ ∀ i j, weights 1 i ≠ weights 1 j →
    tensorMatrixEquiv A (x.1.1 : A ⊗[F] Matrix (Fin 2) (Fin 2) E) i j = 0) ↔ _
  rw [Units.ext_iff, Units.val_one]
  constructor
  · rintro ⟨h1, h⟩
    exact ⟨h1, h 0 1 (by simp [weights]), h 1 0 (by simp [weights])⟩
  · rintro ⟨h1, h01, h10⟩
    refine ⟨h1, fun i j hij => ?_⟩
    fin_cases i <;> fin_cases j
    · exact absurd rfl hij
    · exact h01
    · exact h10
    · exact absurd rfl hij

/-- The Levi point `diag(a,c_A(a)⁻¹)` as a similitude with multiplier one. -/
def leviSimilitude (A : Type u) [CommRing A] [Algebra F A] :
    (E ⊗[F] A)ˣ →* ((involution c).baseChange A).similitudes :=
  ((involution c).baseChange A).unitaryInclusion.comp
    ((algebraPointsEquiv A c).symm.toMonoidHom.comp (leviDiagonalUnitary A c))

theorem similitudeMatrix_leviSimilitude (A : Type u) [CommRing A] [Algebra F A]
    (a : (E ⊗[F] A)ˣ) :
    similitudeMatrix c A (leviSimilitude c A a) = (leviDiagonalUnitary A c a).val :=
  congrArg Subtype.val ((algebraPointsEquiv A c).apply_symm_apply (leviDiagonalUnitary A c a))

theorem leviSimilitude_mem (A : Type u) [CommRing A] [Algebra F A] (a : (E ⊗[F] A)ˣ) :
    leviSimilitude c A a ∈ diagonalSimilitudes c A := by
  refine ⟨rfl, ?_⟩
  intro i j hij
  change ((similitudeMatrix c A (leviSimilitude c A a) : GL (Fin 2) (E ⊗[F] A)) :
    Matrix (Fin 2) (Fin 2) (E ⊗[F] A)) i j = 0
  rw [similitudeMatrix_leviSimilitude, leviDiagonalUnitary_val]
  fin_cases i <;> fin_cases j <;> simp_all [weights]

theorem leviSimilitude_injective (A : Type u) [CommRing A] [Algebra F A] :
    Function.Injective (leviSimilitude c A) := by
  intro a d h
  apply leviDiagonalUnitary_injective A c
  apply Subtype.ext
  rw [← similitudeMatrix_leviSimilitude, ← similitudeMatrix_leviSimilitude, h]

theorem leviSimilitude_surjective (A : Type u) [CommRing A] [Algebra F A]
    (x : ((involution c).baseChange A).similitudes) (hx : x ∈ diagonalSimilitudes c A) :
    ∃ a, leviSimilitude c A a = x := by
  let u := ((involution c).baseChange A).unitaryEquivKernel.symm ⟨x, hx.1⟩
  have hu : ((involution c).baseChange A).unitaryInclusion u = x :=
    congrArg Subtype.val
      (((involution c).baseChange A).unitaryEquivKernel.apply_symm_apply ⟨x, hx.1⟩)
  have hd := (mem_diagonalSimilitudes c A x).mp hx
  obtain ⟨a, ha⟩ := exists_leviDiagonalUnitary A c (algebraPointsEquiv A c u)
    (by rw [← hu] at hd; exact hd.2.1) (by rw [← hu] at hd; exact hd.2.2)
  refine ⟨a, ?_⟩
  rw [← hu]
  change ((involution c).baseChange A).unitaryInclusion
    ((algebraPointsEquiv A c).symm (leviDiagonalUnitary A c a)) = _
  rw [ha, MulEquiv.symm_apply_apply]

/-- The Levi points identify with the diagonal similitudes of multiplier one. -/
def leviSimilitudeEquiv (A : Type u) [CommRing A] [Algebra F A] :
    (E ⊗[F] A)ˣ ≃* diagonalSimilitudes c A :=
  MulEquiv.ofBijective ((leviSimilitude c A).codRestrict _ (leviSimilitude_mem c A))
    ⟨fun a d h => leviSimilitude_injective c A (congrArg Subtype.val h),
      fun x => by
        obtain ⟨a, ha⟩ := leviSimilitude_surjective c A x.1 x.2
        exact ⟨a, Subtype.ext ha⟩⟩

@[simp] theorem leviSimilitudeEquiv_val (A : Type u) [CommRing A] [Algebra F A]
    (a : (E ⊗[F] A)ˣ) : (leviSimilitudeEquiv c A a).val = leviSimilitude c A a := rfl

/-- The Levi similitudes are natural in the coefficient algebra. -/
theorem leviSimilitude_naturality {A A' : Type u} [CommRing A] [Algebra F A] [CommRing A']
    [Algebra F A'] (f : A →ₐ[F] A') (a : (E ⊗[F] A)ˣ) :
    leviSimilitude c A' (Units.map (tensorCoefficientMap f).toMonoidHom a) =
      ((involution c).baseChange A).map ((involution c).baseChange A')
        (changeCoefficients f).toRingHom f.toRingHom
        ((involution c).changeCoefficients_involution f) (changeCoefficients_scalar f)
        (leviSimilitude c A a) := by
  apply Subtype.ext
  apply Prod.ext
  · apply Units.ext
    apply (tensorMatrixEquiv (F := F) (E := E) A').injective
    change ((similitudeMatrix c A' (leviSimilitude c A' _) : GL (Fin 2) (E ⊗[F] A')) :
      Matrix (Fin 2) (Fin 2) (E ⊗[F] A')) =
        tensorMatrixEquiv A' (changeCoefficients f
          (leviSimilitude c A a).1.1)
    rw [similitudeMatrix_leviSimilitude, tensorMatrixEquiv_changeCoefficients]
    change _ = ((similitudeMatrix c A (leviSimilitude c A a) : GL (Fin 2) (E ⊗[F] A)) :
      Matrix (Fin 2) (Fin 2) (E ⊗[F] A)).map (tensorCoefficientMap f)
    rw [similitudeMatrix_leviSimilitude]
    exact (congrArg Units.val (leviDiagonalUnitary_naturality A c f a)).symm
  · apply Units.ext
    change (1 : A') = f 1
    rw [_root_.map_one]

/-- The matrix of the universal similitude over the similitude coordinate ring. -/
def universalMatrix :
    Matrix (Fin 2) (Fin 2) (E ⊗[F] (involution c).similitudeCoordinateRing b) :=
  tensorMatrixEquiv _ ((involution c).universalUnit b :
    (involution c).similitudeCoordinateRing b ⊗[F] Matrix (Fin 2) (Fin 2) E)

/-- The ideal of the similitude coordinate ring cut out by multiplier one and the vanishing of
both off-diagonal matrix entries of the universal similitude, written through the coefficients
of these entries along all linear functionals on `E`. -/
def leviIdeal : Ideal ((involution c).similitudeCoordinateRing b) :=
  Ideal.span ({(involution c).similitudeQuotient b (X SimilitudeVariable.multiplier) - 1} ∪
    {y | ∃ (l : Module.Dual F E) (i j : Fin 2), i ≠ j ∧
      rightCoefficient l _ (universalMatrix b c i j) = y})

/-- The classifying map of a similitude sends the coefficients of the universal matrix
entries to the coefficients of its own matrix entries. -/
theorem similitudeHom_universalMatrix (A : Type u) [CommRing A] [Algebra F A]
    (x : ((involution c).baseChange A).similitudes) (l : Module.Dual F E) (i j : Fin 2) :
    (involution c).similitudeHom b x (rightCoefficient l _ (universalMatrix b c i j)) =
      rightCoefficient l A
        (tensorMatrixEquiv A (x.1.1 : A ⊗[F] Matrix (Fin 2) (Fin 2) E) i j) := by
  rw [← rightCoefficient_tensorCoefficientMap]
  congr 1
  have hx : changeCoefficients ((involution c).similitudeHom b x)
      ((involution c).universalUnit b :
        (involution c).similitudeCoordinateRing b ⊗[F] Matrix (Fin 2) (Fin 2) E) =
      (x.1.1 : A ⊗[F] Matrix (Fin 2) (Fin 2) E) := by
    conv_rhs => rw [← (involution c).similitudePoint_similitudeHom b x]
    rfl
  rw [← hx, tensorMatrixEquiv_changeCoefficients]
  rfl

/-- A similitude is diagonal with multiplier one exactly when its classifying map kills
`leviIdeal b c`. -/
theorem mem_diagonalSimilitudes_iff_leviIdeal (A : Type u) [CommRing A] [Algebra F A]
    (x : ((involution c).baseChange A).similitudes) :
    x ∈ diagonalSimilitudes c A ↔
      ∀ y ∈ leviIdeal b c, (involution c).similitudeHom b x y = 0 := by
  rw [mem_diagonalSimilitudes]
  constructor
  · rintro ⟨h1, h01, h10⟩ y hy
    have hle : leviIdeal b c ≤ RingHom.ker ((involution c).similitudeHom b x) := by
      rw [leviIdeal, Ideal.span_le]
      rintro _ (rfl | ⟨l, i, j, hij, rfl⟩)
      · rw [SetLike.mem_coe, RingHom.mem_ker, map_sub, _root_.map_one, similitudeHom_quotient,
          aeval_X]
        exact sub_eq_zero.mpr h1
      · rw [SetLike.mem_coe, RingHom.mem_ker, similitudeHom_universalMatrix]
        fin_cases i <;> fin_cases j
        · exact absurd rfl hij
        · exact (congrArg (rightCoefficient l A) h01).trans (map_zero _)
        · exact (congrArg (rightCoefficient l A) h10).trans (map_zero _)
        · exact absurd rfl hij
    exact hle hy
  · intro h
    refine ⟨?_, ?_, ?_⟩
    · have h1 := h ((involution c).similitudeQuotient b (X SimilitudeVariable.multiplier) - 1)
        (Ideal.subset_span (Or.inl rfl))
      rw [map_sub, _root_.map_one, similitudeHom_quotient, aeval_X, sub_eq_zero] at h1
      exact h1
    · refine eq_zero_of_rightCoefficient _ fun l => ?_
      rw [← similitudeHom_universalMatrix b c A x l 0 1]
      exact h _ (Ideal.subset_span (Or.inr ⟨l, 0, 1, by decide, rfl⟩))
    · refine eq_zero_of_rightCoefficient _ fun l => ?_
      rw [← similitudeHom_universalMatrix b c A x l 1 0]
      exact h _ (Ideal.subset_span (Or.inr ⟨l, 1, 0, by decide, rfl⟩))

/-- The diagonal similitudes of multiplier one are cut out by `leviIdeal b c`. -/
theorem isCutOutBy_leviIdeal :
    Corepresented.IsCutOutBy (R := CommRingCat.of F)
      (B := (involution c).similitudeCoordinateAlgebra b)
      ((involution c).similitudeCorepresentableBy b)
      (fun A => diagonalSimilitudes c A) (leviIdeal b c) := fun A x =>
  mem_diagonalSimilitudes_iff_leviIdeal b c A x

/-- Points of the Weil restriction identify with the points of the closed subgroup scheme of
the similitude scheme cut out by `leviIdeal b c`. -/
def leviCutPointsEquiv (T : Over (Spec (CommRingCat.of F))) :
    (T ⟶ (WeilGm.groupScheme (CommRingCat.of F) E).X) ≃*
      (T ⟶ (Corepresented.cutGroupScheme (isCutOutBy_leviIdeal b c)).X) :=
  (WeilGm.pointsEquiv (CommRingCat.of F) E T).trans
    ((leviSimilitudeEquiv c ((algΓ (CommRingCat.of F)).obj T).unop).trans
      (Corepresented.pointsEquiv (Corepresented.cutFunctor (isCutOutBy_leviIdeal b c))
        (Corepresented.cutCorepresentableBy (isCutOutBy_leviIdeal b c)) T).symm)

/-- The cut-out point attached to a Weil restriction point is its Levi similitude. -/
theorem pointsEquiv_leviCutPointsEquiv (T : Over (Spec (CommRingCat.of F)))
    (x : T ⟶ (WeilGm.groupScheme (CommRingCat.of F) E).X) :
    Corepresented.pointsEquiv (Corepresented.cutFunctor (isCutOutBy_leviIdeal b c))
        (Corepresented.cutCorepresentableBy (isCutOutBy_leviIdeal b c)) T
        (leviCutPointsEquiv b c T x) =
      leviSimilitudeEquiv c ((algΓ (CommRingCat.of F)).obj T).unop
        (WeilGm.pointsEquiv (CommRingCat.of F) E T x) :=
  MulEquiv.apply_symm_apply _ _

omit [IsQuadraticExtension F E] in
/-- Base change of the right factor of `E ⊗[F] A`, as used by the Weil restriction points, is
`tensorCoefficientMap`. -/
theorem lTensor_eq_tensorCoefficientMap {A A' : Type u} [CommRing A] [Algebra F A]
    [CommRing A'] [Algebra F A'] (f : A →ₐ[F] A') (y : E ⊗[F] A) :
    Algebra.TensorProduct.lTensor (S := E) E f y = tensorCoefficientMap f y := rfl

theorem leviCutPointsEquiv_naturality {T T' : Over (Spec (CommRingCat.of F))} (a : T' ⟶ T)
    (x : T ⟶ (WeilGm.groupScheme (CommRingCat.of F) E).X) :
    leviCutPointsEquiv b c T' (a ≫ x) = a ≫ leviCutPointsEquiv b c T x := by
  apply (Corepresented.pointsEquiv _
    (Corepresented.cutCorepresentableBy (isCutOutBy_leviIdeal b c)) T').injective
  rw [Corepresented.pointsEquiv_naturality, pointsEquiv_leviCutPointsEquiv,
    pointsEquiv_leviCutPointsEquiv]
  apply Subtype.ext
  rw [leviSimilitudeEquiv_val, WeilGm.pointsEquiv_naturality]
  have hu : Units.map (Algebra.TensorProduct.lTensor (S := E) E
      ((algΓ (CommRingCat.of F)).map a).unop.hom : E ⊗[F] _ →* E ⊗[F] _)
        (WeilGm.pointsEquiv (CommRingCat.of F) E T x) =
      Units.map (tensorCoefficientMap ((algΓ (CommRingCat.of F)).map a).unop.hom).toMonoidHom
        (WeilGm.pointsEquiv (CommRingCat.of F) E T x) :=
    Units.ext (lTensor_eq_tensorCoefficientMap _ _)
  rw [hu]
  exact leviSimilitude_naturality c ((algΓ (CommRingCat.of F)).map a).unop.hom _

/-- The Weil restriction is isomorphic to the closed subgroup scheme cut out by
`leviIdeal b c`. -/
def leviIso : WeilGm.groupScheme (CommRingCat.of F) E ≅
    Corepresented.cutGroupScheme (isCutOutBy_leviIdeal b c) :=
  isoOfPoints (leviCutPointsEquiv b c) (leviCutPointsEquiv_naturality b c)

/-- The points of the cut-out subgroup scheme map to the similitude points through
`Corepresented.cutHom` by forgetting the membership in the diagonal similitudes. -/
theorem pointsEquiv_cutHom {T : Over (Spec (CommRingCat.of F))}
    (y : T ⟶ (Corepresented.cutGroupScheme (isCutOutBy_leviIdeal b c)).X) :
    SchemeModel.pointsEquiv b (involution c) T
        (y ≫ (Corepresented.cutHom (isCutOutBy_leviIdeal b c)).hom.hom) =
      (Corepresented.pointsEquiv _
        (Corepresented.cutCorepresentableBy (isCutOutBy_leviIdeal b c)) T y).val :=
  Corepresented.groupSchemeMap_points _ _ _ y

/-- Followed by the inclusion of the unitary group into the similitude group, the Levi
homomorphism is the isomorphism `leviIso b c` followed by the closed subgroup inclusion. -/
theorem leviHom_comp_unitaryInclusion :
    leviHom b c ≫ SchemeModel.unitaryInclusion b (involution c) =
      (leviIso b c).hom ≫ Corepresented.cutHom (isCutOutBy_leviIdeal b c) := by
  apply hom_ext_points
  intro T x
  rw [Grp.comp_hom_hom, Grp.comp_hom_hom, ← Category.assoc, ← Category.assoc]
  apply (SchemeModel.pointsEquiv b (involution c) T).injective
  rw [← SchemeModel.unitaryInclusion_points]
  have h : SchemeModel.unitaryPointsEquiv b (involution c) T (x ≫ (leviHom b c).hom.hom) =
      (algebraPointsEquiv _ c).symm (leviDiagonalUnitary ((algΓ (CommRingCat.of F)).obj T).unop c
        (WeilGm.pointsEquiv (CommRingCat.of F) E T x)) := by
    rw [← pointsEquiv_leviHom b c]
    exact ((algebraPointsEquiv _ c).symm_apply_apply _).symm
  rw [h, pointsEquiv_cutHom, leviIso, comp_isoOfPoints_hom, pointsEquiv_leviCutPointsEquiv]
  rfl

/-- The Levi homomorphism is a closed subgroup of the quasi-split unitary group scheme. -/
theorem isClosedSubgroup_leviHom : IsClosedSubgroup (leviHom b c) := by
  have : IsIso (leviIso b c).hom.hom.hom.left :=
    ((Grp.forget _ ⋙ Over.forget _).mapIso (leviIso b c)).isIso_hom
  have hcut := Corepresented.isClosedImmersion_cutHom (isCutOutBy_leviIdeal b c)
  have : IsClosedImmersion ((leviHom b c).hom.hom.left ≫
      (SchemeModel.unitaryInclusion b (involution c)).hom.hom.left) := by
    rw [← Over.comp_left, ← Grp.comp_hom_hom, leviHom_comp_unitaryInclusion, Grp.comp_hom_hom,
      Over.comp_left]
    exact IsClosedImmersion.comp _ _
  exact IsClosedImmersion.of_comp_isClosedImmersion _
    (SchemeModel.unitaryInclusion b (involution c)).hom.hom.left

end Closed

end Langlands.GroupScheme.QuasiSplitUnitary
