import Langlands.GroupScheme.Quaternionic.SplittingMatrix
import Langlands.GroupScheme.Quaternionic.GroupSchemes
import Langlands.GroupScheme.SymplecticMatrix.Basic
import Langlands.GroupScheme.SymplecticMatrix.Darboux
import Langlands.GroupScheme.ClosedSubgroupMonomorphism
import Langlands.GroupScheme.Torus.Split
import Langlands.AbelianScheme.KernelBaseChange
import Langlands.GroupScheme.SymplecticMatrix.Reductive
import Langlands.GroupScheme.Reductive.SemisimpleFieldReflectionProof
import Langlands.GroupScheme.Dynamic.CentralizerReductiveTransport
import Langlands.Algebra.CentralSimple.FiniteGaloisSplitting

/-! # The quaternionic symplectic groups are connected reductive

Let `D` be a central division algebra over a field `K` with an involution of the first kind `σ`,
`H` an invertible antihermitian Gram matrix, and `e : L ⊗[K] D ≃ₐ[L] M₂(L)` a matrix chart. If
the symmetric elements of `σ` form a `3`-dimensional space (in characteristic not two: `σ` is
orthogonal), the split Gram matrix `C = splitGram e σ H` is alternating. A Darboux matrix `P`
with `P C Pᵀ = J` identifies the base change of the symplectic group `σ.symplecticGroup H` to
`L` with the split symplectic group `SymplecticMatrix.groupScheme`; on points it is
`u ↦ P Φ(u) P'` for the matrix chart `Φ` (`splittingIso`). Since the split symplectic group is
connected reductive and connected reductivity descends along field extensions,
`σ.symplecticGroup H` is connected reductive (`isConnectedReductive_symplecticGroup`), with the
splitting field taken to be the finite Galois splitting field of `D` from the Library.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Matrix Module
open scoped TensorProduct CategoryTheory.MonObj

namespace Langlands.GroupScheme.Quaternionic

section Sections

variable (K L : Type u) [CommRing K] [CommRing L] [Algebra K L]

/-- The base map `Spec L → Spec K`. -/
abbrev scalarBaseMap : Spec (CommRingCat.of L) ⟶ Spec (CommRingCat.of K) :=
  Spec.map (CommRingCat.ofHom (algebraMap K L))

/-- Global sections of a scheme over `L`, as a `K`-algebra. -/
abbrev restrictedSections (T : Over (Spec (CommRingCat.of L))) :
    CommAlgCat (CommRingCat.of K) :=
  ((algΓ (CommRingCat.of K)).obj ((Over.map (scalarBaseMap K L)).obj T)).unop

/-- The `L`-algebra structure of the global sections of a scheme over `L`. -/
local instance restrictedSectionsAlgebra (T : Over (Spec (CommRingCat.of L))) :
    Algebra L (restrictedSections K L T) :=
  inferInstanceAs (Algebra L ((algΓ (CommRingCat.of L)).obj T).unop)

local instance restrictedSectionsScalarTower (T : Over (Spec (CommRingCat.of L))) :
    IsScalarTower K L (restrictedSections K L T) := by
  apply IsScalarTower.of_algebraMap_eq'
  apply RingHom.ext
  intro r
  change (T.hom ≫ scalarBaseMap K L).appTop ((Scheme.ΓSpecIso (CommRingCat.of K)).inv r) =
    T.hom.appTop ((Scheme.ΓSpecIso (CommRingCat.of L)).inv (algebraMap K L r))
  rw [Scheme.Hom.comp_appTop]
  exact congrArg T.hom.appTop
    (ConcreteCategory.congr_hom (Scheme.ΓSpecIso_inv_naturality
      (CommRingCat.ofHom (algebraMap K L))) r).symm

/-- The structure map `L → Γ(T, ⊤)` is the scalar map of `T`. -/
theorem algebraMap_restrictedSections (T : Over (Spec (CommRingCat.of L))) :
    algebraMap L (restrictedSections K L T) = scalarMap T :=
  rfl

end Sections

section Rectangular

variable {R : Type*} [CommRing R] {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α]
  [DecidableEq β]

/-- Conjugation by a rectangular matrix with a right inverse preserves determinants, when the
index types have the same size. -/
theorem det_mul_mul_of_mul_eq_one (eqv : β ≃ α) {P : Matrix α β R} {P' : Matrix β α R}
    (h : P * P' = 1) (g : Matrix α α R) : (P' * g * P).det = g.det := by
  have hsub : (P' * g * P).submatrix eqv.symm eqv.symm =
      P'.submatrix eqv.symm id * g * P.submatrix id eqv.symm := by
    rw [Matrix.submatrix_mul _ _ _ id _ Function.bijective_id,
      Matrix.submatrix_mul _ _ _ id _ Function.bijective_id, Matrix.submatrix_id_id]
  have hQ : P.submatrix id eqv.symm * P'.submatrix eqv.symm id = 1 := by
    rw [Matrix.submatrix_mul_equiv, h, Matrix.submatrix_id_id]
  rw [← Matrix.det_submatrix_equiv_self eqv.symm, hsub, Matrix.det_mul, Matrix.det_mul,
    mul_comm (P'.submatrix eqv.symm id).det, mul_assoc, ← Matrix.det_mul, Matrix.det_mul_comm,
    hQ, Matrix.det_one, mul_one]

/-- Over a field, two-sided inverse rectangular matrices have index types of the same size. -/
theorem card_eq_of_mul_eq_one {F : Type*} [Field F] {P : Matrix α β F} {P' : Matrix β α F}
    (h₁ : P * P' = 1) (h₂ : P' * P = 1) : Fintype.card α = Fintype.card β := by
  apply le_antisymm
  · calc Fintype.card α = (P * P').rank := by rw [h₁, Matrix.rank_one]
      _ ≤ P.rank := Matrix.rank_mul_le_left _ _
      _ ≤ Fintype.card β := Matrix.rank_le_card_width _
  · calc Fintype.card β = (P' * P).rank := by rw [h₂, Matrix.rank_one]
      _ ≤ P'.rank := Matrix.rank_mul_le_left _ _
      _ ≤ Fintype.card α := Matrix.rank_le_card_width _

end Rectangular

namespace FirstKindInvolution

attribute [local instance] restrictedSectionsAlgebra restrictedSectionsScalarTower

variable {K D : Type u} [Field K] [DivisionRing D] [Algebra K D] [Algebra.IsCentral K D]
  [FiniteDimensional K D] {L : Type u} [Field L] [Algebra K L]
  (e : L ⊗[K] D ≃ₐ[L] Matrix (Fin 2) (Fin 2) L) (σ : FirstKindInvolution K D)
  {n : Type} [Fintype n] [DecidableEq n] [Nonempty n] (H : Matrix n n D)

/-- The base change of the symplectic group to `L`. -/
abbrev baseChangeSymplecticGroup : GroupScheme (Spec (CommRingCat.of L)) :=
  (GroupScheme.baseChange (scalarBaseMap K L)).obj (σ.symplecticGroup H)

/-- The unit of `Γ(T, ⊤) ⊗[K] M_n(D)` underlying a point of the base change. -/
def unitPoint (T : Over (Spec (CommRingCat.of L))) :
    (T ⟶ (σ.baseChangeSymplecticGroup H (L := L)).X) →*
      (restrictedSections K L T ⊗[K] Matrix n n D)ˣ :=
  (FiniteAlgebraUnits.pointsEquiv (Module.finBasis K (Matrix n n D))
      ((Over.map (scalarBaseMap K L)).obj T)).toMonoidHom.comp
    (((yonedaGrp.map (σ.symplecticGroupι H ≫ σ.unitaryGroupι H)).app
        (Opposite.op ((Over.map (scalarBaseMap K L)).obj T))).hom.comp
      (GroupScheme.baseChangePointsEquiv (scalarBaseMap K L) (σ.symplecticGroup H) T).toMonoidHom)

theorem unitPoint_apply (T : Over (Spec (CommRingCat.of L)))
    (x : T ⟶ (σ.baseChangeSymplecticGroup H (L := L)).X) :
    σ.unitPoint H T x = FiniteAlgebraUnits.pointsEquiv (Module.finBasis K (Matrix n n D))
      ((Over.map (scalarBaseMap K L)).obj T)
      ((GroupScheme.baseChangePointsEquiv (scalarBaseMap K L) (σ.symplecticGroup H) T x ≫
        (σ.symplecticGroupι H).hom.hom) ≫ (σ.unitaryGroupι H).hom.hom) := by
  change FiniteAlgebraUnits.pointsEquiv _ _
    (GroupScheme.baseChangePointsEquiv (scalarBaseMap K L) (σ.symplecticGroup H) T x ≫
      (σ.symplecticGroupι H ≫ σ.unitaryGroupι H).hom.hom) = _
  rw [Grp.comp_hom_hom, Category.assoc]

/-- The unit underlying a point is unitary. -/
theorem unitPoint_unitary (T : Over (Spec (CommRingCat.of L)))
    (x : T ⟶ (σ.baseChangeSymplecticGroup H (L := L)).X) :
    (σ.unitPoint H T x : restrictedSections K L T ⊗[K] Matrix n n D) * (1 ⊗ₜ[K] H) *
        (σ.matrix n).baseChange (restrictedSections K L T) (σ.unitPoint H T x) = 1 ⊗ₜ[K] H := by
  have hmem := (σ.mem_range_unitaryGroupι_iff H _).1
    (SubgroupFunctor.mem_range.2 ⟨_, rfl⟩ :
      (GroupScheme.baseChangePointsEquiv (scalarBaseMap K L) (σ.symplecticGroup H) T x ≫
        (σ.symplecticGroupι H).hom.hom) ≫ (σ.unitaryGroupι H).hom.hom ∈
        (SubgroupFunctor.range (σ.unitaryGroupι H)).carrier _)
  rw [unitPoint_apply]
  exact hmem

section Darboux

variable {k : ℕ} {P : Matrix (Fin k ⊕ Fin k) (n × Fin 2) L}
  {P' : Matrix (n × Fin 2) (Fin k ⊕ Fin k) L}

omit [Algebra.IsCentral K D] [FiniteDimensional K D] [Nonempty n] [DecidableEq n] in
theorem map_mul_map_eq_one {R : Type u} [CommRing R] [Algebra L R]
    {A : Matrix (Fin k ⊕ Fin k) (n × Fin 2) L} {B : Matrix (n × Fin 2) (Fin k ⊕ Fin k) L}
    (h : A * B = 1) : A.map (algebraMap L R) * B.map (algebraMap L R) = 1 := by
  rw [← Matrix.map_mul, h, Matrix.map_one _ (_root_.map_zero _) (_root_.map_one _)]

omit [Algebra.IsCentral K D] [FiniteDimensional K D] [Nonempty n] [Fintype n] in
theorem map_mul_map_eq_one' {R : Type u} [CommRing R] [Algebra L R]
    {A : Matrix (n × Fin 2) (Fin k ⊕ Fin k) L} {B : Matrix (Fin k ⊕ Fin k) (n × Fin 2) L}
    (h : A * B = 1) : A.map (algebraMap L R) * B.map (algebraMap L R) = 1 := by
  rw [← Matrix.map_mul, h, Matrix.map_one _ (_root_.map_zero _) (_root_.map_one _)]

omit [Algebra.IsCentral K D] [FiniteDimensional K D] [Nonempty n] [DecidableEq n] in
theorem map_darboux {R : Type u} [CommRing R] [Algebra L R] {C : Matrix (n × Fin 2) (n × Fin 2) L}
    (hPC : P * C * Pᵀ = J (Fin k) L) :
    P.map (algebraMap L R) * C.map (algebraMap L R) * (P.map (algebraMap L R))ᵀ =
      J (Fin k) R := by
  rw [← Matrix.transpose_map, ← Matrix.map_mul, ← Matrix.map_mul, hPC, Matrix.map_J]

variable (P P')

section Ring

variable (R : Type u) [CommRing R] [Algebra K R] [Algebra L R] [IsScalarTower K L R]

/-- The matrix `P Φ(u) P'` of an element `u` of `R ⊗[K] M_n(D)`. -/
def darbouxMatrix (u : R ⊗[K] Matrix n n D) : Matrix (Fin k ⊕ Fin k) (Fin k ⊕ Fin k) R :=
  P.map (algebraMap L R) * matrixChartR e R u * P'.map (algebraMap L R)

omit [Algebra.IsCentral K D] [FiniteDimensional K D] [Nonempty n] in
theorem darbouxMatrix_one (hPP' : P * P' = 1) : darbouxMatrix e P P' R 1 = 1 := by
  rw [darbouxMatrix, _root_.map_one, Matrix.mul_one]
  exact map_mul_map_eq_one hPP'

omit [Algebra.IsCentral K D] [FiniteDimensional K D] [Nonempty n] in
theorem darbouxMatrix_mul (hP'P : P' * P = 1) (u v : R ⊗[K] Matrix n n D) :
    darbouxMatrix e P P' R (u * v) = darbouxMatrix e P P' R u * darbouxMatrix e P P' R v := by
  have h := map_mul_map_eq_one' (R := R) hP'P
  simp only [darbouxMatrix, _root_.map_mul, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (P'.map _) (P.map _), h, Matrix.one_mul]

omit [Algebra.IsCentral K D] [FiniteDimensional K D] [Nonempty n] in
theorem darbouxMatrix_injective (hP'P : P' * P = 1) :
    Function.Injective (darbouxMatrix e P P' R) := by
  intro u v huv
  have h := map_mul_map_eq_one' (R := R) hP'P
  have h2 : matrixChartR e R u = matrixChartR e R v := by
    have h' := congrArg (fun M => P'.map (algebraMap L R) * M * P.map (algebraMap L R)) huv
    simp only [darbouxMatrix, Matrix.mul_assoc] at h'
    simpa only [← Matrix.mul_assoc (P'.map _) (P.map _), h, Matrix.one_mul,
      Matrix.mul_one] using h'
  exact (matrixChartR e R).injective h2

omit [Algebra.IsCentral K D] [FiniteDimensional K D] [Nonempty n] in
/-- `P Φ(u) P'` is symplectic exactly when `u` is unitary for `H`. -/
theorem darbouxMatrix_mem_iff (hP'P : P' * P = 1) (hPC : P * σ.splitGram e H * Pᵀ = J (Fin k) L)
    (u : R ⊗[K] Matrix n n D) :
    darbouxMatrix e P P' R u ∈ Matrix.symplecticGroup (Fin k) R ↔
      u * (1 ⊗ₜ[K] H) * (σ.matrix n).baseChange R u = 1 ⊗ₜ[K] H :=
  (SymplecticMatrix.mul_mul_mem_symplecticGroup_iff (map_mul_map_eq_one' hP'P)
    (map_darboux hPC) _).trans (mul_mul_baseChange_eq_iff e σ R H u).symm

omit [Algebra.IsCentral K D] [FiniteDimensional K D] [Nonempty n] in
/-- The matrix `P Φ(u) P'` commutes with coefficient changes of `L`-algebras. -/
theorem darbouxMatrix_naturality {R' : Type u} [CommRing R'] [Algebra K R'] [Algebra L R']
    [IsScalarTower K L R'] (f : R →ₐ[L] R') (u : R ⊗[K] Matrix n n D) :
    darbouxMatrix e P P' R' (Algebra.TensorProduct.map (f.restrictScalars K) (AlgHom.id K _) u) =
      (darbouxMatrix e P P' R u).map f := by
  rw [darbouxMatrix, darbouxMatrix, matrixChartR_naturality, Matrix.map_mul, Matrix.map_mul,
    Matrix.map_map, Matrix.map_map]
  congr 2 <;> ext <;> simp

/-- Every symplectic matrix is `P Φ(u) P'` for a unit `u` which is unitary for `H` and of
reduced norm one. -/
theorem exists_darbouxMatrix_eq (hPP' : P * P' = 1) (hP'P : P' * P = 1)
    (hPC : P * σ.splitGram e H * Pᵀ = J (Fin k) L)
    (g : Matrix.symplecticGroup (Fin k) R) :
    ∃ w : (R ⊗[K] Matrix n n D)ˣ,
      (w : R ⊗[K] Matrix n n D) * (1 ⊗ₜ[K] H) * (σ.matrix n).baseChange R w = 1 ⊗ₜ[K] H ∧
        CentralSimple.reducedNorm K (Matrix n n D) R w = 1 ∧
          darbouxMatrix e P P' R w = g := by
  have hPP'R := map_mul_map_eq_one (R := R) hPP'
  have hP'PR := map_mul_map_eq_one' (R := R) hP'P
  set PR := P.map (algebraMap L R)
  set P'R := P'.map (algebraMap L R)
  set gi : Matrix (Fin k ⊕ Fin k) (Fin k ⊕ Fin k) R := ((g⁻¹ : Matrix.symplecticGroup (Fin k) R) :
    Matrix (Fin k ⊕ Fin k) (Fin k ⊕ Fin k) R)
  set gm : Matrix (Fin k ⊕ Fin k) (Fin k ⊕ Fin k) R :=
    (g : Matrix (Fin k ⊕ Fin k) (Fin k ⊕ Fin k) R)
  have hggi : gm * gi = 1 := by
    rw [← Submonoid.coe_mul, mul_inv_cancel, Submonoid.coe_one]
  have hgig : gi * gm = 1 := by
    rw [← Submonoid.coe_mul, inv_mul_cancel, Submonoid.coe_one]
  let gu : (Matrix (n × Fin 2) (n × Fin 2) R)ˣ :=
    { val := P'R * gm * PR
      inv := P'R * gi * PR
      val_inv := by
        simp only [Matrix.mul_assoc]
        rw [← Matrix.mul_assoc PR P'R, hPP'R, Matrix.one_mul, ← Matrix.mul_assoc gm gi, hggi,
          Matrix.one_mul, hP'PR]
      inv_val := by
        simp only [Matrix.mul_assoc]
        rw [← Matrix.mul_assoc PR P'R, hPP'R, Matrix.one_mul, ← Matrix.mul_assoc gi, hgig,
          Matrix.one_mul, hP'PR] }
  let w : (R ⊗[K] Matrix n n D)ˣ := Units.map (matrixChartR (n := n) e R).symm.toMonoidHom gu
  have hw : matrixChartR e R (w : R ⊗[K] Matrix n n D) = P'R * gm * PR := by
    change matrixChartR e R ((matrixChartR (n := n) e R).symm (P'R * gm * PR)) = _
    rw [RingEquiv.apply_symm_apply]
  have hdw : darbouxMatrix e P P' R w = g := by
    rw [darbouxMatrix, hw]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc PR P'R, hPP'R, Matrix.one_mul, Matrix.mul_one]
  refine ⟨w, ?_, ?_, hdw⟩
  · rw [← darbouxMatrix_mem_iff e σ H P P' R hP'P hPC, hdw]
    exact g.2
  · let eqv : (n × Fin 2) ≃ (Fin k ⊕ Fin k) :=
      Fintype.equivOfCardEq (card_eq_of_mul_eq_one hPP' hP'P).symm
    rw [reducedNorm_eq_det_matrixChartR e R, hw,
      det_mul_mul_of_mul_eq_one eqv hPP'R, SymplecticGroup.det_eq_one g.2]

end Ring

/-- Restriction of points of the base change acts on the underlying units by the coefficient
change of global sections. -/
theorem unitPoint_naturality {T T' : Over (Spec (CommRingCat.of L))} (a : T' ⟶ T)
    (x : T ⟶ (σ.baseChangeSymplecticGroup H (L := L)).X) :
    σ.unitPoint H T' (a ≫ x) =
      Units.map (Algebra.TensorProduct.map
        ((algΓ (CommRingCat.of K)).map ((Over.map (scalarBaseMap K L)).map a)).unop.hom
        (AlgHom.id K (Matrix n n D))).toMonoidHom (σ.unitPoint H T x) := by
  rw [unitPoint_apply, unitPoint_apply, GroupScheme.baseChangePointsEquiv_naturality,
    Category.assoc, Category.assoc, FiniteAlgebraUnits.pointsEquiv_naturality, Category.assoc]

/-- Units of `Γ(T, ⊤) ⊗[K] M_n(D)` which are unitary of reduced norm one come from points of the
base change. -/
theorem exists_unitPoint_eq (T : Over (Spec (CommRingCat.of L)))
    (w : (restrictedSections K L T ⊗[K] Matrix n n D)ˣ)
    (hw : (w : restrictedSections K L T ⊗[K] Matrix n n D) * (1 ⊗ₜ[K] H) *
      (σ.matrix n).baseChange (restrictedSections K L T) w = 1 ⊗ₜ[K] H)
    (hn : CentralSimple.reducedNorm K (Matrix n n D) (restrictedSections K L T) w = 1) :
    ∃ x, σ.unitPoint H T x = w := by
  set T' := (Over.map (scalarBaseMap K L)).obj T
  set y := (FiniteAlgebraUnits.pointsEquiv (Module.finBasis K (Matrix n n D)) T').symm w
  have hy : y ∈ (SubgroupFunctor.range (σ.unitaryGroupι H)).carrier T' := by
    rw [mem_range_unitaryGroupι_iff, MulEquiv.apply_symm_apply]
    exact hw
  obtain ⟨z, hz⟩ := SubgroupFunctor.mem_range.1 hy
  have hzker : z ≫ (σ.unitaryGroupι H ≫
      CentralSimpleUnits.reducedNormHom K (Matrix n n D)).hom.hom = 1 := by
    apply (Gm.pointsEquiv (Spec (CommRingCat.of K)) T').injective
    rw [Grp.comp_hom_hom, ← Category.assoc, hz, CentralSimpleUnits.reducedNormHom_points,
      MulEquiv.apply_symm_apply, _root_.map_one]
    exact Units.ext hn
  let xk : T' ⟶ (σ.symplecticGroup H).X :=
    (kernelPointsEquiv (σ.unitaryGroupι H ≫ CentralSimpleUnits.reducedNormHom K (Matrix n n D))
      T').symm ⟨z, (MonoidHom.mem_ker).2 hzker⟩
  have hk : xk ≫ (σ.symplecticGroupι H).hom.hom = z :=
    congrArg Subtype.val ((kernelPointsEquiv (σ.unitaryGroupι H ≫
      CentralSimpleUnits.reducedNormHom K (Matrix n n D)) T').apply_symm_apply
        ⟨z, (MonoidHom.mem_ker).2 hzker⟩)
  refine ⟨(GroupScheme.baseChangePointsEquiv _ _ T).symm xk, ?_⟩
  rw [unitPoint_apply, MulEquiv.apply_symm_apply, hk, hz, MulEquiv.apply_symm_apply]

section Scheme

variable (hPP' : P * P' = 1) (hP'P : P' * P = 1) (hPC : P * σ.splitGram e H * Pᵀ = J (Fin k) L)
include hPP' hP'P hPC

/-- On points of the base change, `u ↦ P Φ(u) P'`. -/
def splitPointsHom (T : Over (Spec (CommRingCat.of L))) :
    (T ⟶ (σ.baseChangeSymplecticGroup H (L := L)).X) →*
      Matrix.symplecticGroup (Fin k) (restrictedSections K L T) where
  toFun x := ⟨darbouxMatrix e P P' (restrictedSections K L T) (σ.unitPoint H T x),
    (darbouxMatrix_mem_iff e σ H P P' _ hP'P hPC _).2 (σ.unitPoint_unitary H T x)⟩
  map_one' := Subtype.ext (by
    change darbouxMatrix e P P' (restrictedSections K L T)
      ((σ.unitPoint H T 1 : (restrictedSections K L T ⊗[K] Matrix n n D)ˣ) :
        restrictedSections K L T ⊗[K] Matrix n n D) = 1
    rw [_root_.map_one, Units.val_one]
    exact darbouxMatrix_one e P P' _ hPP')
  map_mul' x y := Subtype.ext (by
    change darbouxMatrix e P P' (restrictedSections K L T)
      ((σ.unitPoint H T (x * y) : (restrictedSections K L T ⊗[K] Matrix n n D)ˣ) :
        restrictedSections K L T ⊗[K] Matrix n n D) =
      darbouxMatrix e P P' (restrictedSections K L T) (σ.unitPoint H T x) *
        darbouxMatrix e P P' (restrictedSections K L T) (σ.unitPoint H T y)
    rw [_root_.map_mul, Units.val_mul]
    exact darbouxMatrix_mul e P P' _ hP'P _ _)

theorem splitPointsHom_apply (T : Over (Spec (CommRingCat.of L)))
    (x : T ⟶ (σ.baseChangeSymplecticGroup H (L := L)).X) :
    (σ.splitPointsHom e H P P' hPP' hP'P hPC T x :
        Matrix (Fin k ⊕ Fin k) (Fin k ⊕ Fin k) (restrictedSections K L T)) =
      darbouxMatrix e P P' (restrictedSections K L T) (σ.unitPoint H T x) :=
  rfl

theorem splitPointsHom_bijective (T : Over (Spec (CommRingCat.of L))) :
    Function.Bijective (σ.splitPointsHom e H P P' hPP' hP'P hPC T) := by
  constructor
  · intro x y hxy
    have h1 := congrArg Subtype.val hxy
    rw [splitPointsHom_apply, splitPointsHom_apply] at h1
    have h3 : σ.unitPoint H T x = σ.unitPoint H T y :=
      Units.ext (darbouxMatrix_injective e P P' _ hP'P h1)
    rw [unitPoint_apply, unitPoint_apply] at h3
    have h4 := (FiniteAlgebraUnits.pointsEquiv _ _).injective h3
    have := (σ.isClosedSubgroup_unitaryGroupι H).mono_overHom
    have : Mono (σ.symplecticGroupι H).hom.hom := kernelι_mono _
    exact (GroupScheme.baseChangePointsEquiv _ _ T).injective
      ((cancel_mono _).1 ((cancel_mono _).1 h4))
  · intro g
    obtain ⟨w, hw, hn, hwg⟩ := exists_darbouxMatrix_eq e σ H P P' _ hPP' hP'P hPC g
    obtain ⟨x, hx⟩ := σ.exists_unitPoint_eq H T w hw hn
    refine ⟨x, Subtype.ext ?_⟩
    rw [splitPointsHom_apply, hx, hwg]

/-- Points of the base change of the symplectic group are split symplectic matrices. -/
def splitPointsEquiv (T : Over (Spec (CommRingCat.of L))) :
    (T ⟶ (σ.baseChangeSymplecticGroup H (L := L)).X) ≃*
      Matrix.symplecticGroup (Fin k) Γ(T.left, ⊤) :=
  MulEquiv.ofBijective (σ.splitPointsHom e H P P' hPP' hP'P hPC T)
    (σ.splitPointsHom_bijective e H P P' hPP' hP'P hPC T)

theorem splitPointsEquiv_naturality {T T' : Over (Spec (CommRingCat.of L))} (a : T' ⟶ T)
    (x : T ⟶ (σ.baseChangeSymplecticGroup H (L := L)).X) :
    σ.splitPointsEquiv e H P P' hPP' hP'P hPC T' (a ≫ x) =
      SymplecticMatrix.map (Fin k) a.left.appTop.hom
        (σ.splitPointsEquiv e H P P' hPP' hP'P hPC T x) := by
  apply Subtype.ext
  change darbouxMatrix e P P' (restrictedSections K L T') (σ.unitPoint H T' (a ≫ x)) =
    (darbouxMatrix e P P' (restrictedSections K L T) (σ.unitPoint H T x)).map
      a.left.appTop.hom
  rw [unitPoint_naturality]
  let f : restrictedSections K L T →ₐ[L] restrictedSections K L T' :=
    { ((algΓ (CommRingCat.of K)).map ((Over.map (scalarBaseMap K L)).map a)).unop.hom.toRingHom
      with commutes' := fun c => ((algΓ (CommRingCat.of L)).map a).unop.hom.commutes c }
  exact darbouxMatrix_naturality e P P' (restrictedSections K L T) f (σ.unitPoint H T x)

/-- The base change of the symplectic group to `L` is the split symplectic group. -/
def splittingIso :
    σ.baseChangeSymplecticGroup H (L := L) ≅
      SymplecticMatrix.groupScheme (Fin k) (CommRingCat.of L) :=
  isoOfPointModels (fun T => Matrix.symplecticGroup (Fin k) Γ(T.left, ⊤))
    (fun a => SymplecticMatrix.map (Fin k) a.left.appTop.hom)
    (σ.splitPointsEquiv e H P P' hPP' hP'P hPC)
    (SymplecticMatrix.pointsEquiv (Fin k) (CommRingCat.of L))
    (σ.splitPointsEquiv_naturality e H P P' hPP' hP'P hPC)
    (fun a y => SymplecticMatrix.pointsEquiv_naturality a y)

end Scheme

end Darboux

section Reductive

/-- A central division algebra of dimension `4` has reduced degree `2`. -/
theorem reducedDegree_eq_two {K D : Type u} [Field K] [DivisionRing D] [Algebra K D]
    [Algebra.IsCentral K D] [FiniteDimensional K D] (hD : finrank K D = 4) :
    CentralSimple.reducedDegree K D = 2 := by
  have h := (CentralSimple.finiteGaloisSplittingChart_spec K D).2
  rw [hD] at h
  exact Nat.mul_self_inj.1 (h.symm.trans (by norm_num))

/-- **The quaternionic symplectic groups are connected reductive.** Let `D` be a central
quaternion division algebra over a field `K` with an involution of the first kind `σ` whose
symmetric elements have dimension `3` (in characteristic not two, an orthogonal involution),
and let `H` be an invertible trace-valued antihermitian Gram matrix. Then the special unitary
group `σ.symplecticGroup H` is a connected reductive group over `K`. -/
theorem isConnectedReductive_symplecticGroup {K D : Type u} [Field K] [DivisionRing D]
    [Algebra K D] [Algebra.IsCentral K D] [FiniteDimensional K D] (hD : finrank K D = 4)
    (σ : FirstKindInvolution K D) (hσ : finrank K σ.symmetricSubspace = 3) {n : Type}
    [Fintype n] [DecidableEq n] [Nonempty n] (H : Matrix n n D) (hH : σ.IsAntihermitian H)
    (hu : IsUnit H) : IsConnectedReductive (σ.symplecticGroup H) := by
  let L := CentralSimple.finiteGaloisSplittingField K D
  let e : L ⊗[K] D ≃ₐ[L] Matrix (Fin 2) (Fin 2) L :=
    (CentralSimple.finiteGaloisSplittingChart K D).trans
      (Matrix.reindexAlgEquiv L L (finCongr (reducedDegree_eq_two hD)))
  obtain ⟨k, P, P', hPP', hP'P, hPC⟩ := SymplecticMatrix.exists_mul_mul_transpose_eq_J
    (σ.splitGram e H) (σ.transpose_splitGram e hσ hH) (σ.splitGram_diag e hσ hH)
    (σ.det_splitGram_ne_zero e hu)
  apply IsConnectedReductive.of_fieldExtension (K := L)
  exact IsConnectedReductive.of_iso (σ.splittingIso e H P P' hPP' hP'P hPC)
    (SymplecticMatrix.isConnectedReductive (Fin k) L)

end Reductive

end FirstKindInvolution

end Langlands.GroupScheme.Quaternionic
