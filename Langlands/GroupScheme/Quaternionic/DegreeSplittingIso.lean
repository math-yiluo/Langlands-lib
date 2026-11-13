import Langlands.GroupScheme.Quaternionic.DegreeSplittingMatrix
import Langlands.GroupScheme.Quaternionic.SymplecticReductive

/-! # The base change of `SU(D, h)` to a splitting field, in any degree

Let `D` be a central division algebra over a field `K` with an involution of the first kind `σ`,
`H ∈ M_n(D)` an invertible antihermitian Gram matrix, and `e : L ⊗[K] D ≃ₐ[L] M_κ(L)` a matrix
chart over a field extension `L`, for a finite index type `κ`. Let `C = splitGram e σ H` be the
split Gram matrix. Given rectangular matrices `P`, `P'` with `P P' = 1`, `P' P = 1` and
`P C Pᵀ = J`, this module identifies the base change of `σ.symplecticGroup H` to `L` with the
split symplectic group `SymplecticMatrix.groupScheme (Fin k)`; on points it is `u ↦ P Φ(u) P'`
for the matrix chart `Φ` (`splittingIso`, `pointsEquiv_splittingIso_hom`).

This generalises the sections `Darboux` and `Scheme` of the Library module
`Quaternionic.SymplecticReductive`, which treat `κ = Fin 2`; the proofs are the same.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Matrix Module
open scoped TensorProduct CategoryTheory.MonObj

namespace Langlands.GroupScheme.Quaternionic

namespace DegreeSplitting

attribute [local instance] restrictedSectionsAlgebra restrictedSectionsScalarTower

open FirstKindInvolution

variable {K D : Type u} [Field K] [DivisionRing D] [Algebra K D] [Algebra.IsCentral K D]
  [FiniteDimensional K D] {L : Type u} [Field L] [Algebra K L]
  {κ : Type} [Fintype κ] [DecidableEq κ]
  (e : L ⊗[K] D ≃ₐ[L] Matrix κ κ L) (σ : FirstKindInvolution K D)
  {n : Type} [Fintype n] [DecidableEq n] [Nonempty n] (H : Matrix n n D)

section Darboux

variable {k : ℕ} {P : Matrix (Fin k ⊕ Fin k) (n × κ) L}
  {P' : Matrix (n × κ) (Fin k ⊕ Fin k) L}

omit [Algebra.IsCentral K D] [FiniteDimensional K D] [Nonempty n] [DecidableEq n]
  [DecidableEq κ] in
theorem map_mul_map_eq_one {R : Type u} [CommRing R] [Algebra L R]
    {A : Matrix (Fin k ⊕ Fin k) (n × κ) L} {B : Matrix (n × κ) (Fin k ⊕ Fin k) L}
    (h : A * B = 1) : A.map (algebraMap L R) * B.map (algebraMap L R) = 1 := by
  rw [← Matrix.map_mul, h, Matrix.map_one _ (_root_.map_zero _) (_root_.map_one _)]

omit [Algebra.IsCentral K D] [FiniteDimensional K D] [Nonempty n] [Fintype n] [Fintype κ] in
theorem map_mul_map_eq_one' {R : Type u} [CommRing R] [Algebra L R]
    {A : Matrix (n × κ) (Fin k ⊕ Fin k) L} {B : Matrix (Fin k ⊕ Fin k) (n × κ) L}
    (h : A * B = 1) : A.map (algebraMap L R) * B.map (algebraMap L R) = 1 := by
  rw [← Matrix.map_mul, h, Matrix.map_one _ (_root_.map_zero _) (_root_.map_one _)]

omit [Algebra.IsCentral K D] [FiniteDimensional K D] [Nonempty n] [DecidableEq n]
  [DecidableEq κ] in
theorem map_darboux {R : Type u} [CommRing R] [Algebra L R] {C : Matrix (n × κ) (n × κ) L}
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
theorem darbouxMatrix_mem_iff (hP'P : P' * P = 1)
    (hPC : P * splitGram e σ H * Pᵀ = J (Fin k) L) (u : R ⊗[K] Matrix n n D) :
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
    (hPC : P * splitGram e σ H * Pᵀ = J (Fin k) L)
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
  let gu : (Matrix (n × κ) (n × κ) R)ˣ :=
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
  let w : (R ⊗[K] Matrix n n D)ˣ :=
    Units.map (matrixChartR (n := n) e R).symm.toMonoidHom gu
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
  · let eqv : (n × κ) ≃ (Fin k ⊕ Fin k) :=
      Fintype.equivOfCardEq (card_eq_of_mul_eq_one hPP' hP'P).symm
    rw [reducedNorm_eq_det_matrixChartR e R, hw,
      det_mul_mul_of_mul_eq_one eqv hPP'R, SymplecticGroup.det_eq_one g.2]

end Ring

section Scheme

variable (hPP' : P * P' = 1) (hP'P : P' * P = 1) (hPC : P * splitGram e σ H * Pᵀ = J (Fin k) L)
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
    (splitPointsHom e σ H P P' hPP' hP'P hPC T x :
        Matrix (Fin k ⊕ Fin k) (Fin k ⊕ Fin k) (restrictedSections K L T)) =
      darbouxMatrix e P P' (restrictedSections K L T) (σ.unitPoint H T x) :=
  rfl

theorem splitPointsHom_bijective (T : Over (Spec (CommRingCat.of L))) :
    Function.Bijective (splitPointsHom e σ H P P' hPP' hP'P hPC T) := by
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
  MulEquiv.ofBijective (splitPointsHom e σ H P P' hPP' hP'P hPC T)
    (splitPointsHom_bijective e σ H P P' hPP' hP'P hPC T)

theorem splitPointsEquiv_apply (T : Over (Spec (CommRingCat.of L)))
    (x : T ⟶ (σ.baseChangeSymplecticGroup H (L := L)).X) :
    (splitPointsEquiv e σ H P P' hPP' hP'P hPC T x).1 =
      darbouxMatrix e P P' (restrictedSections K L T) (σ.unitPoint H T x) :=
  rfl

theorem splitPointsEquiv_naturality {T T' : Over (Spec (CommRingCat.of L))} (a : T' ⟶ T)
    (x : T ⟶ (σ.baseChangeSymplecticGroup H (L := L)).X) :
    splitPointsEquiv e σ H P P' hPP' hP'P hPC T' (a ≫ x) =
      SymplecticMatrix.map (Fin k) a.left.appTop.hom
        (splitPointsEquiv e σ H P P' hPP' hP'P hPC T x) := by
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
    (splitPointsEquiv e σ H P P' hPP' hP'P hPC)
    (SymplecticMatrix.pointsEquiv (Fin k) (CommRingCat.of L))
    (splitPointsEquiv_naturality e σ H P P' hPP' hP'P hPC)
    (fun a y => SymplecticMatrix.pointsEquiv_naturality a y)

/-- On points, the splitting isomorphism is `u ↦ P Φ(u) P'`. -/
theorem pointsEquiv_splittingIso_hom (T : Over (Spec (CommRingCat.of L)))
    (x : T ⟶ (σ.baseChangeSymplecticGroup H (L := L)).X) :
    SymplecticMatrix.pointsEquiv (Fin k) (CommRingCat.of L) T
        (x ≫ (splittingIso e σ H P P' hPP' hP'P hPC).hom.hom.hom) =
      splitPointsEquiv e σ H P P' hPP' hP'P hPC T x :=
  isoOfPointModels_hom (fun T => Matrix.symplecticGroup (Fin k) Γ(T.left, ⊤))
    (fun a => SymplecticMatrix.map (Fin k) a.left.appTop.hom)
    (splitPointsEquiv e σ H P P' hPP' hP'P hPC)
    (SymplecticMatrix.pointsEquiv (Fin k) (CommRingCat.of L))
    (splitPointsEquiv_naturality e σ H P P' hPP' hP'P hPC)
    (fun a y => SymplecticMatrix.pointsEquiv_naturality a y) T x

end Scheme

end Darboux

end DegreeSplitting

end Langlands.GroupScheme.Quaternionic
