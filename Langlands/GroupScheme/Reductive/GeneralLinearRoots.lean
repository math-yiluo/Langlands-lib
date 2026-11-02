import Langlands.GroupScheme.Reductive.GeneralLinearMaximal
import Langlands.GroupScheme.Reductive.GeneralLinearNormalizer
import Langlands.GroupScheme.Lie.GeneralLinearAdjoint

/-! # The roots of the diagonal torus of `GL_n` -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj LaurentPolynomial

namespace Langlands.GroupScheme.GeneralLinear

variable {n : Type} [Fintype n] [DecidableEq n]

/-! ### Coordinates of affine points of the split torus -/

section Coords

variable {R : CommRingCat.{u}} {A : Type u} [CommRing A] [Algebra R A]

/-- The coordinates of an `A`-point of the split torus, as units of `A`, through the published
`splitTorus.affinePointsEquiv`. -/
def torusCoords (t : Lie.AffinePoints (splitTorus.commGroupScheme (Spec R) (ULift.{u} n)).toGrp A) :
    ULift.{u} n → Aˣ :=
  splitTorus.affinePointsEquiv (ULift.{u} n) (R := CommRingCat.of A)
    ((algSpec R).obj (op (CommAlgCat.of R A))).hom t

/-- The `A`-point of the split torus with prescribed coordinates. -/
def affineTorusPoint (v : ULift.{u} n → Aˣ) :
    Lie.AffinePoints (splitTorus.commGroupScheme (Spec R) (ULift.{u} n)).toGrp A :=
  (splitTorus.affinePointsEquiv (ULift.{u} n) (R := CommRingCat.of A)
    ((algSpec R).obj (op (CommAlgCat.of R A))).hom).symm v

omit [DecidableEq n] in
theorem torusCoords_affineTorusPoint (v : ULift.{u} n → Aˣ) :
    torusCoords (affineTorusPoint (R := R) v) = v :=
  MulEquiv.apply_symm_apply _ _

/-- An `A`-point of the diagonal torus maps to the diagonal matrix of its coordinates. -/
theorem affinePointsEquiv_comp_diagonalTorus
    (t : Lie.AffinePoints (splitTorus.commGroupScheme (Spec R) (ULift.{u} n)).toGrp A) :
    affinePointsEquiv n R (CommAlgCat.of R A) (t ≫ (diagonalTorus n R).hom.hom) =
      diagonalTorusUnits n A (torusCoords t) := by
  let U := (algSpec R).obj (op (CommAlgCat.of R A))
  let φ := (Corepresented.affineSectionsIso (CommAlgCat.of R A)).hom.hom
  ext a b
  have hM : φ ((pointsEquiv n R U (t ≫ (diagonalTorus n R).hom.hom) : Matrix n n Γ(U.left, ⊤)) a b) =
      (affinePointsEquiv n R (CommAlgCat.of R A) (t ≫ (diagonalTorus n R).hom.hom) :
        Matrix n n A) a b := by
    have h := congrArg (fun M : GL n A => (M : Matrix n n A) a b)
      (affinePointsEquiv_eq_map_pointsEquiv (CommAlgCat.of R A) (t ≫ (diagonalTorus n R).hom.hom))
    exact h.symm
  have hΓ : (pointsEquiv n R U (t ≫ (diagonalTorus n R).hom.hom) : Matrix n n Γ(U.left, ⊤)) a b =
      if a = b then ((splitTorus.pointsEquiv (ULift.{u} n) U t ⟨a⟩ : Γ(U.left, ⊤)ˣ) :
        Γ(U.left, ⊤)) else 0 := by
    rw [pointsEquiv_diagonalTorus, coe_diagonalTorusUnits, Matrix.diagonal_apply]
  refine hM.symm.trans ((congrArg φ hΓ).trans ?_)
  rw [coe_diagonalTorusUnits, Matrix.diagonal_apply]
  split_ifs with hab
  · subst hab
    exact DFunLike.congr_fun
      (Corepresented.affineSectionsIso_hom_ringHom (CommAlgCat.of R A)) _
  · exact map_zero φ

theorem coe_inv_diagonalTorusUnits (t : ULift.{u} n → Aˣ) :
    (((diagonalTorusUnits n A t)⁻¹ : GL n A) : Matrix n n A) =
      Matrix.diagonal fun i => (((t ⟨i⟩)⁻¹ : Aˣ) : A) :=
  rfl

end Coords

/-! ### Weight spaces of the diagonal torus -/

section Weights

variable {k : Type u} [Field k]

local notation "𝔻" => splitTorus.commGroupScheme (Spec (CommRingCat.of k)) (ULift n)

omit [DecidableEq n] in
theorem characterValue_characterLatticeEquiv_symm (m : ULift.{u} n → ℤ) {A : Type u} [CommRing A]
    [Algebra k A] (t : Lie.AffinePoints (𝔻).toGrp A) :
    Lie.characterValue ((splitTorus.characterLatticeEquiv k (ULift.{u} n)).symm m) t =
      ∏ c, torusCoords t c ^ m c := by
  have hpt : t ≫ (CommGroupScheme.groupHom
      ((splitTorus.characterLatticeEquiv k (ULift.{u} n)).symm m)).hom.hom =
      ∏ c, (t ≫ (CommGroupScheme.groupHom
        (splitTorus.proj (Spec (CommRingCat.of k)) (ULift.{u} n) c)).hom.hom) ^ m c := by
    rw [splitTorus.characterLatticeEquiv_symm_eq, comp_groupHom_sum (G := 𝔻)]
    refine Finset.prod_congr rfl fun c _ => ?_
    exact comp_groupHom_zsmul (G := 𝔻) t (m c) _
  let ψ := Gm.affinePointsEquiv (R := CommRingCat.of A)
    ((algSpec (CommRingCat.of k)).obj (op (CommAlgCat.of (CommRingCat.of k) A))).hom
  change ψ _ = _
  refine (congrArg ψ hpt).trans ((map_prod ψ _ _).trans ?_)
  exact Finset.prod_congr rfl fun c _ => map_zpow ψ _ _

/-- Membership of a matrix in a weight space of the diagonal torus, entrywise. -/
theorem mem_weightSpace_diagonalTorus_iff (Y : Matrix n n k) (χ : characterLattice 𝔻) :
    DualNumber.pointKernelLinearEquiv (R := CommRingCat.of k) Y ∈
        weightSpace (diagonalTorus n (CommRingCat.of k)) χ ↔
      ∀ (A : Type u) [CommRing A] [Algebra k A] (t : Lie.AffinePoints (𝔻).toGrp A) (a b : n),
        (torusCoords t ⟨a⟩ : A) * algebraMap k A (Y a b) * (((torusCoords t ⟨b⟩)⁻¹ : Aˣ) : A) =
          (Lie.characterValue χ t : A) * algebraMap k A (Y a b) := by
  rw [mem_weightSpace]
  refine forall_congr' fun A => ?_
  refine ⟨fun h _ _ t a b => ?_, fun h _ _ t => ?_⟩
  · have h1 := h t
    rw [DualNumber.pointKernelLinearEquiv_naturality, DualNumber.adjoint_pointKernelLinearEquiv,
      ← map_smul, EmbeddingLike.apply_eq_iff_eq, affinePointsEquiv_comp_diagonalTorus] at h1
    have h2 := congrFun (congrFun h1 a) b
    simpa only [coe_diagonalTorusUnits, coe_inv_diagonalTorusUnits, Matrix.mul_diagonal,
      Matrix.diagonal_mul, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul,
      Algebra.ofId_apply] using h2
  · rw [DualNumber.pointKernelLinearEquiv_naturality, DualNumber.adjoint_pointKernelLinearEquiv,
      ← map_smul, affinePointsEquiv_comp_diagonalTorus]
    congr 1
    ext a b
    simpa only [coe_diagonalTorusUnits, coe_inv_diagonalTorusUnits, Matrix.mul_diagonal,
      Matrix.diagonal_mul, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul,
      Algebra.ofId_apply] using h t a b

end Weights

/-! ### The roots -/

section Roots

variable {k : Type u} [Field k]

theorem prod_zpow_single_sub {A : Type*} [CommRing A] (τ : ULift.{u} n → Aˣ) (i j : ULift.{u} n) :
    ∏ c, τ c ^ ((Pi.single i 1 - Pi.single j 1 : ULift.{u} n → ℤ) c) = τ i * (τ j)⁻¹ := by
  have hs : ∀ d : ULift.{u} n, ∏ c, τ c ^ ((Pi.single d 1 : ULift.{u} n → ℤ) c) = τ d := by
    intro d
    rw [Finset.prod_eq_single d (fun c _ hc => by rw [Pi.single_eq_of_ne hc, zpow_zero])
      (by simp), Pi.single_eq_same, zpow_one]
  calc ∏ c, τ c ^ ((Pi.single i 1 - Pi.single j 1 : ULift.{u} n → ℤ) c)
      = ∏ c, τ c ^ ((Pi.single i 1 : ULift.{u} n → ℤ) c) /
          τ c ^ ((Pi.single j 1 : ULift.{u} n → ℤ) c) :=
        Finset.prod_congr rfl fun c _ => by rw [Pi.sub_apply, zpow_sub, div_eq_mul_inv]
    _ = τ i * (τ j)⁻¹ := by rw [Finset.prod_div_distrib, hs, hs, div_eq_mul_inv]

theorem prod_mulSingle_zpow {A : Type*} [CommRing A] (c : ULift.{u} n) (x : Aˣ)
    (m : ULift.{u} n → ℤ) :
    ∏ d, Pi.mulSingle c x d ^ m d = x ^ m c :=
  (Finset.prod_eq_single c (fun d _ hd => by rw [Pi.mulSingle_eq_of_ne hd, one_zpow])
    (by simp)).trans (by rw [Pi.mulSingle_eq_same])

omit [Fintype n] in
theorem val_mulSingle_coordUnit (c d : ULift.{u} n) :
    ((Pi.mulSingle (M := fun _ : ULift.{u} n => (k[T;T⁻¹])ˣ) c (Gm.relativeCoordUnit k) d :
      (k[T;T⁻¹])ˣ) : k[T;T⁻¹]) =
      LaurentPolynomial.T (if d = c then 1 else 0) := by
  by_cases h : d = c
  · subst h
    rw [Pi.mulSingle_eq_same]
    simp only [ite_true]
    rfl
  · rw [Pi.mulSingle_eq_of_ne h]
    simp only [h, ite_false, Units.val_one, LaurentPolynomial.T_zero]

omit [Fintype n] in
theorem val_inv_mulSingle_coordUnit (c d : ULift.{u} n) :
    (((Pi.mulSingle (M := fun _ : ULift.{u} n => (k[T;T⁻¹])ˣ) c (Gm.relativeCoordUnit k) d)⁻¹ :
      (k[T;T⁻¹])ˣ) : k[T;T⁻¹]) =
      LaurentPolynomial.T (-(if d = c then 1 else 0)) := by
  by_cases h : d = c
  · subst h
    rw [Pi.mulSingle_eq_same]
    simp only [ite_true]
    rfl
  · rw [Pi.mulSingle_eq_of_ne h]
    simp only [h, ite_false, inv_one, Units.val_one, neg_zero, LaurentPolynomial.T_zero]

/-- The matrix unit `E_{ij}` lies in the weight space of `eᵢ - eⱼ`. -/
theorem single_mem_weightSpace (i j : n) :
    DualNumber.pointKernelLinearEquiv (R := CommRingCat.of k) (Matrix.single i j (1 : k)) ∈
      weightSpace (diagonalTorus n (CommRingCat.of k))
        ((splitTorus.characterLatticeEquiv k (ULift.{u} n)).symm
          (Pi.single ⟨i⟩ 1 - Pi.single ⟨j⟩ 1)) := by
  rw [mem_weightSpace_diagonalTorus_iff]
  intro A _ _ t a b
  rw [characterValue_characterLatticeEquiv_symm, prod_zpow_single_sub]
  by_cases hab : i = a ∧ j = b
  · obtain ⟨rfl, rfl⟩ := hab
    have h1 : Matrix.single i j (1 : k) i j = 1 := Matrix.single_apply_same _ _ _
    rw [h1, Units.val_mul]
    ring
  · have h0 : Matrix.single i j (1 : k) a b = 0 := Matrix.single_apply_of_ne _ _ _ _ _ hab
    rw [h0, map_zero, mul_zero, zero_mul, mul_zero]

/-- The roots of the diagonal torus of `GL_n` are the characters `eᵢ - eⱼ`, `i ≠ j`
(Milne, Example 21.6). -/
theorem roots_diagonalTorus :
    roots (diagonalTorus n (CommRingCat.of k)) =
      {χ | ∃ i j : n, i ≠ j ∧ splitTorus.characterLatticeEquiv k (ULift.{u} n) χ =
        Pi.single (ULift.up i) 1 - Pi.single (ULift.up j) 1} := by
  ext χ
  constructor
  · rintro ⟨hχ, hne⟩
    obtain ⟨X, hX, hX0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
    set Y := (DualNumber.pointKernelLinearEquiv (n := n) (R := CommRingCat.of k)
      (A := k)).symm X
    have hXY : X = DualNumber.pointKernelLinearEquiv (R := CommRingCat.of k) Y :=
      (LinearEquiv.apply_symm_apply _ _).symm
    obtain ⟨a, b, hab⟩ : ∃ a b, Y a b ≠ 0 := by
      by_contra h
      push Not at h
      apply hX0
      rw [hXY]
      have hY : Y = 0 := Matrix.ext h
      rw [hY, map_zero]
    rw [hXY, mem_weightSpace_diagonalTorus_iff] at hX
    set m := splitTorus.characterLatticeEquiv k (ULift.{u} n) χ
    have hχm : χ = (splitTorus.characterLatticeEquiv k (ULift.{u} n)).symm m :=
      ((splitTorus.characterLatticeEquiv k (ULift.{u} n)).symm_apply_apply χ).symm
    have hm : ∀ c : ULift.{u} n,
        m c = (if (⟨a⟩ : ULift.{u} n) = c then 1 else 0) - (if (⟨b⟩ : ULift.{u} n) = c then 1 else 0) := by
      intro c
      have h1 := hX k[T;T⁻¹] (affineTorusPoint (R := CommRingCat.of k)
        (Pi.mulSingle c (Gm.relativeCoordUnit k))) a b
      rw [hχm, characterValue_characterLatticeEquiv_symm, torusCoords_affineTorusPoint,
        prod_mulSingle_zpow, Gm.relativeCoordUnit_zpow_val, val_mulSingle_coordUnit,
        val_inv_mulSingle_coordUnit, ← LaurentPolynomial.C_eq_algebraMap] at h1
      refine exponent_eq_of_C_mul_T hab ?_
      rw [sub_eq_add_neg, LaurentPolynomial.T_add, ← h1]
      ring
    have hm' : m = Pi.single ⟨a⟩ 1 - Pi.single ⟨b⟩ 1 := by
      funext c
      rw [hm c, Pi.sub_apply, Pi.single_apply, Pi.single_apply]
      simp only [eq_comm (a := c)]
    refine ⟨a, b, fun h => hχ ?_, hm'⟩
    rw [hχm, hm', h, sub_self, map_zero]
  · rintro ⟨i, j, hij, hχ⟩
    have hχ' : χ = (splitTorus.characterLatticeEquiv k (ULift.{u} n)).symm
        (Pi.single ⟨i⟩ 1 - Pi.single ⟨j⟩ 1) := by
      rw [← hχ, AddEquiv.symm_apply_apply]
    refine ⟨fun h0 => ?_, ?_⟩
    · have h1 := congrFun hχ ⟨i⟩
      rw [h0, map_zero, Pi.zero_apply, Pi.sub_apply, Pi.single_eq_same,
        Pi.single_eq_of_ne (fun e => hij (congrArg ULift.down e))] at h1
      norm_num at h1
    · rw [Submodule.ne_bot_iff]
      refine ⟨_, hχ' ▸ single_mem_weightSpace i j, ?_⟩
      intro h0
      have h1 := congrArg (fun x => (DualNumber.pointKernelLinearEquiv (n := n)
        (R := CommRingCat.of k) (A := k)).symm x i j) h0
      simp only [LinearEquiv.symm_apply_apply, map_zero, Matrix.zero_apply,
        Matrix.single_apply_same] at h1
      exact one_ne_zero h1

end Roots

end Langlands.GroupScheme.GeneralLinear
