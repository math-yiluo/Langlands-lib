import Langlands.GroupScheme.Reductive.GeneralLinearWeyl

/-! # Points normalizing the diagonal torus of `GL_n` act by permutations -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj LaurentPolynomial

namespace Langlands.GroupScheme.GeneralLinear

variable {n : Type} [Fintype n] [DecidableEq n] {k : Type u} [Field k]

local notation "𝔻" => splitTorus.commGroupScheme (Spec (CommRingCat.of k)) (ULift n)

/-- The test scheme `Spec k[T, T⁻¹]` over `Spec k`. -/
local notation "𝕃" => Over.mk (Spec.map (Gm.laurentC k))

/-! ### Values on the universal unit -/

/-- The global-sections isomorphism of `Spec k[T, T⁻¹]`. -/
abbrev laurentΓ : Γ((𝕃).left, ⊤) →+* k[T;T⁻¹] :=
  (Scheme.ΓSpecIso (CommRingCat.of k[T;T⁻¹])).hom.hom

/-- The powers of the universal unit are the powers of `T`. -/
theorem laurentΓ_zpow (m : ℤ) :
    laurentΓ (((Gm.pointsEquiv _ 𝕃 (Gm.laurentPoint k)) ^ m : Γ((𝕃).left, ⊤)ˣ) :
      Γ((𝕃).left, ⊤)) = LaurentPolynomial.T m := by
  rw [← map_zpow (Gm.pointsEquiv _ 𝕃)]
  exact (Gm.affinePointsEquiv_val _ _).symm.trans (Gm.affinePointsEquiv_laurentPoint_zpow k m)

theorem laurentΓ_unit :
    laurentΓ ((Gm.pointsEquiv _ 𝕃 (Gm.laurentPoint k) : Γ((𝕃).left, ⊤)ˣ) : Γ((𝕃).left, ⊤)) =
      LaurentPolynomial.T 1 := by
  simpa using laurentΓ_zpow (k := k) 1

/-- Comparison of exponents of monomials with a nonzero coefficient. -/
theorem exponent_eq_of_C_mul_T {x : k} (hx : x ≠ 0) {p q : ℤ}
    (h : LaurentPolynomial.C x * LaurentPolynomial.T p =
      LaurentPolynomial.T q * LaurentPolynomial.C x) : q = p := by
  rw [mul_comm (LaurentPolynomial.T q), ← LaurentPolynomial.single_eq_C_mul_T,
    ← LaurentPolynomial.single_eq_C_mul_T] at h
  exact (AddMonoidAlgebra.single_left_injective hx h).symm

/-- Restriction of base constants to `Spec k[T, T⁻¹]` is the constant embedding. -/
theorem laurentΓ_appTop (z : Γ(Spec (CommRingCat.of k), ⊤)) :
    laurentΓ ((𝕃).hom.appTop z) =
      LaurentPolynomial.C ((Scheme.ΓSpecIso (CommRingCat.of k)).hom z) :=
  ConcreteCategory.congr_hom (Scheme.ΓSpecIso_naturality (Gm.laurentC k)) z

omit [DecidableEq n] in
/-- A cocharacter on the universal unit, in coordinates. -/
theorem laurentΓ_cocharacter (ν : cocharacterLattice 𝔻) (d : ULift.{u} n) :
    laurentΓ ((splitTorus.pointsEquiv (ULift.{u} n) 𝕃
        (Gm.laurentPoint k ≫ (CommGroupScheme.groupHom ν).hom.hom) d : Γ((𝕃).left, ⊤)ˣ) :
      Γ((𝕃).left, ⊤)) =
      LaurentPolynomial.T (splitTorus.cocharacterLatticeEquiv k (ULift.{u} n) ν d) := by
  conv_lhs => rw [← (splitTorus.cocharacterLatticeEquiv k (ULift.{u} n)).symm_apply_apply ν]
  rw [splitTorus.pointsEquiv_cocharacterLatticeEquiv_symm]
  exact laurentΓ_zpow _

/-! ### The normalizing equation in coordinates -/

variable {n0 : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ (groupScheme n (CommRingCat.of k)).X}
  {σ : splitTorus.commGroupScheme (Spec (CommRingCat.of k)) (ULift.{u} n) ≅
    splitTorus.commGroupScheme (Spec (CommRingCat.of k)) (ULift.{u} n)}

/-- The matrix over `k` of a base point of `GL_n`. -/
abbrev baseMatrix (n0 : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ (groupScheme n (CommRingCat.of k)).X) :
    GL n k :=
  Matrix.GeneralLinearGroup.map (Scheme.ΓSpecIso (CommRingCat.of k)).hom.hom
    (pointsEquiv n _ (Over.mk (𝟙 _)) n0)

/-- If `n0` normalizes the diagonal torus through `σ` and the `(a, b)` entry of `n0` is
nonzero, then the `a`-th coordinate of the cocharacter `single c ≫ σ` is `1` if `b = c` and `0`
otherwise. -/
theorem cocharacter_coord_of_isNormalizingPoint
    (h : IsNormalizingPoint (diagonalTorus n (CommRingCat.of k)) n0 σ) {a b : n}
    (hab : (baseMatrix n0 : Matrix n n k) a b ≠ 0) (c : ULift.{u} n) :
    splitTorus.cocharacterLatticeEquiv k (ULift.{u} n)
        (splitTorus.single _ (ULift.{u} n) c ≫ σ.hom) ⟨a⟩ = if (⟨b⟩ : ULift.{u} n) = c then 1 else 0 := by
  set t := Gm.laurentPoint k ≫
    (CommGroupScheme.groupHom (splitTorus.single _ (ULift.{u} n) c)).hom.hom
  have h1 := congrArg (fun f => t ≫ f.hom.hom) h
  simp only [Grp.comp_hom_hom] at h1
  rw [← Category.assoc, comp_innerIso_hom, ← Category.assoc] at h1
  have h2 := congrArg (pointsEquiv n _ 𝕃) h1
  rw [map_mul, map_mul, map_inv, pointsEquiv_diagonalTorus, pointsEquiv_diagonalTorus,
    mul_inv_eq_iff_eq_mul] at h2
  have hν : t ≫ (CommGroupScheme.groupHom σ.hom).hom.hom =
      Gm.laurentPoint k ≫ (CommGroupScheme.groupHom
        (splitTorus.single _ (ULift.{u} n) c ≫ σ.hom)).hom.hom := by
    rw [comp_groupHom_comp]
  rw [hν, splitTorus.pointsEquiv_comp_single] at h2
  have h3 := congrArg
    (fun M : GL n Γ((𝕃).left, ⊤) => laurentΓ ((M : Matrix n n Γ((𝕃).left, ⊤)) a b)) h2
  simp only [Units.val_mul, coe_diagonalTorusUnits, Matrix.mul_diagonal,
    Matrix.diagonal_mul, map_mul, laurentΓ_cocharacter] at h3
  rw [pointsEquiv_constantPoint, Matrix.GeneralLinearGroup.map_apply, laurentΓ_appTop] at h3
  set x := (baseMatrix n0 : Matrix n n k) a b
  simp only [Pi.mulSingle_apply] at h3
  by_cases hbc : (⟨b⟩ : ULift.{u} n) = c
  · simp only [hbc, ite_true, laurentΓ_unit] at h3 ⊢
    exact exponent_eq_of_C_mul_T hab h3
  · simp only [hbc, ite_false, Units.val_one, map_one] at h3 ⊢
    refine exponent_eq_of_C_mul_T hab ?_
    rw [LaurentPolynomial.T_zero]
    exact h3

/-! ### Normalizing points are monomial -/

theorem exists_ne_zero_row (M : GL n k) (a : n) : ∃ b, (M : Matrix n n k) a b ≠ 0 := by
  by_contra h
  push Not at h
  have h1 : ((M : Matrix n n k) * ((M⁻¹ : GL n k) : Matrix n n k)) a a = 1 := by
    rw [Units.mul_inv, Matrix.one_apply_eq]
  rw [Matrix.mul_apply] at h1
  simp [h] at h1

theorem exists_ne_zero_col (M : GL n k) (b : n) : ∃ a, (M : Matrix n n k) a b ≠ 0 := by
  by_contra h
  push Not at h
  have h1 : (((M⁻¹ : GL n k) : Matrix n n k) * (M : Matrix n n k)) b b = 1 := by
    rw [Units.inv_mul, Matrix.one_apply_eq]
  rw [Matrix.mul_apply] at h1
  simp [h] at h1

theorem cocharacterLatticeEquiv_single (d i : ULift.{u} n) :
    splitTorus.cocharacterLatticeEquiv k (ULift.{u} n)
        (splitTorus.single (Spec (CommRingCat.of k)) (ULift.{u} n) d) i =
      if d = i then 1 else 0 := by
  change gmEndEquiv k (splitTorus.single _ _ d ≫ splitTorus.proj _ _ i) = _
  rw [splitTorus.single_comp_proj]
  split_ifs
  · exact gmEndEquiv_id k
  · exact map_zero _

omit [DecidableEq n] in
/-- The automorphism of the diagonal torus is determined by its values on the coordinate
cocharacters. -/
theorem inv_eq_of_single_comp {σ' τ : splitTorus.commGroupScheme (Spec (CommRingCat.of k))
      (ULift.{u} n) ≅ splitTorus.commGroupScheme (Spec (CommRingCat.of k)) (ULift.{u} n)}
    (hst : ∀ c, splitTorus.single _ (ULift.{u} n) c ≫ σ'.inv =
      splitTorus.single _ (ULift.{u} n) c ≫ τ.inv) : σ'.inv = τ.inv := by
  calc σ'.inv = 𝟙 _ ≫ σ'.inv := (Category.id_comp _).symm
    _ = (∑ c, splitTorus.proj _ (ULift.{u} n) c ≫ splitTorus.single _ (ULift.{u} n) c) ≫
        σ'.inv := by rw [splitTorus.sum_proj_comp_single]
    _ = (∑ c, splitTorus.proj _ (ULift.{u} n) c ≫ splitTorus.single _ (ULift.{u} n) c) ≫
        τ.inv := by
      rw [Preadditive.sum_comp, Preadditive.sum_comp]
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [Category.assoc, Category.assoc, hst]
    _ = τ.inv := by rw [splitTorus.sum_proj_comp_single, Category.id_comp]

/-- A point normalizing the diagonal torus acts on it through a permutation of the
coordinates. -/
theorem exists_perm_of_isNormalizingPoint
    (h : IsNormalizingPoint (diagonalTorus n (CommRingCat.of k)) n0 σ) :
    ∃ w : Equiv.Perm n, σ.inv = (torusPerm (CommRingCat.of k) w).inv := by
  set X := baseMatrix n0
  have huniq : ∀ {a b b' : n}, (X : Matrix n n k) a b ≠ 0 → (X : Matrix n n k) a b' ≠ 0 →
      b = b' := by
    intro a b b' hb hb'
    have h1 := cocharacter_coord_of_isNormalizingPoint h hb ⟨b⟩
    have h2 := cocharacter_coord_of_isNormalizingPoint h hb' ⟨b⟩
    by_contra hne
    have h3 := h1.symm.trans h2
    have hne' : (⟨b'⟩ : ULift.{u} n) ≠ ⟨b⟩ := fun e => hne (congrArg ULift.down e).symm
    simp only [ite_true, hne', ite_false] at h3
    exact one_ne_zero h3
  choose π hπ using exists_ne_zero_row X
  have hsurj : Function.Surjective π := by
    intro b
    obtain ⟨a, ha⟩ := exists_ne_zero_col X b
    exact ⟨a, huniq (hπ a) ha⟩
  have hinj : Function.Injective π := Finite.injective_iff_surjective.2 hsurj
  let w : Equiv.Perm n := Equiv.ofBijective π ⟨hinj, hsurj⟩
  have hw : ∀ a, w a = π a := fun _ => rfl
  have hcoord : ∀ (c : ULift.{u} n) (a : n),
      splitTorus.cocharacterLatticeEquiv k (ULift.{u} n)
          (splitTorus.single _ (ULift.{u} n) c ≫ σ.hom) ⟨a⟩ =
        if (⟨π a⟩ : ULift.{u} n) = c then 1 else 0 :=
    fun c a => cocharacter_coord_of_isNormalizingPoint h (hπ a) c
  have hsingle : ∀ c : ULift.{u} n, splitTorus.single _ (ULift.{u} n) c ≫ σ.hom =
      splitTorus.single _ (ULift.{u} n) ⟨w⁻¹ c.down⟩ := by
    intro c
    apply (splitTorus.cocharacterLatticeEquiv k (ULift.{u} n)).injective
    funext i
    obtain ⟨a⟩ := i
    rw [hcoord, cocharacterLatticeEquiv_single]
    by_cases hc : π a = c.down
    · have h1 : (⟨π a⟩ : ULift.{u} n) = c := ULift.ext _ _ hc
      have h2 : (⟨w⁻¹ c.down⟩ : ULift.{u} n) = ⟨a⟩ := by
        congr 1
        rw [← hc, ← hw]
        simp
      simp only [h1, h2, ite_true]
    · have h1 : (⟨π a⟩ : ULift.{u} n) ≠ c := fun e => hc (congrArg ULift.down e)
      have h2 : (⟨w⁻¹ c.down⟩ : ULift.{u} n) ≠ ⟨a⟩ := by
        intro e
        apply hc
        have e' : w⁻¹ c.down = a := congrArg ULift.down e
        rw [← hw, ← e']
        simp
      simp only [h1, h2, ite_false]
  refine ⟨w⁻¹, inv_eq_of_single_comp fun c => ?_⟩
  rw [single_comp_torusPerm_inv, inv_inv]
  have h1 := hsingle ⟨w c.down⟩
  simp only [Equiv.Perm.coe_inv, Equiv.symm_apply_apply] at h1
  calc splitTorus.single _ (ULift.{u} n) c ≫ σ.inv
      = (splitTorus.single _ (ULift.{u} n) ⟨w c.down⟩ ≫ σ.hom) ≫ σ.inv := by rw [h1]
    _ = splitTorus.single _ (ULift.{u} n) ⟨w c.down⟩ := by
      rw [Category.assoc, Iso.hom_inv_id, Category.comp_id]

variable (n k) in
/-- The image of the Weyl action of the diagonal torus is contained in the permutation
action. -/
theorem weylImage_le_range_permutationAction :
    weylImage (diagonalTorus n (CommRingCat.of k)) ≤ (permutationAction n k).range := by
  rintro _ ⟨n1, rfl⟩
  obtain ⟨w, hw⟩ := exists_perm_of_isNormalizingPoint
    (isNormalizingPoint_normalizingAut (diagonalTorus n (CommRingCat.of k)) n1)
  refine ⟨w, ?_⟩
  apply LinearEquiv.ext
  intro χ
  rw [weylAction_apply, ← characterAut_torusPerm k w, characterAut_apply, hw]

variable (n k) in
/-- The image of the Weyl action of the diagonal torus is the permutation action. -/
theorem weylImage_diagonalTorus :
    weylImage (diagonalTorus n (CommRingCat.of k)) = (permutationAction n k).range :=
  le_antisymm (weylImage_le_range_permutationAction n k) (range_permutationAction_le_weylImage k)

end Langlands.GroupScheme.GeneralLinear
