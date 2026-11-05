import Langlands.GroupScheme.Reductive.CharZeroSemisimplicityProof
import Langlands.Representation.Plancherel.RationalMatrixNormComparison
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.RepresentationTheory.Semisimple
import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-! # Semisimplicity of polynomial functions under a reductive group -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry Matrix MvPolynomial
open scoped CategoryTheory.MonObj Kronecker MonoidAlgebra

namespace Langlands.GroupScheme.PolynomialSemisimplicity

section Representations

variable {k G V : Type*} [Field k] [Group G] [AddCommGroup V] [Module k V]

/-- Semisimplicity descends along a surjective group homomorphism: both groups have the
same invariant subspaces. -/
theorem isSemisimpleRepresentation_of_comp {G' : Type*} [Group G']
    (ρ : Representation k G V) (π : G' →* G) (hπ : Function.Surjective π)
    (h : Representation.IsSemisimpleRepresentation (ρ.comp π)) : ρ.IsSemisimpleRepresentation := by
  let e : Subrepresentation ρ ≃o Subrepresentation (ρ.comp π) :=
    { toFun := fun N => ⟨N.toSubmodule, fun g _ hv => N.apply_mem_toSubmodule (π g) hv⟩
      invFun := fun N => ⟨N.toSubmodule, fun g v hv => by
        obtain ⟨g', rfl⟩ := hπ g
        exact N.apply_mem_toSubmodule g' hv⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_rel_iff' := Iff.rfl }
  exact e.complementedLattice_iff.2 h

/-- An equivariant linear map between representations is linear over the group algebra. -/
theorem map_asAlgebraHom {W : Type*} [AddCommGroup W] [Module k W]
    {τ : Representation k G W} {ρ : Representation k G V} (φ : W →ₗ[k] V)
    (hφ : ∀ g w, φ (τ g w) = ρ g (φ w)) (r : k[G]) (w : W) :
    φ (τ.asAlgebraHom r w) = ρ.asAlgebraHom r (φ w) := by
  induction r using MonoidAlgebra.induction_linear with
  | zero => simp
  | add r s hr hs => simp only [map_add, LinearMap.add_apply, hr, hs]
  | single g c =>
    simp only [Representation.asAlgebraHom_single, LinearMap.smul_apply, map_smul, hφ]

/-- A representation covered by equivariant images of semisimple representations is
semisimple. -/
theorem isSemisimpleRepresentation_of_cover (ρ : Representation k G V) {κ : Type*}
    {U : κ → Type*} [∀ i, AddCommGroup (U i)] [∀ i, Module k (U i)]
    (τ : ∀ i, Representation k G (U i)) (hτ : ∀ i, (τ i).IsSemisimpleRepresentation)
    (φ : ∀ i, U i →ₗ[k] V) (hφ : ∀ i g u, φ i (τ i g u) = ρ g (φ i u))
    (hcover : ∀ v, ∃ i u, φ i u = v) : ρ.IsSemisimpleRepresentation := by
  rw [Representation.isSemisimpleRepresentation_iff_isSemisimpleModule_asModule]
  let ψ : ∀ i, (τ i).asModule →ₗ[k[G]] ρ.asModule := fun i =>
    { toFun := fun u => ρ.asModuleEquiv.symm (φ i ((τ i).asModuleEquiv u))
      map_add' := fun u u' => by simp only [map_add]
      map_smul' := fun r u => by
        apply ρ.asModuleEquiv.injective
        rw [RingHom.id_apply, Representation.asModuleEquiv_map_smul,
          Representation.asModuleEquiv_map_smul, LinearEquiv.apply_symm_apply,
          LinearEquiv.apply_symm_apply]
        exact map_asAlgebraHom (φ i) (hφ i) r _ }
  have hss (i : κ) : IsSemisimpleModule k[G] (τ i).asModule :=
    (Representation.isSemisimpleRepresentation_iff_isSemisimpleModule_asModule (τ i)).1 (hτ i)
  refine isSemisimpleModule_of_isSemisimpleModule_submodule'
    (p := fun i => LinearMap.range (ψ i)) (fun i => IsSemisimpleModule.range _) ?_
  rw [eq_top_iff]
  rintro v -
  obtain ⟨i, u, hu⟩ := hcover (ρ.asModuleEquiv v)
  refine Submodule.mem_iSup_of_mem i ⟨(τ i).asModuleEquiv.symm u, ?_⟩
  change ρ.asModuleEquiv.symm (φ i ((τ i).asModuleEquiv ((τ i).asModuleEquiv.symm u))) = v
  rw [LinearEquiv.apply_symm_apply, hu, LinearEquiv.symm_apply_apply]

end Representations

section Matrices

variable {A B : Type*} [CommRing A] [CommRing B]

/-- The Kronecker power of a square matrix, indexed by words of length `D`. -/
def kroneckerPower {κ : Type*} (D : ℕ) (M : Matrix κ κ A) :
    Matrix (Fin D → κ) (Fin D → κ) A :=
  Matrix.of fun e e' => ∏ t, M (e t) (e' t)

theorem kroneckerPower_apply {κ : Type*} (D : ℕ) (M : Matrix κ κ A) (e e' : Fin D → κ) :
    kroneckerPower D M e e' = ∏ t, M (e t) (e' t) :=
  rfl

theorem kroneckerPower_mul {κ : Type*} [Fintype κ] (D : ℕ) (M N : Matrix κ κ A) :
    kroneckerPower D (M * N) = kroneckerPower D M * kroneckerPower D N := by
  ext e e'
  simp only [kroneckerPower, of_apply, mul_apply]
  rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
  exact Finset.sum_congr rfl fun x _ => Finset.prod_mul_distrib

theorem kroneckerPower_one {κ : Type*} [DecidableEq κ] (D : ℕ) :
    kroneckerPower D (1 : Matrix κ κ A) = 1 := by
  ext e e'
  simp only [kroneckerPower, of_apply, one_apply]
  by_cases h : e = e'
  · subst h
    simp
  · simp only [h, ↓reduceIte]
    obtain ⟨t, ht⟩ := Function.ne_iff.1 h
    exact Finset.prod_eq_zero (Finset.mem_univ t) (by simp [ht])

theorem kroneckerPower_map {κ : Type*} (D : ℕ) (M : Matrix κ κ A) (f : A →+* B) :
    kroneckerPower D (M.map f) = (kroneckerPower D M).map f := by
  ext e e'
  simp [kroneckerPower, map_prod]

/-- A square matrix extended by the identity on one padding coordinate. -/
def padded {κ : Type*} [DecidableEq κ] (M : Matrix κ κ A) : Matrix (κ ⊕ Unit) (κ ⊕ Unit) A :=
  fromBlocks M 0 0 1

theorem padded_mul {κ : Type*} [Fintype κ] [DecidableEq κ] (M N : Matrix κ κ A) :
    padded (M * N) = padded M * padded N := by
  simp [padded, fromBlocks_multiply]

theorem padded_one {κ : Type*} [DecidableEq κ] : padded (1 : Matrix κ κ A) = 1 :=
  fromBlocks_one

theorem padded_map {κ : Type*} [DecidableEq κ] (M : Matrix κ κ A) (f : A →+* B) :
    padded (M.map f) = (padded M).map f := by
  simp [padded, fromBlocks_map]

variable (A) in
/-- Kronecker powers of padded invertible matrices. -/
def wordHom (κ : Type*) [Fintype κ] [DecidableEq κ] (D : ℕ) :
    GL κ A →* GL (Fin D → κ ⊕ Unit) A :=
  MonoidHom.toHomUnits
    { toFun := fun g => kroneckerPower D (padded (g : Matrix κ κ A))
      map_one' := by rw [Units.val_one, padded_one, kroneckerPower_one]
      map_mul' := fun g g' => by rw [Units.val_mul, padded_mul, kroneckerPower_mul] }

theorem coe_wordHom {κ : Type*} [Fintype κ] [DecidableEq κ] (D : ℕ) (g : GL κ A) :
    ((wordHom A κ D g : GL (Fin D → κ ⊕ Unit) A) : Matrix (Fin D → κ ⊕ Unit) _ A) =
      kroneckerPower D (padded (g : Matrix κ κ A)) :=
  rfl

theorem wordHom_map {κ : Type*} [Fintype κ] [DecidableEq κ] (D : ℕ) (f : A →+* B)
    (g : GL κ A) :
    wordHom B κ D (Matrix.GeneralLinearGroup.map f g) =
      Matrix.GeneralLinearGroup.map f (wordHom A κ D g) := by
  apply Units.ext
  change kroneckerPower D (padded ((g : Matrix κ κ A).map f)) =
    (kroneckerPower D (padded (g : Matrix κ κ A))).map f
  rw [padded_map, kroneckerPower_map]

/-- Right translation `(X, Y) ↦ (X h, h⁻¹ Y)` of a pair of square matrices, written on the
entries of the pair. -/
def rightMatrix {n : Type*} [Fintype n] [DecidableEq n] (h : GL n A) :
    Matrix ((n × n) ⊕ (n × n)) ((n × n) ⊕ (n × n)) A :=
  fromBlocks ((1 : Matrix n n A) ⊗ₖ (h : Matrix n n A)ᵀ) 0 0
    (((h⁻¹ : GL n A) : Matrix n n A) ⊗ₖ (1 : Matrix n n A))

theorem rightMatrix_mul {n : Type*} [Fintype n] [DecidableEq n] (h h' : GL n A) :
    rightMatrix (h * h') = rightMatrix h' * rightMatrix h := by
  simp only [rightMatrix, fromBlocks_multiply, ← mul_kronecker_mul, _root_.mul_inv_rev, Units.val_mul,
    transpose_mul, Matrix.mul_one, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add]

theorem rightMatrix_one {n : Type*} [Fintype n] [DecidableEq n] :
    rightMatrix (1 : GL n A) = 1 := by
  simp [rightMatrix, fromBlocks_one]

theorem rightMatrix_map {n : Type*} [Fintype n] [DecidableEq n] (f : A →+* B) (h : GL n A) :
    rightMatrix (Matrix.GeneralLinearGroup.map f h) = (rightMatrix h).map f := by
  have hinv : (((Matrix.GeneralLinearGroup.map f h)⁻¹ : GL n B) : Matrix n n B) =
      ((h⁻¹ : GL n A) : Matrix n n A).map f := by
    rw [← map_inv]
    rfl
  rw [rightMatrix, rightMatrix, hinv, fromBlocks_map]
  congr 1
  · ext ⟨i, j⟩ ⟨i', j'⟩
    simp [one_apply, apply_ite f]
  · simp
  · simp
  · ext ⟨i, j⟩ ⟨i', j'⟩
    simp [one_apply, apply_ite f]

variable (A) in
/-- Right translation as a homomorphism of invertible matrices: the transpose of
`rightMatrix`, because `rightMatrix` reverses products. -/
def rightHom (n : Type*) [Fintype n] [DecidableEq n] :
    GL n A →* GL ((n × n) ⊕ (n × n)) A :=
  MonoidHom.toHomUnits
    { toFun := fun h => (rightMatrix h)ᵀ
      map_one' := by rw [rightMatrix_one, transpose_one]
      map_mul' := fun h h' => by rw [rightMatrix_mul, transpose_mul] }

theorem coe_rightHom {n : Type*} [Fintype n] [DecidableEq n] (h : GL n A) :
    ((rightHom A n h : GL ((n × n) ⊕ (n × n)) A) : Matrix _ _ A) = (rightMatrix h)ᵀ :=
  rfl

theorem rightHom_map {n : Type*} [Fintype n] [DecidableEq n] (f : A →+* B) (h : GL n A) :
    rightHom B n (Matrix.GeneralLinearGroup.map f h) =
      Matrix.GeneralLinearGroup.map f (rightHom A n h) := by
  apply Units.ext
  change (rightMatrix (Matrix.GeneralLinearGroup.map f h))ᵀ = ((rightMatrix h)ᵀ).map f
  rw [rightMatrix_map, transpose_map]

end Matrices

section Polynomials

variable {k : Type*} [Field k] {κ : Type*} [Fintype κ] [DecidableEq κ]

/-- The linear substitution `X i ↦ ∑ j, M j i • X j`. -/
def linearSubst (M : Matrix κ κ k) : MvPolynomial κ k →ₐ[k] MvPolynomial κ k :=
  bind₁ fun i => ∑ j, M j i • X j

omit [DecidableEq κ] in
theorem linearSubst_X (M : Matrix κ κ k) (i : κ) :
    linearSubst M (X i) = ∑ j, M j i • X j :=
  bind₁_X_right _ _

theorem linearSubst_one : linearSubst (1 : Matrix κ κ k) = AlgHom.id k _ := by
  apply MvPolynomial.algHom_ext
  intro i
  rw [linearSubst_X, AlgHom.id_apply]
  simp [one_apply]

omit [DecidableEq κ] in
theorem linearSubst_mul (M N : Matrix κ κ k) :
    linearSubst (M * N) = (linearSubst M).comp (linearSubst N) := by
  apply MvPolynomial.algHom_ext
  intro i
  rw [AlgHom.comp_apply, linearSubst_X, linearSubst_X, map_sum]
  simp only [map_smul, linearSubst_X, mul_apply, Finset.sum_smul, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => by rw [mul_comm]

variable {Γ : Type*} [Group Γ]

/-- The representation on polynomials in the coordinates `κ` attached to a matrix
homomorphism: `g` acts by the linear substitution `linearSubst (π g)`. -/
def polyRep (π : Γ →* GL κ k) : Representation k Γ (MvPolynomial κ k) where
  toFun g := (linearSubst (π g : Matrix κ κ k)).toLinearMap
  map_one' := by
    rw [map_one, Units.val_one, linearSubst_one]
    rfl
  map_mul' g g' := by
    rw [map_mul, Units.val_mul, linearSubst_mul]
    rfl

theorem polyRep_apply (π : Γ →* GL κ k) (g : Γ) (p : MvPolynomial κ k) :
    polyRep π g p = linearSubst (π g : Matrix κ κ k) p :=
  rfl

theorem polyRep_eq (π : Γ →* GL κ k) (g : Γ) :
    polyRep π g = (linearSubst (π g : Matrix κ κ k)).toLinearMap :=
  rfl

variable (k) in
/-- The variables, together with the constant `1` for the padding letter. -/
def letter : κ ⊕ Unit → MvPolynomial κ k := Sum.elim X 1

/-- The monomial spelled by a padded word. -/
def wordMonomial {D : ℕ} (e : Fin D → κ ⊕ Unit) : MvPolynomial κ k := ∏ t, letter k (e t)

theorem linearSubst_letter (M : Matrix κ κ k) (j : κ ⊕ Unit) :
    linearSubst M (letter k j) = ∑ j', padded M j' j • letter k j' := by
  rcases j with i | u
  · simp [letter, linearSubst_X, padded, Fintype.sum_sum_type]
  · simp [letter, padded, Fintype.sum_sum_type]

theorem linearSubst_wordMonomial {D : ℕ} (M : Matrix κ κ k) (e : Fin D → κ ⊕ Unit) :
    linearSubst M (wordMonomial e) =
      ∑ e', kroneckerPower D (padded M) e' e • wordMonomial (k := k) e' := by
  rw [wordMonomial, map_prod]
  simp_rw [linearSubst_letter]
  rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
  refine Finset.sum_congr rfl fun e' _ => ?_
  simp only [smul_eq_C_mul, Finset.prod_mul_distrib, ← map_prod C]
  rfl

theorem exists_wordMonomial_eq (D : ℕ) (α : κ →₀ ℕ) (hα : α.degree ≤ D) :
    ∃ e : Fin D → κ ⊕ Unit, wordMonomial (k := k) e = monomial α 1 := by
  induction D generalizing α with
  | zero =>
    have hα0 : α = 0 := (Finsupp.degree_eq_zero_iff α).1 (Nat.le_zero.1 hα)
    exact ⟨Fin.elim0, by simp [wordMonomial, hα0]⟩
  | succ D ih =>
    by_cases hα0 : α = 0
    · exact ⟨fun _ => Sum.inr (), by simp [wordMonomial, letter, hα0]⟩
    · obtain ⟨i, hi⟩ : ∃ i, α i ≠ 0 := by
        by_contra hne
        push Not at hne
        exact hα0 (Finsupp.ext hne)
      have hle : Finsupp.single i 1 ≤ α := by
        rw [Finsupp.single_le_iff]
        omega
      have hsplit : α = Finsupp.single i 1 + (α - Finsupp.single i 1) :=
        (add_tsub_cancel_of_le hle).symm
      have hdeg : (α - Finsupp.single i 1).degree ≤ D := by
        have h := congrArg Finsupp.degree hsplit
        rw [map_add, Finsupp.degree_single] at h
        omega
      obtain ⟨e, he⟩ := ih _ hdeg
      refine ⟨Fin.cons (Sum.inl i) e, ?_⟩
      rw [wordMonomial, Fin.prod_univ_succ, Fin.cons_zero]
      simp only [Fin.cons_succ]
      rw [← wordMonomial, he]
      simp only [letter, Sum.elim_inl]
      conv_rhs => rw [hsplit]
      rw [X, monomial_mul_monomial, one_mul]

variable (k κ) in
/-- Linear combinations of the padded word monomials of length `D`. -/
def wordMap (D : ℕ) : ((Fin D → κ ⊕ Unit) → k) →ₗ[k] MvPolynomial κ k :=
  Fintype.linearCombination k wordMonomial

/-- Every polynomial of total degree at most `D` is a combination of words of length `D`. -/
theorem exists_wordMap_eq {D : ℕ} {p : MvPolynomial κ k} (hp : p.totalDegree ≤ D) :
    ∃ c, wordMap k κ D c = p := by
  have hspan : p ∈ Submodule.span k (Set.range (wordMonomial (k := k) (κ := κ) (D := D))) := by
    rw [p.as_sum]
    refine Submodule.sum_mem _ fun α hα => ?_
    obtain ⟨e, he⟩ := exists_wordMonomial_eq (k := k) D α ((le_totalDegree hα).trans hp)
    have : monomial α (p.coeff α) = p.coeff α • monomial α (1 : k) := by
      rw [smul_monomial, smul_eq_mul, mul_one]
    rw [this, ← he]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨e, rfl⟩)
  rw [← Fintype.range_linearCombination] at hspan
  exact hspan

/-- The word map intertwines the Kronecker power of the padded matrix with the linear
substitution. -/
theorem wordMap_mulVec (D : ℕ) (M : Matrix κ κ k) (c : (Fin D → κ ⊕ Unit) → k) :
    wordMap k κ D (kroneckerPower D (padded M) *ᵥ c) = linearSubst M (wordMap k κ D c) := by
  simp only [wordMap, Fintype.linearCombination_apply, map_sum, map_smul,
    linearSubst_wordMonomial, Finset.smul_sum, smul_smul, mulVec, dotProduct, Finset.sum_smul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun e _ => Finset.sum_congr rfl fun e' _ => by rw [mul_comm]

end Polynomials

section Scheme

variable (R : CommRingCat.{u}) (κ : Type) [Fintype κ] [DecidableEq κ] (D : ℕ)

/-- Kronecker powers of padded matrices are natural in the coefficient algebra. -/
def wordNat : GeneralLinear.functor κ R ⟶ GeneralLinear.functor (Fin D → κ ⊕ Unit) R where
  app S := GrpCat.ofHom (wordHom S κ D)
  naturality S S' f := by
    ext g : 2
    exact wordHom_map D f.hom.toRingHom g

/-- The actual group-scheme homomorphism of Kronecker powers of padded matrices. -/
def wordGroupHom :
    GeneralLinear.groupScheme κ R ⟶ GeneralLinear.groupScheme (Fin D → κ ⊕ Unit) R :=
  Corepresented.groupSchemeMap (GeneralLinear.corepresentableBy κ R)
    (GeneralLinear.corepresentableBy (Fin D → κ ⊕ Unit) R) (wordNat R κ D)

variable {R κ}

/-- The `D`th padded Kronecker power of a matrix representation. -/
def wordRepresentation {G : GroupScheme (Spec R)} (σ : MatrixRepresentation G κ) :
    MatrixRepresentation G (Fin D → κ ⊕ Unit) :=
  σ ≫ wordGroupHom R κ D

theorem pointMatrix_wordRepresentation {G : GroupScheme (Spec R)}
    (σ : MatrixRepresentation G κ) (T : Over (Spec R)) (x : T ⟶ G.X) :
    (wordRepresentation D σ).pointMatrix T x = wordHom Γ(T.left, ⊤) κ D (σ.pointMatrix T x) :=
  Corepresented.groupSchemeMap_points (GeneralLinear.corepresentableBy κ R)
    (GeneralLinear.corepresentableBy (Fin D → κ ⊕ Unit) R) (wordNat R κ D) (x ≫ σ.hom.hom)

theorem rationalMatrix_wordRepresentation {G : GroupScheme (Spec R)}
    (σ : MatrixRepresentation G κ) (x : Over.mk (𝟙 (Spec R)) ⟶ G.X) :
    (wordRepresentation D σ).rationalMatrix x = wordHom R κ D (σ.rationalMatrix x) := by
  change Matrix.GeneralLinearGroup.map (Scheme.ΓSpecIso R).hom.hom
      ((wordRepresentation D σ).pointMatrix _ x) = _
  rw [pointMatrix_wordRepresentation]
  exact (wordHom_map D _ _).symm

variable (R) in
/-- Right translation is natural in the coefficient algebra. -/
def rightNat (n : Type) [Fintype n] [DecidableEq n] :
    GeneralLinear.functor n R ⟶ GeneralLinear.functor ((n × n) ⊕ (n × n)) R where
  app S := GrpCat.ofHom (rightHom S n)
  naturality S S' f := by
    ext g : 2
    exact rightHom_map f.hom.toRingHom g

variable (R) in
/-- The actual group-scheme homomorphism of right translation on pairs of matrices. -/
def rightGroupHom (n : Type) [Fintype n] [DecidableEq n] :
    GeneralLinear.groupScheme n R ⟶ GeneralLinear.groupScheme ((n × n) ⊕ (n × n)) R :=
  Corepresented.groupSchemeMap (GeneralLinear.corepresentableBy n R)
    (GeneralLinear.corepresentableBy ((n × n) ⊕ (n × n)) R) (rightNat R n)

/-- Right translation by the matrices of a representation. -/
def rightRepresentation {G : GroupScheme (Spec R)} {n : Type} [Fintype n] [DecidableEq n]
    (ρ : MatrixRepresentation G n) : MatrixRepresentation G ((n × n) ⊕ (n × n)) :=
  ρ ≫ rightGroupHom R n

theorem pointMatrix_rightRepresentation {G : GroupScheme (Spec R)} {n : Type} [Fintype n]
    [DecidableEq n] (ρ : MatrixRepresentation G n) (T : Over (Spec R)) (x : T ⟶ G.X) :
    (rightRepresentation ρ).pointMatrix T x = rightHom Γ(T.left, ⊤) n (ρ.pointMatrix T x) :=
  Corepresented.groupSchemeMap_points (GeneralLinear.corepresentableBy n R)
    (GeneralLinear.corepresentableBy ((n × n) ⊕ (n × n)) R) (rightNat R n) (x ≫ ρ.hom.hom)

theorem rationalMatrix_rightRepresentation {G : GroupScheme (Spec R)} {n : Type} [Fintype n]
    [DecidableEq n] (ρ : MatrixRepresentation G n) (x : Over.mk (𝟙 (Spec R)) ⟶ G.X) :
    (rightRepresentation ρ).rationalMatrix x = rightHom R n (ρ.rationalMatrix x) := by
  change Matrix.GeneralLinearGroup.map (Scheme.ΓSpecIso R).hom.hom
      ((rightRepresentation ρ).pointMatrix _ x) = _
  rw [pointMatrix_rightRepresentation]
  exact (rightHom_map _ _).symm

end Scheme

section Main

variable {k : Type u} [Field k] [IsAlgClosed k] [CharZero k]
  {G : GroupScheme (Spec (CommRingCat.of k))}

/-- For a connected reductive group over an algebraically closed field of characteristic
zero, the substitution action of its rational points on polynomials, through any matrix
representation, is semisimple. -/
theorem isSemisimpleRepresentation_polyRep (hG : IsPseudoReductive G) {κ : Type} [Fintype κ]
    [DecidableEq κ] (σ : MatrixRepresentation G κ) :
    (polyRep (k := k) σ.rationalMatrix).IsSemisimpleRepresentation := by
  refine isSemisimpleRepresentation_of_cover (polyRep (k := k) σ.rationalMatrix)
    (fun D => (wordRepresentation D σ).rationalRepresentation)
    (fun D => reductiveCharZeroSemisimplicityStatement k G hG _ _)
    (fun D => wordMap k κ D) (fun D g c => ?_)
    (fun p => ⟨p.totalDegree, exists_wordMap_eq le_rfl⟩)
  rw [MatrixRepresentation.rationalRepresentation_apply, rationalMatrix_wordRepresentation]
  exact wordMap_mulVec D _ c

/-- Right translation of polynomial functions on pairs of matrices, restricted to the actual
rational-point image of a matrix representation of a reductive group, is semisimple. -/
theorem isSemisimpleRepresentation_rightTranslation (hG : IsPseudoReductive G) {n : Type}
    [Fintype n] [DecidableEq n] (ρ : MatrixRepresentation G n) :
    Representation.IsSemisimpleRepresentation ((polyRep (rightHom k n)).comp
      (ρ.affineMatrix (CommAlgCat.of k k)).range.subtype) := by
  set H := (ρ.affineMatrix (CommAlgCat.of k k)).range
  have hmem (x : rationalPoints G) : ρ.rationalMatrix x ∈ H :=
    ⟨_, (Plancherel.rationalMatrix_eq_affineMatrix ρ x).symm⟩
  let π : rationalPoints G →* H := ρ.rationalMatrix.codRestrict H hmem
  have hπ : Function.Surjective π := by
    rintro ⟨_, y, rfl⟩
    refine ⟨(AlgebraicGeometry.PointTopology.rationalPointEquiv k G.X).symm y, Subtype.ext ?_⟩
    change ρ.rationalMatrix _ = _
    rw [Plancherel.rationalMatrix_eq_affineMatrix]
    exact congrArg (ρ.affineMatrix (CommAlgCat.of k k))
      ((AlgebraicGeometry.PointTopology.rationalPointEquiv k G.X).apply_symm_apply y)
  refine isSemisimpleRepresentation_of_comp _ π hπ ?_
  have hcomp : ((polyRep (rightHom k n)).comp H.subtype).comp π =
      polyRep (k := k) (rightRepresentation ρ).rationalMatrix := by
    ext x : 1
    change polyRep (rightHom k n) (ρ.rationalMatrix x) = _
    rw [polyRep_eq, polyRep_eq, rationalMatrix_rightRepresentation]
  rw [hcomp]
  exact isSemisimpleRepresentation_polyRep hG _

end Main

end Langlands.GroupScheme.PolynomialSemisimplicity
