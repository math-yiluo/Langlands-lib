/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Algebra.Homology.MatrixComplex
public import WeilConjectures.CategoryTheory.DerivedCategory.Perfect

/-!
# Minimal matrix complexes over a local ring

Let `S` be a commutative local ring with maximal ideal `𝔪`. A matrix complex over `S` is
*minimal* (`MatrixComplex.IsMinimal`) if all the entries of its matrices lie in `𝔪`; its
associated complex is then minimal in the sense of `CochainComplex.IsMinimal`.

## Main results

- `MatrixComplex.exists_iso_Q_obj_of_isPerfect`: every perfect object of `D(S)` is the image of
  a minimal matrix complex with bounded ranks.
- `MatrixComplex.exists_isIso_Q_map_eq`: a morphism between images of bounded minimal matrix
  complexes in `D(S)` which is an isomorphism is the image of an isomorphism of complexes.
- `MatrixComplex.exists_map_eq_isUnit_det`: invertible matrices lift along surjective morphisms
  of local rings.
- `MatrixComplex.conj`: the conjugate of a matrix complex by invertible matrices, isomorphic to
  it (`MatrixComplex.conjHom`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

section SmulTop

variable {S : Type u} [CommRing S] (I : Ideal S)

/-- A vector of `Sᵏ` lies in `I • Sᵏ` if and only if its coordinates lie in `I`. -/
lemma Ideal.mem_smul_top_pi_iff {k : Type*} [Finite k] (v : k → S) :
    v ∈ I • (⊤ : Submodule S (k → S)) ↔ ∀ j, v j ∈ I := by
  constructor
  · intro hv j
    exact Submodule.smul_le.2 (fun a ha b _ ↦ I.mul_mem_right b ha)
      ((LinearMap.proj (R := S) (φ := fun _ : k ↦ S) j).map_mem_ideal_smul_top I hv)
  · intro hv
    have := Fintype.ofFinite k
    classical
    rw [pi_eq_sum_univ v]
    exact Submodule.sum_mem _ fun j _ ↦ Submodule.smul_mem_smul (hv j) Submodule.mem_top

/-- The entries of a product `B * D * C` of matrices lie in an ideal containing the entries
of `D`. -/
lemma Matrix.mul_mul_apply_mem {l m n o : Type*} [Fintype m] [Fintype n] (B : Matrix l m S)
    {D : Matrix m n S} (C : Matrix n o S) (hD : ∀ j k, D j k ∈ I) (j : l) (k : o) :
    (B * D * C) j k ∈ I := by
  simp only [Matrix.mul_apply]
  exact Ideal.sum_mem _ fun x _ ↦ Ideal.mul_mem_right _ _
    (Ideal.sum_mem _ fun y _ ↦ Ideal.mul_mem_left _ _ (hD y x))

end SmulTop

namespace MatrixComplex

variable {r r' : ℤ → ℕ} {S : Type u} [CommRing S]

/-! ### Matrix complexes from complexes of free modules -/

section OfLinearEquiv

variable (N : CochainComplex (ModuleCat.{u} S) ℤ) (e : ∀ i, N.X i ≃ₗ[S] (Fin (r i) → S))

/-- The matrix complex obtained from a complex `N` together with identifications of its terms
with `Sʳ⁽ⁱ⁾`. -/
noncomputable def ofLinearEquiv : MatrixComplex r S where
  d i := LinearMap.toMatrix'
    ((e (i + 1)).toLinearMap ∘ₗ (N.d i (i + 1)).hom ∘ₗ (e i).symm.toLinearMap)
  d_mul_d i := by
    apply Matrix.toLin'.injective
    rw [Matrix.toLin'_mul, Matrix.toLin'_toMatrix', Matrix.toLin'_toMatrix', map_zero]
    refine LinearMap.ext fun v ↦ ?_
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply,
      LinearMap.zero_apply]
    rw [← LinearMap.comp_apply (N.d (i + 1) (i + 1 + 1)).hom, ← ModuleCat.hom_comp,
      N.d_comp_d, ModuleCat.hom_zero, LinearMap.zero_apply, map_zero]

/-- The matrices of `MatrixComplex.ofLinearEquiv` represent the differentials. -/
lemma ofLinearEquiv_d_mulVec (i : ℤ) (x : N.X i) :
    ((ofLinearEquiv N e).d i).mulVec (e i x) = e (i + 1) ((N.d i (i + 1)).hom x) := by
  rw [← Matrix.toLin'_apply, ofLinearEquiv, Matrix.toLin'_toMatrix']
  simp

/-- A complex `N` is isomorphic to the matrix complex obtained from identifications of its
terms with `Sʳ⁽ⁱ⁾`. -/
noncomputable def isoOfLinearEquiv : N ≅ (ofLinearEquiv N e).complex :=
  HomologicalComplex.Hom.isoOfComponents (fun i ↦ (e i).toModuleIso) fun i j hij ↦ by
    obtain rfl : i + 1 = j := hij
    ext x
    exact ((ofLinearEquiv N e).complex_d_apply i (e i x)).trans (ofLinearEquiv_d_mulVec N e i x)

end OfLinearEquiv

/-- The matrices of an isomorphism between matrix complexes of the same ranks are
invertible. -/
lemma isUnit_det_toMatrix {M N : MatrixComplex r S} (g : M.complex ⟶ N.complex) [IsIso g]
    (i : ℤ) : IsUnit (toMatrix g i).det :=
  Matrix.isUnit_det_of_left_inverse (B := toMatrix (inv g) i) (by
    rw [← toMatrix_comp, IsIso.hom_inv_id, toMatrix_id])

/-- The entries of the inverse of a matrix map to the entries of the inverse of its image. -/
lemma _root_.Matrix.map_nonsing_inv_of_isUnit_det {S' : Type u} [CommRing S'] (φ : S →+* S')
    {k : ℕ} {b : Matrix (Fin k) (Fin k) S} (hb : IsUnit b.det) :
    b.map φ * (b⁻¹).map φ = 1 := by
  rw [← Matrix.map_mul, Matrix.mul_nonsing_inv _ hb, Matrix.map_one _ (map_zero φ) (map_one φ)]

/-! ### Conjugation by invertible matrices -/

section Conj

variable (M : MatrixComplex r S) (b : ∀ i, Matrix (Fin (r i)) (Fin (r i)) S)
  (hb : ∀ i, IsUnit (b i).det)

include hb in
/-- The conjugated matrices form a matrix complex. -/
lemma conj_d_mul_d (i : ℤ) :
    b (i + 1 + 1) * M.d (i + 1) * (b (i + 1))⁻¹ * (b (i + 1) * M.d i * (b i)⁻¹) = 0 := by
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (b (i + 1))⁻¹, Matrix.nonsing_inv_mul _ (hb _), Matrix.one_mul,
    ← Matrix.mul_assoc (M.d (i + 1)), M.d_mul_d, Matrix.zero_mul, Matrix.mul_zero]

/-- The conjugate of a matrix complex by invertible matrices `b i`: the differentials are
`b (i + 1) * d i * (b i)⁻¹`. -/
noncomputable def conj : MatrixComplex r S where
  d i := b (i + 1) * M.d i * (b i)⁻¹
  d_mul_d := conj_d_mul_d M b hb

/-- The differentials of `MatrixComplex.conj`. -/
lemma conj_d (i : ℤ) : (M.conj b hb).d i = b (i + 1) * M.d i * (b i)⁻¹ :=
  rfl

/-- The matrices `b i` commute with the differentials of a matrix complex and of its conjugate. -/
lemma conj_d_mul (i : ℤ) : (M.conj b hb).d i * b i = b (i + 1) * M.d i := by
  rw [conj_d, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ (hb i), Matrix.mul_one]

/-- The inverses of the matrices `b i` commute with the differentials of a matrix complex and
of its conjugate. -/
lemma d_mul_inv (i : ℤ) : M.d i * (b i)⁻¹ = (b (i + 1))⁻¹ * (M.conj b hb).d i := by
  rw [conj_d, Matrix.mul_assoc, ← Matrix.mul_assoc (b (i + 1))⁻¹,
    Matrix.nonsing_inv_mul _ (hb _), Matrix.one_mul]

/-- The isomorphism from a matrix complex to its conjugate, given by the matrices `b i`. -/
noncomputable def conjHom : M.complex ⟶ (M.conj b hb).complex :=
  homMk b (conj_d_mul M b hb)

/-- The matrices of `MatrixComplex.conjHom`. -/
lemma toMatrix_conjHom (i : ℤ) : toMatrix (M.conjHom b hb) i = b i :=
  toMatrix_homMk _ _ i

/-- The chain map `MatrixComplex.conjHom` is an isomorphism. -/
instance isIso_conjHom : IsIso (M.conjHom b hb) :=
  ⟨homMk (fun i ↦ (b i)⁻¹) (fun i ↦ d_mul_inv M b hb i),
    toMatrix_injective fun i ↦ by
      rw [toMatrix_comp, toMatrix_homMk, toMatrix_conjHom, Matrix.nonsing_inv_mul _ (hb i),
        toMatrix_id],
    toMatrix_injective fun i ↦ by
      rw [toMatrix_comp, toMatrix_homMk, toMatrix_conjHom, Matrix.mul_nonsing_inv _ (hb i),
        toMatrix_id]⟩

/-- If `b` reduces along `φ` to the matrices `a` of a chain map from the reduction of `M` to
`N`, then the conjugate of `M` by `b` reduces to `N`. -/
lemma map_conj_d {S' : Type u} [CommRing S'] (φ : S →+* S') (N : MatrixComplex r S')
    (a : ∀ i, Matrix (Fin (r i)) (Fin (r i)) S') (ha : ∀ i, (b i).map φ = a i)
    (hcomm : ∀ i, N.d i * a i = a (i + 1) * (M.d i).map φ) (i : ℤ) :
    ((M.conj b hb).d i).map φ = N.d i := by
  rw [conj_d, Matrix.map_mul, Matrix.map_mul, ha (i + 1), ← hcomm, Matrix.mul_assoc, ← ha i,
    Matrix.map_nonsing_inv_of_isUnit_det φ (hb i), Matrix.mul_one]

end Conj

variable [IsLocalRing S]

/-! ### Minimal matrix complexes -/

/-- A matrix complex over a local ring is *minimal* if the entries of its matrices lie in the
maximal ideal. -/
def IsMinimal (M : MatrixComplex r S) : Prop :=
  ∀ i j k, M.d i j k ∈ IsLocalRing.maximalIdeal S

/-- The complex of a minimal matrix complex is minimal. -/
lemma IsMinimal.complex {M : MatrixComplex r S} (hM : M.IsMinimal) : M.complex.IsMinimal := by
  intro i j x
  by_cases hij : i + 1 = j
  · subst hij
    rw [complex_d_apply, Ideal.mem_smul_top_pi_iff]
    intro k
    simp only [Matrix.mulVec, dotProduct]
    exact Ideal.sum_mem _ fun l _ ↦ Ideal.mul_mem_right _ _ (hM i k l)
  · rw [M.complex.shape i j hij, ModuleCat.hom_zero, LinearMap.zero_apply]
    exact Submodule.zero_mem _

/-- The matrix complex obtained from a minimal complex is minimal. -/
lemma IsMinimal.ofLinearEquiv {N : CochainComplex (ModuleCat.{u} S) ℤ} (hN : N.IsMinimal)
    (e : ∀ i, N.X i ≃ₗ[S] (Fin (r i) → S)) : (ofLinearEquiv N e).IsMinimal := by
  intro i j k
  have h := (e (i + 1)).toLinearMap.map_mem_ideal_smul_top _ (hN i (i + 1) ((e i).symm
    (Pi.single k 1)))
  rw [Ideal.mem_smul_top_pi_iff] at h
  simpa [MatrixComplex.ofLinearEquiv, LinearMap.toMatrix'_apply] using h j

/-- The base change of a minimal matrix complex along a local morphism of local rings is
minimal. -/
lemma IsMinimal.map {S' : Type u} [CommRing S'] [IsLocalRing S'] (φ : S →+* S') [IsLocalHom φ]
    {M : MatrixComplex r S} (hM : M.IsMinimal) : (M.map φ).IsMinimal :=
  fun i j k ↦ map_nonunit φ _ (hM i j k)

/-- Invertible matrices lift along surjective morphisms of local rings. -/
lemma exists_map_eq_isUnit_det {S' : Type u} [CommRing S'] [IsLocalRing S'] (φ : S →+* S')
    (hφ : Function.Surjective φ) {k : ℕ} (a : Matrix (Fin k) (Fin k) S') (ha : IsUnit a.det) :
    ∃ b : Matrix (Fin k) (Fin k) S, b.map φ = a ∧ IsUnit b.det := by
  have := IsLocalHom.of_surjective φ hφ
  let b : Matrix (Fin k) (Fin k) S := fun j l ↦ (hφ (a j l)).choose
  have hb : b.map φ = a := Matrix.ext fun j l ↦ (hφ (a j l)).choose_spec
  refine ⟨b, hb, isUnit_of_map_unit φ _ ?_⟩
  rw [RingHom.map_det, RingHom.mapMatrix_apply, hb]
  exact ha

/-- The conjugate of a minimal matrix complex is minimal. -/
lemma IsMinimal.conj {M : MatrixComplex r S} (hM : M.IsMinimal)
    (b : ∀ i, Matrix (Fin (r i)) (Fin (r i)) S) (hb : ∀ i, IsUnit (b i).det) :
    (M.conj b hb).IsMinimal :=
  fun i ↦ Matrix.mul_mul_apply_mem _ _ _ (hM i)

variable [HasDerivedCategory.{u} (ModuleCat.{u} S)]

/-- Every perfect object of `D(S)` over a local ring `S` is the image of a minimal matrix
complex with bounded ranks. -/
theorem exists_iso_Q_obj_of_isPerfect {K : DerivedCategory (ModuleCat.{u} S)}
    (hK : K.IsPerfect) :
    ∃ (r : ℤ → ℕ) (lo hi : ℤ) (M : MatrixComplex r S), (∀ i, i < lo → r i = 0) ∧
      (∀ i, hi < i → r i = 0) ∧ M.IsMinimal ∧
        Nonempty (DerivedCategory.Q.obj M.complex ≅ K) := by
  obtain ⟨P, a, b, ha, hb, hP, ⟨e⟩⟩ := hK
  have (i : ℤ) : Module.Finite S (P.X i) := (hP i).2
  have (i : ℤ) : Module.Projective S (P.X i) := (hP i).1
  have (i : ℤ) : Module.Free S (P.X i) := Module.free_of_flat_of_isLocalRing
  obtain ⟨N, hN, hNa, hNb, hNfree, hNfin, ⟨h⟩⟩ :=
    CochainComplex.exists_homotopyEquiv_isMinimal P a b
  let eb (i : ℤ) : N.X i ≃ₗ[S] (Fin (Module.finrank S (N.X i)) → S) :=
    haveI := hNfree i
    haveI := hNfin i
    (Module.finBasis S (N.X i)).equivFun
  refine ⟨_, a, b, ofLinearEquiv N eb, fun i hi ↦ ?_, fun i hi ↦ ?_,
    IsMinimal.ofLinearEquiv hN eb, ⟨?_⟩⟩
  · have := ModuleCat.isZero_iff_subsingleton.1 (N.isZero_of_isStrictlyGE a i hi)
    exact Module.finrank_zero_of_subsingleton
  · have := ModuleCat.isZero_iff_subsingleton.1 (N.isZero_of_isStrictlyLE b i hi)
    exact Module.finrank_zero_of_subsingleton
  · have : IsIso (DerivedCategory.Q.map h.inv) :=
      (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2 inferInstance
    exact DerivedCategory.Q.mapIso (isoOfLinearEquiv N eb).symm ≪≫
      asIso (DerivedCategory.Q.map h.inv) ≪≫ e.symm

/-- An isomorphism in `D(S)` between the images of bounded above minimal matrix complexes over
a local ring is the image of an isomorphism of complexes. -/
theorem exists_isIso_Q_map_eq {M : MatrixComplex r S} {N : MatrixComplex r' S}
    (hM : M.IsMinimal) (hN : N.IsMinimal) (hi hi' : ℤ) (hMhi : ∀ i, hi < i → r i = 0)
    (hNhi : ∀ i, hi' < i → r' i = 0)
    (ψ : DerivedCategory.Q.obj M.complex ⟶ DerivedCategory.Q.obj N.complex) [IsIso ψ] :
    ∃ g : M.complex ⟶ N.complex, IsIso g ∧ DerivedCategory.Q.map g = ψ := by
  have := M.isStrictlyLE_complex hi hMhi
  have := N.isStrictlyLE_complex hi' hNhi
  obtain ⟨g, rfl⟩ := DerivedCategory.Q_map_surjective_of_projective M.complex N.complex hi ψ
  have : QuasiIso g := (DerivedCategory.isIso_Q_map_iff_quasiIso _ g).1 inferInstance
  exact ⟨g, CochainComplex.isIso_of_quasiIso_of_isMinimal g hi hi' hM.complex hN.complex, rfl⟩

omit [HasDerivedCategory.{u} (ModuleCat.{u} S)] in
/-- An isomorphism between the complexes of matrix complexes over a local ring forces their
ranks to agree. -/
lemma rank_eq_of_isIso {M : MatrixComplex r S} {N : MatrixComplex r' S}
    (g : M.complex ⟶ N.complex) [IsIso g] (i : ℤ) : r i = r' i := by
  have e : (Fin (r i) → S) ≃ₗ[S] (Fin (r' i) → S) :=
    ((HomologicalComplex.eval _ _ i).mapIso (asIso g)).toLinearEquiv
  simpa using e.finrank_eq

end MatrixComplex
